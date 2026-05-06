"""json2lean – convert JSON proof exercises into Lean 4 files.

CLI entry-point and pipeline orchestrator.

Usage:
    python -m json2lean input.json [--output-dir lean/LeanProject] [--no-preprocess]
                                    [--no-validate] [--no-recover]
                                    [--config config.json] [--model MODEL]
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Dict, List

# Ensure local ``src/`` is importable when running ``python main.py`` directly.
_PROJECT_ROOT = Path(__file__).resolve().parent
_SRC_DIR = _PROJECT_ROOT / "src"
if str(_SRC_DIR) not in sys.path:
    sys.path.insert(0, str(_SRC_DIR))

from json2lean.block_parser import (
    generate_block_comment,
    block_id_for,
    parse_blocks,
    extract_block_by_id,
    extract_block_comment_text,
    extract_block_comment_and_code,
    replace_block_code,
    frozen_context_before,
    frozen_context_in_section,
    insert_block_comment,
    insert_code_after_comment,
    dedupe_block_code_against_frozen,
)
from json2lean.config.api_client import APIClient
from json2lean.config.codex_cli_client import CodexCLIClient
from json2lean.semantic.declaration_policy import validate_top_level_contract
from json2lean.config.lean_env import check_lean_env, lean_version
from json2lean.loader import load_config, load_settings, load_json, write_json
from json2lean.models import Exercise, ExerciseStatus
from json2lean.parser import parse_exercises
from json2lean.preprocess import preprocess_all
from json2lean.repair_history import RepairHistory
from json2lean.translater import translate_exercise
from json2lean.compile.compiling_checker import validate_exercise_with_mcp
from json2lean.compile.compiling_checker import compile_lean_file
from json2lean.compile.compiling_checker import CompileResult
from json2lean.compile.compiling_checker import print_compile_result as _print_compile_result
from json2lean.writer import write_lean_file
from json2lean.compile.compiling_fixer import recover_all
from json2lean.semantic.semantic_reviewer import review_record
from json2lean.semantic.semantic_rewriter import rewrite_from_report
from json2lean.postprocess_lean import postprocess_lean_file
from postprocess.fault_tolerance import (
    annotate_lean_failure,
    comment_out_block,
    tag_preprocess_failure,
    tag_semantic_not_usable,
    tag_translation_failure,
    tag_unrecoverable,
)
from postprocess.failure_report import (
    export_failure_reports,
    append_failure_event,
    append_realtime_event,
)
from postprocess.error_problem_sync import (
    sync_realtime_failures_to_errors,
)
from postprocess.redundancy_cleanup import cleanup_lean_file
from postprocess.math_comment_render import render_math_comments_file

# Optional: compile error logger
try:
    from utils.compile_logger import log_compile_result as _real_log_compile
except ImportError:
    _real_log_compile = None


def _log_compile(**kwargs) -> Any:
    if _real_log_compile is None:
        return None
    return _real_log_compile(**kwargs)

_DECL_START_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(def|theorem|lemma|structure|abbrev|class|inductive|instance|axiom|opaque)\b",
    re.MULTILINE,
)


def _compile_and_log(
    filepath, *, toolchain_dir, timeout, use_lake_env, auto_cache_recovery, run_label="",
):
    """Compile a Lean file and log the result to the compile error log."""
    result = compile_lean_file(
        filepath,
        toolchain_dir=toolchain_dir,
        timeout=timeout,
        use_lake_env=use_lake_env,
        auto_cache_recovery=auto_cache_recovery,
    )
    try:
        _log_compile(
            lean_file=str(filepath),
            returncode=result.returncode,
            errors=result.errors,
            warnings=result.warnings,
            run_label=run_label,
        )
    except Exception:
        pass  # logging must never break the pipeline
    return result


# ------------------------------------------------------------------
# CLI
# ------------------------------------------------------------------

def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="json2lean",
        description="Convert JSON proof exercises into Lean 4 files.",
    )
    p.add_argument("input_json", help="Path to the input JSON file.")
    p.add_argument(
        "--output-dir", "-o", default="lean/LeanProject",
        help="Directory for generated Lean files (default: lean/LeanProject/).",
    )
    p.add_argument(
        "--log-dir", default="logs",
        help="Directory for logs and token-usage records (default: logs/).",
    )
    p.add_argument("--config", default=None, help="Path to credential config.json (api_key, base_url, model).")
    p.add_argument("--settings", default=None, help="Path to runtime settings.json (non-credential pipeline settings).")
    p.add_argument("--model", default=None, help="Override model from config.")
    p.add_argument(
        "--no-preprocess", action="store_true",
        help="Skip the preprocessing step.",
    )
    p.add_argument(
        "--no-validate", action="store_true",
        help="Skip Lean compilation / validation.",
    )
    p.add_argument(
        "--no-recover", action="store_true",
        help="Skip automatic recovery on validation failure.",
    )
    p.add_argument(
        "--no-translate", action="store_true",
        help="Deprecated in single-file output mode; currently ignored (kept for compatibility).",
    )
    p.add_argument(
        "--max-recovery-retries", type=int, default=None,
        help="Override recovery retry limit from config.",
    )
    p.add_argument(
        "--resume", action="store_true",
        help="Resume from last successful item using checkpoint file.",
    )
    p.add_argument(
        "--resume-from", type=int, default=None,
        help="Resume from a specific 1-based item index.",
    )
    p.add_argument(
        "--resume-translate", action="store_true",
        help=(
            "When used with --resume-from, force block translation from that index "
            "instead of entering resume-only compile mode."
        ),
    )
    p.add_argument(
        "--semantic-only", action="store_true",
        help="Skip preprocessing/translation and run semantic loop on existing combined Lean file.",
    )
    p.add_argument(
        "--postprocess-only", action="store_true",
        help="Run only final Lean postprocess on existing combined file and exit.",
    )
    p.add_argument(
        "--no-postprocess", action="store_true",
        help="Disable Lean postprocessing (comment normalization and section directive normalization).",
    )
    p.add_argument(
        "--postprocess-llm-comments", action="store_true",
        help="Use LLM-constrained rewriting for TeX-heavy Lean comments during postprocess.",
    )
    p.add_argument(
        "--postprocess-llm-comments-force-all", action="store_true",
        help="Force LLM-constrained rewriting for all Lean block comments during postprocess.",
    )
    p.add_argument(
        "--postprocess-llm-comments-only", action="store_true",
        help="Use pure LLM comment rewriting (skip rule-based TeX normalization before LLM).",
    )
    p.add_argument(
        "--no-postprocess-llm", action="store_true",
        help="Disable default LLM-based comment rewriting in postprocess.",
    )
    return p


# _print_compile_result is now imported from compiling_checker


# ------------------------------------------------------------------
# Pipeline
# ------------------------------------------------------------------

def run_pipeline(args: argparse.Namespace) -> None:
    # ---- Config ---------------------------------------------------
    config_path = Path(args.config) if args.config else None
    cfg = load_config(config_path)
    # Layer runtime settings from settings.json on top of defaults.
    # Explicit --settings arg takes priority; otherwise auto-discover
    # settings.json in the project root (next to the config file).
    settings_path = getattr(args, "settings", None)
    if not settings_path:
        auto_settings = Path(__file__).resolve().parent / "settings.json"
        if auto_settings.exists():
            settings_path = str(auto_settings)
    settings_dict = load_settings(Path(settings_path) if settings_path else None)
    if settings_dict:
        cfg = cfg.overlay_settings(settings_dict)
    if args.model:
        cfg.model = args.model
    if args.max_recovery_retries is not None:
        cfg.recovery_max_retries = args.max_recovery_retries

    do_preprocess = cfg.preprocessing_enabled and not args.no_preprocess
    do_validate = not args.no_validate
    do_recover = not args.no_recover
    do_semantic = cfg.semantic_enabled
    do_postprocess = not args.no_postprocess
    # Default policy: enable LLM comment rewriting, but keep force-all/comments-only opt-in.
    default_postprocess_llm = not bool(args.no_postprocess_llm)
    llm_rewrite_comments = bool(args.postprocess_llm_comments) or default_postprocess_llm
    llm_rewrite_all_comments = bool(args.postprocess_llm_comments_force_all)
    llm_comments_only = bool(args.postprocess_llm_comments_only)
    semantic_only = bool(args.semantic_only)
    postprocess_only = bool(args.postprocess_only)
    if semantic_only:
        do_preprocess = False
        do_semantic = True
    if postprocess_only:
        do_preprocess = False
        do_validate = False
        do_recover = False
        do_semantic = False

    project_root = Path(__file__).resolve().parent
    toolchain_dir = Path(cfg.lean_toolchain_dir)
    if not toolchain_dir.is_absolute():
        toolchain_dir = (project_root / toolchain_dir).resolve()

    input_path = Path(args.input_json).expanduser().resolve()
    input_stem = _safe_dirname(input_path.stem)

    output_root = Path(args.output_dir)
    if not output_root.is_absolute():
        output_root = (project_root / output_root).resolve()
    output_dir = output_root  # compatibility for downstream helpers
    output_file = output_root / f"{input_stem}.lean"
    log_dir = Path(args.log_dir).resolve()
    checkpoint_path = _checkpoint_file(log_dir=log_dir, input_stem=input_stem)
    semantic_checkpoint_path = _semantic_checkpoint_file(log_dir=log_dir, input_stem=input_stem)
    output_dir.mkdir(parents=True, exist_ok=True)
    log_dir.mkdir(parents=True, exist_ok=True)
    report_dir = log_dir / "failure_reports"

    def _emit_failure_event(ex: Exercise, event: str, extra: Dict[str, Any] | None = None) -> None:
        try:
            append_failure_event(
                ex,
                report_dir,
                event=event,
                extra=extra,
                lean_file=str(output_file),
            )
        except Exception as _err:
            print(f"[pipeline] Warning: realtime failure report append failed: {_err}", file=sys.stderr)

    def _emit_realtime_event(event: str, payload: Dict[str, Any]) -> None:
        try:
            append_realtime_event(
                report_dir,
                event=event,
                payload=payload,
                lean_file=str(output_file),
            )
        except Exception as _err:
            print(f"[pipeline] Warning: realtime event append failed: {_err}", file=sys.stderr)

    if args.no_translate:
        print(
            "[pipeline] --no-translate is ignored in single-file output mode; proceeding with translation.",
            file=sys.stderr,
        )
    if semantic_only:
        print("[pipeline] --semantic-only enabled: preprocessing/translation will be skipped.", file=sys.stderr)
    if postprocess_only:
        print("[pipeline] --postprocess-only enabled: only postprocess will run.", file=sys.stderr)

    # ---- Lean environment check -----------------------------------
    if do_validate:
        check_lean_env(str(toolchain_dir))
        print(f"[pipeline] Lean version: {lean_version()}", file=sys.stderr)

    # ---- Load input -----------------------------------------------
    data = load_json(input_path)
    exercises = parse_exercises(data)
    _ensure_unique_labels(exercises)
    if not exercises:
        print("[pipeline] No exercises found in input file.", file=sys.stderr)
        sys.exit(1)
    print(f"[pipeline] Loaded {len(exercises)} exercise(s) from {input_path}",
          file=sys.stderr)

    resume_idx = 1
    semantic_resume_label = ""
    if args.resume_from is not None:
        resume_idx = max(1, int(args.resume_from))
        print(f"[pipeline] Resume requested from explicit item index: {resume_idx}", file=sys.stderr)
    elif args.resume:
        if semantic_only:
            sckpt = _load_checkpoint(semantic_checkpoint_path)
            if sckpt:
                semantic_resume_label = str(sckpt.get("next_label", "") or "").strip()
                if bool(sckpt.get("semantic_completed", False)) and not semantic_resume_label:
                    semantic_resume_label = "__SEMANTIC_COMPLETE__"
                print(
                    f"[pipeline] Semantic resume requested from checkpoint {semantic_checkpoint_path} "
                    f"(next_label={semantic_resume_label or '<end>'})",
                    file=sys.stderr,
                )
            else:
                print(
                    f"[pipeline] Semantic resume requested but checkpoint missing/unreadable: "
                    f"{semantic_checkpoint_path}; start semantic from first target.",
                    file=sys.stderr,
                )
        else:
            ckpt = _load_checkpoint(checkpoint_path)
            if ckpt:
                resume_idx = max(1, int(ckpt.get("next_item", 1)))
                print(
                    f"[pipeline] Resume requested from checkpoint {checkpoint_path} (next_item={resume_idx})",
                    file=sys.stderr,
                )
            else:
                print(
                    f"[pipeline] Resume requested but checkpoint missing/unreadable: {checkpoint_path}; start from 1.",
                    file=sys.stderr,
                )
    if resume_idx > len(exercises):
        print(
            f"[pipeline] Resume index {resume_idx} exceeds total items {len(exercises)}; nothing to do.",
            file=sys.stderr,
        )
        return

    # ---- LLM clients (lazy) ---------------------------------------
    api_client: APIClient | None = None
    codex_client: CodexCLIClient | None = None

    def _get_api_client() -> APIClient:
        nonlocal api_client
        if api_client is None:
            api_client = APIClient(
                api_key=cfg.api_key,
                base_url=cfg.base_url,
                model=cfg.model,
                timeout=cfg.timeout_seconds,
                token_log_dir=log_dir,
                realtime_token_log=True,
            )
        return api_client

    def _use_codex_for(stage: str) -> bool:
        backend = str(getattr(cfg, "llm_backend", "api") or "api").strip().lower()
        if backend != "codex_cli":
            return False
        configured = getattr(cfg, "codex_stages", None) or []
        enabled = {str(x).strip().lower() for x in configured if str(x).strip()}
        return stage.strip().lower() in enabled

    def _get_codex_client() -> CodexCLIClient:
        nonlocal codex_client
        if codex_client is None:
            codex_bin_path = Path(str(getattr(cfg, "codex_bin", "bin/codex") or "bin/codex"))
            if not codex_bin_path.is_absolute():
                codex_bin_path = _PROJECT_ROOT / codex_bin_path
            codex_workdir = Path(str(getattr(cfg, "codex_workdir", "lean") or "lean"))
            if not codex_workdir.is_absolute():
                codex_workdir = _PROJECT_ROOT / codex_workdir
            codex_client = CodexCLIClient(
                codex_bin=str(codex_bin_path),
                workdir=codex_workdir,
                model=str(getattr(cfg, "codex_model", "") or cfg.model),
                reasoning_effort=str(getattr(cfg, "codex_reasoning_effort", "") or "").strip() or None,
                disable_plugins=bool(getattr(cfg, "codex_disable_plugins", True)),
                max_retries=int(getattr(cfg, "codex_max_retries", 3) or 3),
                retry_backoff_base_seconds=float(getattr(cfg, "codex_retry_backoff_base_seconds", 1.0) or 1.0),
                retry_backoff_max_seconds=float(getattr(cfg, "codex_retry_backoff_max_seconds", 8.0) or 8.0),
                call_log_dir=getattr(cfg, "codex_call_log_dir", None),
                token_log_dir=log_dir,
                realtime_token_log=True,
                source_config_path=config_path,
                extra_args=list(getattr(cfg, "codex_extra_args", []) or []),
            )
        return codex_client

    def _get_recovery_client():
        return _get_codex_client() if _use_codex_for("recovery") else _get_api_client()

    def _get_semantic_client():
        return _get_codex_client() if _use_codex_for("semantic") else _get_api_client()

    backend_name = str(getattr(cfg, "llm_backend", "api") or "api").strip().lower()
    print(
        "[pipeline] LLM backend:"
        f" backend={backend_name},"
        f" recovery={'codex_cli' if _use_codex_for('recovery') else 'api'},"
        f" semantic={'codex_cli' if _use_codex_for('semantic') else 'api'},"
        " translation=api",
        file=sys.stderr,
    )

    total = len(exercises)
    # Per-label repair history for compile-fix loop (persisted across pipeline)
    compile_history_by_label: Dict[str, RepairHistory] = {}
    # Cache dedupe relevance decisions to avoid repeated LLM calls.
    dedupe_relevance_cache: Dict[tuple[str, str, str, str], bool] = {}

    def _dedupe_keep_if_related_by_llm(
        block_id: str,
        block_comment: str,
        removed_kind: str,
        removed_text: str,
    ) -> bool:
        """Return True when removed_text is semantically related to block comment."""
        comment = str(block_comment or "").strip()
        candidate = str(removed_text or "").strip()
        if not comment or not candidate:
            return False
        key = (str(block_id), comment, str(removed_kind), candidate)
        cached = dedupe_relevance_cache.get(key)
        if cached is not None:
            return cached

        prompt = (
            "You are checking whether deduplication would delete content that is still "
            "semantically relevant to this block comment.\\n"
            "Return STRICT JSON only: {\"related\": true|false, \"reason\": \"...\"}.\\n"
            "Interpretation:\\n"
            "- related=true  => this removed code helps realize/comment on the block's source text, so KEEP it.\\n"
            "- related=false => this removed code is duplicate boilerplate or unrelated to the block comment, so deletion is safe.\\n\\n"
            f"[block_id]\\n{block_id}\\n\\n"
            f"[block_comment]\\n{comment}\\n\\n"
            f"[removed_kind]\\n{removed_kind}\\n\\n"
            f"[removed_candidate]\\n```lean\\n{candidate}\\n```\\n"
        )
        keep = True
        try:
            raw = _get_api_client().chat(
                prompt=prompt,
                max_tokens=256,
                call_type="dedupe_relevance_check",
                exercise_label=str(block_id),
                json_mode=True,
            )
            obj = json.loads(raw)
            keep = bool(obj.get("related", True))
        except Exception as err:
            # Fail-safe: keep candidate when relevance check is unavailable.
            print(
                f"[dedupe] {block_id}: relevance check failed, keep candidate ({err})",
                file=sys.stderr,
            )
            keep = True

        dedupe_relevance_cache[key] = keep
        if keep:
            print(
                f"[dedupe] {block_id}: kept {removed_kind} candidate due to comment relevance",
                file=sys.stderr,
            )
        return keep

    if postprocess_only:
        if not output_file.exists():
            print(
                f"[pipeline] --postprocess-only requires existing combined file: {output_file}",
                file=sys.stderr,
            )
            sys.exit(1)
        changed = False
        if do_postprocess:
            changed = postprocess_lean_file(
                output_file,
                llm_rewrite_comments=llm_rewrite_comments,
                llm_rewrite_all_comments=llm_rewrite_all_comments,
                llm_comments_only=llm_comments_only,
                get_client=_get_api_client
                if llm_rewrite_comments
                else None,
            )
        print(
            f"[pipeline] Postprocess {'applied' if changed else 'no-op'}: {output_file}",
            file=sys.stderr,
        )
        print("[pipeline] Done (postprocess-only).", file=sys.stderr)
        return

    if semantic_only:
        if not output_file.exists():
            print(
                f"[pipeline] --semantic-only requires existing combined file: {output_file}",
                file=sys.stderr,
            )
            sys.exit(1)
        print(f"[pipeline] Reusing existing combined file: {output_file}", file=sys.stderr)
        # When running --semantic-only, normalize any non-BLOCK-style comments
        # in-place so parse_blocks() will detect all blocks consistently.
        try:
            _text = output_file.read_text(encoding="utf-8")
            import re as _re

            def _fix_match(m: _re.Match) -> str:
                first = m.group(1).strip()
                return f"/- [BLOCK {first}]\n"

            _new = _re.sub(r"/\-[ \t]*\n(Exercise[^\n\r]+)\n", _fix_match, _text)
            if _new != _text:
                output_file.write_text(_new, encoding="utf-8")
                print(f"[pipeline] semantic-only: normalized non-BLOCK comments in {output_file}", file=sys.stderr)
        except Exception as _err:
            print(f"[pipeline] Warning: semantic-only normalization failed: {_err}", file=sys.stderr)
        # Derive exercises_to_translate from blocks parsed out of the existing
        # combined file so that each exercise carries the correct `kind` (defn,
        # thm, algo, …) and a raw dict whose block_id_for() result matches the
        # IDs already embedded in the file.  Without this the semantic loop's
        # kind-filter would reject all items from raw JSON files that lack a
        # `kind` field (e.g. ch5.json).
        _lean_full = output_file.read_text(encoding="utf-8")
        _file_blocks = parse_blocks(_lean_full)
        if _file_blocks:
            _block_exercises: List[Exercise] = []
            _seen_labels: set[str] = set()
            for _b in _file_blocks:
                _parts = _b.block_id.split("|", 2)
                _src_idx = _parts[0].strip() if len(_parts) > 0 else "UNSPECIFIED"
                _idx_str = _parts[1].strip() if len(_parts) > 1 else "0"
                _kind_str = _parts[2].strip().lower() if len(_parts) > 2 else "unknown"
                try:
                    _idx_int = int(_idx_str)
                except ValueError:
                    _idx_int = 0
                _raw = {"source_idx": _src_idx, "index": _idx_int, "kind": _kind_str}
                _base_label = f"{_safe_section_name(_src_idx)}_{_idx_int}_{_kind_str}"
                _lbl = _base_label
                _lk = 2
                while _lbl in _seen_labels:
                    _lbl = f"{_base_label}_{_lk}"
                    _lk += 1
                _seen_labels.add(_lbl)
                _bex = Exercise(raw=_raw, index=_idx_int, label=_lbl, problem="")
                _bex.lean_code = _lean_full[_b.code_start:_b.code_end].strip()
                _block_exercises.append(_bex)
            exercises_to_translate = _block_exercises
            print(
                f"[pipeline] semantic-only: derived {len(exercises_to_translate)} block(s) from existing file",
                file=sys.stderr,
            )
    else:
        # ---- Step 1: Preprocess ---------------------------------------
        if do_preprocess:
            print("[pipeline] === Preprocessing ===", file=sys.stderr)
            preprocess_failed = preprocess_all(
                _get_api_client(), exercises,
                max_tokens=cfg.preprocessing_max_tokens,
                max_attempts=cfg.preprocessing_max_attempts,
                normalize_skip_thm=cfg.preprocessing_normalize_skip_thm,
                exclude_hints=cfg.preprocessing_exclude_hints,
                input_stem=input_stem,
            )
            if preprocess_failed:
                print(
                    f"[pipeline] {len(preprocess_failed)} exercise(s) kept original problem.",
                    file=sys.stderr,
                )
                # Tag exercises whose preprocessing failed
                failed_labels = set(preprocess_failed)
                for ex in exercises:
                    if ex.label in failed_labels:
                        tag_preprocess_failure(
                            ex,
                            RuntimeError(f"preprocess_all failed for {ex.label}"),
                            phase="preprocess",
                        )
                        _emit_failure_event(ex, "preprocess_failed")
        else:
            print("[pipeline] Preprocessing skipped.", file=sys.stderr)

        # ---- Step 2: Block-by-block incremental translation --------
        print("[pipeline] === Translation (block-by-block incremental) ===", file=sys.stderr)

        # Load preprocessed records if available (for per-record translation)
        exercises_to_translate = exercises
        preprocessed_path: Path | None = None
        if do_preprocess:
            preprocessed_path = log_dir / f"{input_stem}.json"
            if not preprocessed_path.exists():
                preprocessed_path = Path(__file__).resolve().parent / "preprocessed_data" / f"{input_stem}.json"
        elif bool(args.no_preprocess):
            candidate = Path(__file__).resolve().parent / "preprocessed_data" / f"{input_stem}.json"
            if candidate.exists():
                preprocessed_path = candidate
                print(
                    f"[pipeline] --no-preprocess: reusing preprocessed records from {preprocessed_path}",
                    file=sys.stderr,
                )
        if preprocessed_path is not None and preprocessed_path.exists():
            try:
                preprocessed_data = load_json(preprocessed_path)
                if isinstance(preprocessed_data, list) and preprocessed_data:
                    temp_exercises = []
                    for rec_idx, record in enumerate(preprocessed_data, 1):
                        if record.get("kind") == "hints":
                            continue
                        rec_kind = record.get("kind", "unknown")
                        rec_content = record.get("content", "")
                        rec_term = record.get("term", "")
                        rec_source_idx = record.get("source_idx", "")
                        label = f"{rec_source_idx}_{rec_kind}_{rec_idx}"
                        temp_ex = Exercise(
                            raw={
                                "kind": rec_kind,
                                "content": rec_content,
                                "term": rec_term,
                                "source_idx": rec_source_idx,
                                "index": rec_idx,
                            },
                            index=rec_idx,
                            label=label,
                            problem=rec_content,
                        )
                        temp_exercises.append(temp_ex)
                    if temp_exercises:
                        exercises_to_translate = temp_exercises
                        print(
                            f"[pipeline] Using {len(exercises_to_translate)} preprocessed records for translation",
                            file=sys.stderr,
                        )
            except Exception as err:
                print(f"[pipeline] Warning: Failed to load preprocessed records: {err}", file=sys.stderr)

        # Initialize combined file scaffold with section wrappers
        if resume_idx > 1 and output_file.exists():
            print(
                f"[pipeline] Reusing existing combined file for resume: {output_file}",
                file=sys.stderr,
            )
        else:
            scaffold = _build_scaffold(exercises_to_translate)
            output_file.write_text(scaffold + "\n", encoding="utf-8")
            print(f"[pipeline] Combined Lean file scaffold created: {output_file}", file=sys.stderr)

        # Resume-only compile mode: when preprocessing is disabled and an
        # existing combined file is present, and a resume index is given,
        # skip translation and run compile/recover per-block starting at
        # `resume_idx`.
        resume_compile_only_mode = (
            bool(args.no_preprocess)
            and output_file.exists()
            and (args.resume_from is not None)
            and (not bool(args.resume_translate))
        )
        if resume_compile_only_mode:
            print(f"[pipeline] Resume-only compile mode enabled from item {resume_idx}", file=sys.stderr)
            print(
                "[pipeline] Tip: pass --resume-translate to force translation instead of compile-only resume.",
                file=sys.stderr,
            )
            for i, ex in enumerate(exercises_to_translate, 1):
                if i < resume_idx:
                    continue
                label = ex.label
                if _exercise_kind(ex) == "hints":
                    print(f"[pipeline][item] [{i}/{len(exercises_to_translate)}] {label} (hints, skipped)", file=sys.stderr)
                    continue
                print(f"[pipeline][item] [{i}/{len(exercises_to_translate)}] {label}", file=sys.stderr)

                # Ensure raw has 'index' for block_id generation
                if isinstance(ex.raw, dict) and "index" not in ex.raw:
                    ex.raw["index"] = ex.index

                bid = block_id_for(ex.raw)
                section_name = _safe_section_name(str((ex.raw or {}).get("source_idx") or "UNSPECIFIED"))

                # Attempt to extract existing translated code for this block
                full_text = output_file.read_text(encoding="utf-8")
                code_data = extract_block_by_id(full_text, bid)
                if not code_data or not code_data[0].strip():
                    print(f"[pipeline][item] [{i}/{len(exercises_to_translate)}] block {bid} missing or empty; skipping", file=sys.stderr)
                    # Still save checkpoint so resume can continue later
                    _save_checkpoint(
                        checkpoint_path,
                        input_path=input_path,
                        output_file=output_file,
                        total=total,
                        next_item=i + 1,
                    )
                    continue
                ex.lean_code = code_data[0]

                # Compile and attempt recovery as-needed for the existing block
                if do_validate:
                    step_result = _compile_and_log(
                        output_file,
                        toolchain_dir=str(toolchain_dir),
                        timeout=cfg.lean_timeout_seconds,
                        use_lake_env=cfg.compile_use_lake_env,
                        auto_cache_recovery=cfg.compile_auto_cache_recovery,
                        run_label=f"resume_only_item_{i}_of_{len(exercises_to_translate)}",
                    )
                    _print_compile_result(step_result, context=f"[item {i}/{len(exercises_to_translate)}] combined file (resume-only)")
                    if step_result.returncode == 0 and not step_result.errors:
                        ex.status = ExerciseStatus.VALID
                        ex.compile_returncode = 0
                        ex.errors = []
                        ex.warnings = step_result.warnings
                        print(f"[pipeline][item] [{i}/{len(exercises_to_translate)}] combined validation OK", file=sys.stderr)
                        _save_checkpoint(
                            checkpoint_path,
                            input_path=input_path,
                            output_file=output_file,
                            total=total,
                            next_item=i + 1,
                        )
                    else:
                        ex.status = ExerciseStatus.REPAIR_FAILED
                        ex.compile_returncode = step_result.returncode
                        ex.errors = step_result.errors
                        ex.warnings = step_result.warnings
                        print(
                            f"[pipeline][item] [{i}/{len(exercises_to_translate)}] combined validation FAIL "
                            f"(errors={len(step_result.errors)})",
                            file=sys.stderr,
                        )
                        if do_recover:
                            entry_hist = compile_history_by_label.setdefault(
                                str(ex.label), RepairHistory(keep_recent=5)
                            )
                            ok = _recover_combined_file_for_item(
                                get_client=_get_recovery_client,
                                get_api_client=_get_api_client,
                                get_cli_client=_get_codex_client,
                                ex=ex,
                                output_file=output_file,
                                input_stem=input_stem,
                                toolchain_dir=str(toolchain_dir),
                                cfg=cfg,
                                base_report_hint=None,
                                history=entry_hist,
                                current_block_id=bid,
                                dedupe_relevance_checker=_dedupe_keep_if_related_by_llm,
                            )
                            if ok:
                                print(f"[pipeline][item] [{i}/{len(exercises_to_translate)}] recovered; continue", file=sys.stderr)
                                _save_checkpoint(
                                    checkpoint_path,
                                    input_path=input_path,
                                    output_file=output_file,
                                    total=total,
                                    next_item=i + 1,
                                )
                            else:
                                _print_compile_result(step_result, context=f"[item {i}/{len(exercises_to_translate)}] combined file (failed, recovery attempted)")
                                tag_unrecoverable(
                                    ex, phase="compile",
                                    message=f"item {label} failed recovery during resume-only validation",
                                    errors=step_result.errors,
                                )
                                _emit_failure_event(ex, "unrecoverable_commented_out", {"block_id": bid})
                                full_text = output_file.read_text(encoding="utf-8")
                                full_text = comment_out_block(full_text, bid)
                                output_file.write_text(full_text, encoding="utf-8")
                                print(f"[pipeline][item] [{i}/{len(exercises_to_translate)}] UNRECOVERABLE: block commented out, continuing", file=sys.stderr)
                                _save_checkpoint(
                                    checkpoint_path,
                                    input_path=input_path,
                                    output_file=output_file,
                                    total=total,
                                    next_item=i + 1,
                                )
                        else:
                            tag_unrecoverable(
                                ex, phase="compile",
                                message=f"item {label} failed validation and recovery is disabled",
                                errors=step_result.errors,
                            )
                            _emit_failure_event(ex, "unrecoverable_commented_out", {"block_id": bid})
                            full_text = output_file.read_text(encoding="utf-8")
                            full_text = comment_out_block(full_text, bid)
                            output_file.write_text(full_text, encoding="utf-8")
                            print(f"[pipeline][item] [{i}/{len(exercises_to_translate)}] UNRECOVERABLE: block commented out, continuing", file=sys.stderr)
                            _save_checkpoint(
                                checkpoint_path,
                                input_path=input_path,
                                output_file=output_file,
                                total=total,
                                next_item=i + 1,
                            )
                else:
                    _save_checkpoint(
                        checkpoint_path,
                        input_path=input_path,
                        output_file=output_file,
                        total=total,
                        next_item=i + 1,
                    )
            print(f"[pipeline] Resume-only compile loop complete (post-translate): {output_file}", file=sys.stderr)
        else:
            for i, ex in enumerate(exercises_to_translate, 1):
                if i < resume_idx:
                    continue

                label = ex.label
                if _exercise_kind(ex) == "hints":
                    print(f"[pipeline][item] [{i}/{len(exercises_to_translate)}] {label} (hints, skipped)", file=sys.stderr)
                    continue
                print(f"[pipeline][item] [{i}/{len(exercises_to_translate)}] {label}", file=sys.stderr)

                # Ensure raw has 'index' for block_id generation
                if isinstance(ex.raw, dict) and "index" not in ex.raw:
                    ex.raw["index"] = ex.index

                bid = block_id_for(ex.raw)
                section_name = _safe_section_name(str((ex.raw or {}).get("source_idx") or "UNSPECIFIED"))

                # --- Step 2a: Insert block comment into combined file ---
                block_comment = generate_block_comment(ex.raw)
                full_text = output_file.read_text(encoding="utf-8")

                # Only insert if not already present (resume case)
                if f"/- [BLOCK {str(ex.raw.get('source_idx', 'UNSPECIFIED')).strip()} | {str(ex.raw.get('index', ex.index)).strip()} | " not in full_text:
                    full_text = insert_block_comment(full_text, section_name, block_comment)
                    output_file.write_text(full_text, encoding="utf-8")
                    print(f"[pipeline][item] [{i}/{len(exercises_to_translate)}] block comment inserted", file=sys.stderr)

                # --- Step 2b: Translate only the current block ---
                try:
                    # Provide frozen earlier code as read-only context
                    current_text = output_file.read_text(encoding="utf-8")
                    section_ctx = frozen_context_before(current_text, bid)
                    mcp_ctx = _gather_translation_mcp_context(
                        output_file=output_file,
                        ex=ex,
                        toolchain_dir=str(toolchain_dir),
                        cfg=cfg,
                    )
                    if mcp_ctx:
                        print(
                            f"[pipeline][item] [{i}/{len(exercises_to_translate)}] translation MCP context loaded ({len(mcp_ctx)} chars)",
                            file=sys.stderr,
                        )
                    translate_exercise(
                        _get_api_client(),
                        ex,
                        max_tokens=cfg.translation_max_tokens,
                        max_attempts=cfg.translation_max_attempts,
                        section_context=section_ctx,
                        mcp_context=mcp_ctx,
                    )
                except Exception as err:
                    tag_translation_failure(ex, err)
                    _emit_failure_event(ex, "translation_failed")
                    # Annotate the Lean file with the failure
                    full_text = output_file.read_text(encoding="utf-8")
                    full_text = annotate_lean_failure(
                        full_text, bid,
                        phase="translation",
                        failure_type="translation_error",
                        message=str(err),
                    )
                    output_file.write_text(full_text, encoding="utf-8")
                    print(f"[pipeline][item] [{i}/{len(exercises_to_translate)}] translation failed: {err}", file=sys.stderr)
                    _save_checkpoint(
                        checkpoint_path,
                        input_path=input_path,
                        output_file=output_file,
                        total=total,
                        next_item=i + 1,
                    )
                    continue

                # --- Step 2c: Insert translated code under block comment ---
                translated_code = _strip_lean_preamble(str(ex.lean_code or ""), section_name=section_name).strip()
                # Guard: LLM may return full file including frozen context (earlier blocks).
                # Extract only the current block's code region to avoid duplicating earlier blocks.
                _trans_extracted = extract_block_by_id(translated_code, bid)
                if _trans_extracted is not None:
                    translated_code = _trans_extracted[0].strip()
                if translated_code:
                    current_text = output_file.read_text(encoding="utf-8")
                    updated = insert_code_after_comment(current_text, bid, translated_code)
                    output_file.write_text(updated, encoding="utf-8")
                    print(f"[pipeline][item] [{i}/{len(exercises_to_translate)}] code inserted under block comment", file=sys.stderr)

                # --- Step 2d: Compile-fix until current block is stable ---
                if do_validate:
                    step_result = _compile_and_log(
                        output_file,
                        toolchain_dir=str(toolchain_dir),
                        timeout=cfg.lean_timeout_seconds,
                        use_lake_env=cfg.compile_use_lake_env,
                        auto_cache_recovery=cfg.compile_auto_cache_recovery,
                        run_label=f"translate_item_{i}_of_{len(exercises_to_translate)}",
                    )
                    _print_compile_result(step_result, context=f"[item {i}/{len(exercises_to_translate)}] combined file")
                    if step_result.returncode == 0 and not step_result.errors:
                        ex.status = ExerciseStatus.VALID
                        ex.compile_returncode = 0
                        ex.errors = []
                        ex.warnings = step_result.warnings
                        print(f"[pipeline][item] [{i}/{len(exercises_to_translate)}] combined validation OK", file=sys.stderr)
                        _save_checkpoint(
                            checkpoint_path,
                            input_path=input_path,
                            output_file=output_file,
                            total=total,
                            next_item=i + 1,
                        )
                    else:
                        ex.status = ExerciseStatus.REPAIR_FAILED
                        ex.compile_returncode = step_result.returncode
                        ex.errors = step_result.errors
                        ex.warnings = step_result.warnings
                        print(
                            f"[pipeline][item] [{i}/{len(exercises_to_translate)}] combined validation FAIL "
                            f"(errors={len(step_result.errors)})",
                            file=sys.stderr,
                        )
                        if do_recover:
                            entry_hist = compile_history_by_label.setdefault(
                                str(ex.label), RepairHistory(keep_recent=5)
                            )
                            ok = _recover_combined_file_for_item(
                                get_client=_get_recovery_client,
                                get_api_client=_get_api_client,
                                get_cli_client=_get_codex_client,
                                ex=ex,
                                output_file=output_file,
                                input_stem=input_stem,
                                toolchain_dir=str(toolchain_dir),
                                cfg=cfg,
                                base_report_hint=None,
                                history=entry_hist,
                                current_block_id=bid,
                                dedupe_relevance_checker=_dedupe_keep_if_related_by_llm,
                            )
                            if ok:
                                print(f"[pipeline][item] [{i}/{len(exercises_to_translate)}] recovered; continue", file=sys.stderr)
                                _save_checkpoint(
                                    checkpoint_path,
                                    input_path=input_path,
                                    output_file=output_file,
                                    total=total,
                                    next_item=i + 1,
                                )
                            else:
                                _print_compile_result(step_result, context=f"[item {i}/{len(exercises_to_translate)}] combined file (failed, recovery attempted)")
                                tag_unrecoverable(
                                    ex, phase="compile",
                                    message=f"item {label} failed recovery during translation-stage validation",
                                    errors=step_result.errors,
                                )
                                _emit_failure_event(ex, "unrecoverable_commented_out", {"block_id": bid})
                                full_text = output_file.read_text(encoding="utf-8")
                                full_text = comment_out_block(full_text, bid)
                                output_file.write_text(full_text, encoding="utf-8")
                                print(f"[pipeline][item] [{i}/{len(exercises_to_translate)}] UNRECOVERABLE: block commented out, continuing", file=sys.stderr)
                                _save_checkpoint(
                                    checkpoint_path,
                                    input_path=input_path,
                                    output_file=output_file,
                                    total=total,
                                    next_item=i + 1,
                                )
                        else:
                            tag_unrecoverable(
                                ex, phase="compile",
                                message=f"item {label} failed validation and recovery is disabled",
                                errors=step_result.errors,
                            )
                            _emit_failure_event(ex, "unrecoverable_commented_out", {"block_id": bid})
                            full_text = output_file.read_text(encoding="utf-8")
                            full_text = comment_out_block(full_text, bid)
                            output_file.write_text(full_text, encoding="utf-8")
                            print(f"[pipeline][item] [{i}/{len(exercises_to_translate)}] UNRECOVERABLE: block commented out, continuing", file=sys.stderr)
                            _save_checkpoint(
                                checkpoint_path,
                                input_path=input_path,
                                output_file=output_file,
                                total=total,
                                next_item=i + 1,
                            )
                else:
                    _save_checkpoint(
                        checkpoint_path,
                        input_path=input_path,
                        output_file=output_file,
                        total=total,
                        next_item=i + 1,
                    )

        # --- After translation pass: normalize any non-BLOCK-style comments ---
        try:
            _text = output_file.read_text(encoding="utf-8")
            import re as _re

            def _fix_match(m: _re.Match) -> str:
                first = m.group(1).strip()
                return f"/- [BLOCK {first}]\n"

            _text = _re.sub(r"/\-[ \t]*\n(Exercise[^\n\r]+)\n", _fix_match, _text)
            output_file.write_text(_text, encoding="utf-8")
            print(f"[pipeline] Normalized non-BLOCK comments in {output_file}", file=sys.stderr)
        except Exception as _err:
            print(f"[pipeline] Warning: failed to normalize comments: {_err}", file=sys.stderr)

        print(f"[pipeline] Combined Lean file saved (post-translate): {output_file}", file=sys.stderr)

    if not do_validate:
        print("[pipeline] Validation skipped.", file=sys.stderr)
    else:
        base_result = _compile_and_log(
            output_file,
            toolchain_dir=str(toolchain_dir),
            timeout=cfg.lean_timeout_seconds,
            use_lake_env=cfg.compile_use_lake_env,
            auto_cache_recovery=cfg.compile_auto_cache_recovery,
            run_label="baseline_combined_file",
        )
        _print_compile_result(base_result, context="baseline combined file")
        if base_result.returncode == 0 and not base_result.errors:
            print("[pipeline] Baseline combined-file validation: OK", file=sys.stderr)
            for ex in exercises:
                if ex.status not in (ExerciseStatus.ERROR, ExerciseStatus.UNRECOVERABLE):
                    ex.status = ExerciseStatus.VALID
                    ex.compile_returncode = 0
                    ex.errors = []
                    ex.warnings = []
        else:
            print(
                f"[pipeline] Baseline combined-file validation: FAIL "
                f"(errors={len(base_result.errors)}, warnings={len(base_result.warnings)})",
                file=sys.stderr,
            )

    # ---- Step 6: Optional semantic review/rewrite loop -------------
    # Defensive: ensure `exercises_to_translate` exists on all code paths.
    if 'exercises_to_translate' not in locals():
        exercises_to_translate = exercises
    semantic_targets = exercises_to_translate[resume_idx - 1 :] if resume_idx > 1 else exercises_to_translate
    if do_validate and do_semantic:
        _run_semantic_loop_on_combined_file(
            get_client=_get_semantic_client,
            get_api_client=_get_api_client,
            get_cli_client=_get_codex_client,
            exercises=semantic_targets,
            input_path=input_path,
            input_stem=input_stem,
            output_file=output_file,
            toolchain_dir=str(toolchain_dir),
            cfg=cfg,
            do_recover=do_recover,
            semantic_checkpoint_path=semantic_checkpoint_path,
            semantic_resume_label=semantic_resume_label,
            dedupe_relevance_checker=_dedupe_keep_if_related_by_llm,
            emit_failure_event=_emit_failure_event,
            emit_realtime_event=_emit_realtime_event,
        )
    elif do_semantic and not do_validate:
        print(
            "[pipeline] Semantic loop skipped: validation is disabled.",
            file=sys.stderr,
        )

    # ---- Step 7: Build semantic-review input -----------------------
    if output_file.exists() and do_postprocess:
        changed = postprocess_lean_file(
            output_file,
            llm_rewrite_comments=llm_rewrite_comments,
            llm_rewrite_all_comments=llm_rewrite_all_comments,
            llm_comments_only=llm_comments_only,
            get_client=_get_api_client if llm_rewrite_comments else None,
        )
        print(
            f"[pipeline] Postprocess {'applied' if changed else 'no-op'}: {output_file}",
            file=sys.stderr,
        )

    # ---- Step 8: Post-processing pipeline --------------------------
    # Step 8a: Failure report export
    all_exercises = exercises_to_translate if 'exercises_to_translate' in locals() else exercises
    try:
        written = export_failure_reports(all_exercises, report_dir)
        if written:
            print(f"[pipeline] Failure reports exported: {len(written)} file(s) to {report_dir}", file=sys.stderr)
        else:
            print("[pipeline] No failures to report.", file=sys.stderr)
    except Exception as _err:
        print(f"[pipeline] Warning: failure report export failed: {_err}", file=sys.stderr)

    # Step 8a.1: sync realtime failure events to error_problem/errors.json
    try:
        sync_stats = sync_realtime_failures_to_errors(
            report_dir=report_dir,
            data_dir=project_root / "data",
            errors_json_path=project_root / "error_problem" / "errors.json",
        )
        print(
            "[pipeline] Failure sync: "
            f"events={sync_stats.get('total_events', 0)} "
            f"matched={sync_stats.get('matched_records', 0)} "
            f"inserted={sync_stats.get('inserted_records', 0)} "
            f"existing={sync_stats.get('skipped_existing', 0)} "
            f"unmatched={sync_stats.get('unmatched_events', 0)}",
            file=sys.stderr,
        )
        print("[pipeline] realtime_failures.jsonl retained after sync.", file=sys.stderr)
    except Exception as _err:
        print(
            f"[pipeline] Warning: failure sync to error_problem/errors.json failed: {_err}",
            file=sys.stderr,
        )

    # Step 8b: Lean redundancy cleanup
    if output_file.exists():
        try:
            removals = cleanup_lean_file(output_file)
            if removals > 0:
                print(f"[pipeline] Redundancy cleanup: {removals} removal(s) in {output_file}", file=sys.stderr)
            else:
                print("[pipeline] Redundancy cleanup: no duplicates found.", file=sys.stderr)
        except Exception as _err:
            print(f"[pipeline] Warning: redundancy cleanup failed: {_err}", file=sys.stderr)

    # Step 8c: Math comment rendering
    if output_file.exists():
        try:
            math_changed = render_math_comments_file(
                output_file,
                get_client=_get_api_client if llm_rewrite_comments else None,
            )
            print(
                f"[pipeline] Math comment rendering: {'applied' if math_changed else 'no-op'}",
                file=sys.stderr,
            )
        except Exception as _err:
            print(f"[pipeline] Warning: math comment rendering failed: {_err}", file=sys.stderr)

    print(f"[pipeline] Combined Lean file saved: {output_file}", file=sys.stderr)
    if do_validate:
        final_result = _compile_and_log(
            output_file,
            toolchain_dir=str(toolchain_dir),
            timeout=cfg.lean_timeout_seconds,
            use_lake_env=cfg.compile_use_lake_env,
            auto_cache_recovery=cfg.compile_auto_cache_recovery,
            run_label="final_combined_file",
        )
        _print_compile_result(final_result, context="final combined file")
        if final_result.returncode == 0 and not final_result.errors:
            print("[pipeline] Final combined Lean validation: OK", file=sys.stderr)
        else:
            print(
                f"[pipeline] Final combined Lean validation: FAIL "
                f"(errors={len(final_result.errors)}, warnings={len(final_result.warnings)})",
                file=sys.stderr,
            )
            for i, err in enumerate(final_result.errors[:5], start=1):
                print(
                    f"[pipeline][final-error {i}] "
                    f"line {err.get('line', '?')}:{err.get('column', '?')} "
                    f"{err.get('message', '')}",
                    file=sys.stderr,
                )

    # ---- Summary --------------------------------------------------
    _print_summary(exercises)

    # ---- Token usage log ------------------------------------------
    clients_used = [c for c in (api_client, codex_client) if c is not None]
    if clients_used:
        _save_token_logs(clients_used, exercises, log_dir)
    else:
        print("[pipeline] No API calls made; token usage log skipped.", file=sys.stderr)

    print("[pipeline] Done.", file=sys.stderr)


# ------------------------------------------------------------------
# Helpers
# ------------------------------------------------------------------

def _print_summary(exercises: List[Exercise]) -> None:
    valid = sum(1 for e in exercises if e.status == ExerciseStatus.VALID)
    failed = sum(1 for e in exercises if e.status == ExerciseStatus.REPAIR_FAILED)
    unrecoverable = sum(1 for e in exercises if e.status == ExerciseStatus.UNRECOVERABLE)
    errors = sum(1 for e in exercises if e.status == ExerciseStatus.ERROR)
    other = len(exercises) - valid - failed - unrecoverable - errors
    print(
        f"\n[summary] total={len(exercises)}  valid={valid}  "
        f"repair_failed={failed}  unrecoverable={unrecoverable}  "
        f"error={errors}  other={other}",
        file=sys.stderr,
    )


def _save_token_logs(clients: List[Any], exercises: List[Exercise], log_dir: Path) -> None:
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
    log_path = log_dir / f"token_usage_{timestamp}.json"
    totals = {"prompt_tokens": 0, "completion_tokens": 0, "total_tokens": 0}
    calls: List[Dict[str, Any]] = []
    backends: List[Dict[str, Any]] = []
    for client in clients:
        client_totals = client.total_usage()
        totals["prompt_tokens"] += int(client_totals.get("prompt_tokens", 0))
        totals["completion_tokens"] += int(client_totals.get("completion_tokens", 0))
        totals["total_tokens"] += int(client_totals.get("total_tokens", 0))
        calls.extend(client.dump_usage())
        backends.append(
            {
                "model": getattr(client, "model", ""),
                "base_url": getattr(client, "base_url", ""),
                "total": client_totals,
            }
        )
    report = {
        "timestamp": timestamp,
        "total": totals,
        "backends": backends,
        "calls": calls,
        "exercises": [
            {
                "label": e.label,
                "status": e.status.value,
                "repair_attempts": e.repair_attempts,
                "num_errors": len(e.errors),
                "num_warnings": len(e.warnings),
            }
            for e in exercises
        ],
    }
    write_json(log_path, report)
    print(f"[pipeline] Token usage saved to {log_path}", file=sys.stderr)


def _checkpoint_file(*, log_dir: Path, input_stem: str) -> Path:
    return log_dir / f"resume_{input_stem}.json"


def _build_scaffold(exercises: List[Exercise]) -> str:
    """Build the initial combined Lean file scaffold with section wrappers.

    The scaffold contains ``import Mathlib``, ``noncomputable section``,
    standard project-wide ``open``/``open scoped`` directives, and empty
    ``namespace … end`` pairs for each distinct ``source_idx``.
    """
    parts: List[str] = [
        "import Mathlib",
        "",
        "noncomputable section",
        "",
        "open scoped Topology",
        "open scoped Matrix.Norms.L2Operator",
        "open scoped RealInnerProductSpace",
        "open scoped Gradient",
        "open scoped Matrix",
        "open Filter",
        "open scoped BigOperators",
    ]
    seen_sections: List[str] = []
    for ex in exercises:
        if _exercise_kind(ex) == "hints":
            continue
        sid = str((ex.raw or {}).get("source_idx") or "UNSPECIFIED").strip() or "UNSPECIFIED"
        sec_name = _safe_section_name(sid)
        if sec_name not in seen_sections:
            seen_sections.append(sec_name)
    for sec_name in seen_sections:
        parts.append("")
        parts.append(f"namespace {sec_name}")
        parts.append("")
        parts.append(f"end {sec_name}")
    return "\n".join(parts)


def _gather_translation_mcp_context(
    *,
    output_file: Path,
    ex: Exercise,
    toolchain_dir: str,
    cfg: Any,
) -> str:
    if not bool(getattr(cfg, "translation_mcp_enabled", False)):
        return ""
    if not output_file.exists():
        return ""
    try:
        from json2lean.config.mcp_helper import gather_recovery_context

        source_hint = str((ex.raw or {}).get("source_idx") or "")
        kind_hint = str((ex.raw or {}).get("kind") or "")
        term_hint = str((ex.raw or {}).get("term") or "")
        pseudo_errors = [{
            "line": 1,
            "column": 1,
            "message": f"translate {source_hint} {kind_hint} {term_hint}".strip(),
        }]

        # Derive tool names for logging (mirror helper's selection logic)
        configured = getattr(cfg, "translation_mcp_tools", None)
        mode = str(getattr(cfg, "translation_mcp_tool_mode", "targeted") or "targeted").strip().lower()
        if configured is not None:
            tool_names = [str(t).strip() for t in configured if str(t or "").strip()]
        else:
            if mode == "targeted":
                tool_names = [
                    "lean_unified_search",
                    "lean_leansearch",
                    "lean_loogle",
                    "lean_leanfinder",
                ]
            else:
                tool_names = [
                    "lean_unified_search",
                    "lean_leansearch",
                    "lean_loogle",
                    "lean_leanfinder",
                    "lean_file_contents",
                    "lean_local_search",
                ]

        # Log which MCP tools will be considered for translation context
        print(f"[translate]   MCP tools: {', '.join(tool_names)}", file=sys.stderr)

        context = gather_recovery_context(
            file_path=output_file.resolve(),
            project_root=Path(toolchain_dir).resolve(),
            lean_path="lean",
            pool_size=int(getattr(cfg, "translation_mcp_pool_size", 1) or 1),
            focus_line=1,
            focus_column=1,
            mcp_repo_path=getattr(cfg, "translation_mcp_repo_path", None),
            tool_mode=mode,
            errors=pseudo_errors,
            enabled_tools=configured,
        )
        return str(context or "").strip()
    except Exception as err:
        print(f"[translate][mcp] context unavailable for {ex.label}: {err}", file=sys.stderr)
        return ""


def _semantic_checkpoint_file(*, log_dir: Path, input_stem: str) -> Path:
    return log_dir / f"semantic_resume_{input_stem}.json"


def _load_checkpoint(path: Path) -> Dict[str, Any]:
    try:
        data = load_json(path)
    except Exception:
        return {}
    return data if isinstance(data, dict) else {}


def _save_checkpoint(
    path: Path,
    *,
    input_path: Path,
    output_file: Path,
    total: int,
    next_item: int,
) -> None:
    payload = {
        "input_json": str(input_path),
        "output_file": str(output_file),
        "total": int(total),
        "next_item": int(next_item),
        "updated_at_utc": datetime.now(timezone.utc).isoformat(),
    }
    write_json(path, payload)


def _run_semantic_loop_on_combined_file(
    *,
    get_client: Callable[[], Any],
    get_api_client: Callable[[], Any] | None = None,
    get_cli_client: Callable[[], Any] | None = None,
    exercises: List[Exercise],
    input_path: Path,
    input_stem: str,
    output_file: Path,
    toolchain_dir: str,
    cfg: Any,
    do_recover: bool,
    semantic_checkpoint_path: Path | None = None,
    semantic_resume_label: str = "",
    dedupe_relevance_checker: Callable[[str, str, str, str], bool] | None = None,
    emit_failure_event: Callable[[Exercise, str, Dict[str, Any] | None], None] | None = None,
    emit_realtime_event: Callable[[str, Dict[str, Any]], None] | None = None,
) -> None:
    """Block-based semantic review/rewrite loop.

    Semantic units are delimited by block comments (``/- [BLOCK …] -/``).
    Each block is processed strictly in order; earlier blocks are immutable.
    """
    min_required_rounds = 1
    if cfg.semantic_max_rounds <= 0:
        print("[pipeline] Semantic loop disabled by max_rounds <= 0.", file=sys.stderr)
        return

    print("[pipeline] === Semantic Review/Rewrite (block-based) ===", file=sys.stderr)
    targets = [ex for ex in exercises if _exercise_kind(ex) in {"defn", "thm", "opt_prob", "algo", "alg"}]
    if not targets:
        print("[semantic] no defn/thm/opt_prob/algo items; semantic loop skipped.", file=sys.stderr)
        return
    if str(semantic_resume_label or "").strip() == "__SEMANTIC_COMPLETE__":
        print("[semantic] resume checkpoint indicates semantic loop already complete; skip.", file=sys.stderr)
        return
    start_idx = 1
    resume_label = str(semantic_resume_label or "").strip()
    if resume_label:
        matched = False
        for idx, ex in enumerate(targets, 1):
            if str(ex.label) == resume_label:
                start_idx = idx
                matched = True
                break
        if matched:
            print(f"[semantic] resume from label `{resume_label}` (target {start_idx}/{len(targets)})", file=sys.stderr)
        else:
            print(f"[semantic] resume label `{resume_label}` not found; start from first target", file=sys.stderr)
    if start_idx > 1:
        targets = targets[start_idx - 1 :]

    report_path = (
        Path(__file__).resolve().parent / "review_log"
        / f"{input_stem}_semantic_report_round1.json"
    )
    report_path.parent.mkdir(parents=True, exist_ok=True)
    reports = _load_semantic_report_list(report_path)

    for i, ex in enumerate(targets, 1):
        label = str(ex.label)
        if isinstance(ex.raw, dict) and "index" not in ex.raw:
            ex.raw["index"] = ex.index
        bid = block_id_for(ex.raw)
        section_name = _safe_section_name(str((ex.raw or {}).get("source_idx") or "UNSPECIFIED"))
        print(f"[semantic][item] [{i}/{len(targets)}] {label} (block={bid})", file=sys.stderr)

        sem_history = RepairHistory(keep_recent=5)
        stabilized = False
        usable_seen = False
        last_semantic_status = ""
        last_semantic_report: Dict[str, Any] | None = None
        semantic_passes_run = 0
        semantic_exit_event = ""
        semantic_exit_extra: Dict[str, Any] = {}

        for pass_idx in range(1, cfg.semantic_max_rounds + 1):
            semantic_passes_run = pass_idx
            if not output_file.exists():
                print(f"[semantic][item] {label} -> missing combined file, stop", file=sys.stderr)
                return
            full_text = output_file.read_text(encoding="utf-8")

            # Extract current block using block_parser
            block_data = extract_block_comment_and_code(full_text, bid)
            if block_data is None:
                print(f"[semantic][item] {label} pass {pass_idx}: block {bid} not found, stop item", file=sys.stderr)
                semantic_exit_event = "semantic_block_not_found"
                semantic_exit_extra = {"block_id": bid, "pass": pass_idx}
                break
            chunk, chunk_start, chunk_end = block_data
            if not chunk.strip():
                print(f"[semantic][item] {label} pass {pass_idx}: empty block, stop item", file=sys.stderr)
                semantic_exit_event = "semantic_empty_block"
                semantic_exit_extra = {"block_id": bid, "pass": pass_idx}
                break

            # Extract only the code part (after comment)
            code_data = extract_block_by_id(full_text, bid)
            code_chunk = code_data[0] if code_data else ""
            ex.lean_code = code_chunk

            # Context = frozen code within the same section only
            section_context = frozen_context_in_section(full_text, bid, section_name)

            row = _build_single_review_row(
                ex, output_file, chunk,
                section_context=section_context,
            )
            report = review_record(
                get_client(), row,
                max_tokens=cfg.semantic_review_max_tokens,
                max_attempts=cfg.semantic_review_max_attempts,
            )
            report["pass"] = pass_idx
            reports.append(report)
            report_path.write_text(json.dumps(reports, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
            status = str(report.get("overall_status", "")).strip().lower()
            last_semantic_status = status
            last_semantic_report = report
            truth = str(report.get("truth_judgement", "unknown") or "unknown").strip().lower()
            counterexample = str(report.get("counterexample", "") or "").strip()
            if truth == "false" and counterexample:
                preview = counterexample[:160]
                print(
                    f"[semantic][review] {label} pass {pass_idx} -> "
                    f"{report.get('overall_status', 'unknown')} "
                    f"(truth=false, counterexample={preview})",
                    file=sys.stderr,
                )
            else:
                print(
                    f"[semantic][review] {label} pass {pass_idx} -> "
                    f"{report.get('overall_status', 'unknown')} (truth={truth})",
                    file=sys.stderr,
                )

            if status == "usable":
                usable_seen = True
                if pass_idx >= min_required_rounds:
                    stabilized = True
                    break
                continue

            target_issue = _pick_top_issue(report)
            report_summary = str(report.get("overall_status", "")) + "; " + str(report.get("top_priority_fix", ""))[:100]
            sem_history.record(
                attempt=sem_history.size + 1,
                loop="semantic", pass_idx=pass_idx,
                lean_code=code_chunk,
                errors=list(ex.errors or []),
                semantic_report_summary=report_summary,
            )
            new_code = rewrite_from_report(
                get_client(), row, report,
                max_tokens=cfg.semantic_rewrite_max_tokens,
                max_attempts=cfg.semantic_rewrite_max_attempts,
                target_issue=target_issue,
                history=sem_history,
            )
            if not new_code.strip():
                print(f"[semantic][rewrite] {label} pass {pass_idx} -> no output", file=sys.stderr)
                semantic_exit_event = "semantic_rewrite_no_output"
                semantic_exit_extra = {"block_id": bid, "pass": pass_idx}
                break
            new_chunk = _strip_lean_preamble(new_code, section_name=section_name).strip()
            # Guard: if the rewriter returned the full file (including frozen context
            # from section_context), extract only the current block's code portion so
            # that replace_block_code doesn't duplicate earlier blocks.
            _extracted = extract_block_by_id(new_chunk, bid)
            if _extracted is not None:
                new_chunk = _extracted[0].strip()
            
            if not new_chunk:
                print(f"[semantic][rewrite] {label} pass {pass_idx} -> empty", file=sys.stderr)
                semantic_exit_event = "semantic_rewrite_empty"
                semantic_exit_extra = {"block_id": bid, "pass": pass_idx}
                break
            if new_chunk == code_chunk.strip():
                print(
                    f"[semantic][rewrite] {label} pass {pass_idx} -> unchanged; continue until success or max rounds",
                    file=sys.stderr,
                )
                continue

            # Replace only the code region of this block (with built-in deduplication)
            full_text = output_file.read_text(encoding="utf-8")
            comment_text = extract_block_comment_text(full_text, bid) or ""
            keep_if_related = None
            if comment_text.strip() and dedupe_relevance_checker is not None:
                keep_if_related = (
                    lambda kind, removed_text, _bid=bid, _comment=comment_text:
                    dedupe_relevance_checker(_bid, _comment, kind, removed_text)
                )
            updated, dedup_stat = replace_block_code(
                full_text,
                bid,
                new_chunk,
                frozen_context=section_context,
                keep_if_related=keep_if_related,
            )
            if dedup_stat["removed_declarations"] > 0 or dedup_stat["removed_lines"] > 0:
                print(
                    f"[semantic][rewrite] {label} pass {pass_idx} -> dedupe removed "
                    f"decls={dedup_stat['removed_declarations']} lines={dedup_stat['removed_lines']}",
                    file=sys.stderr,
                )
            output_file.write_text(updated, encoding="utf-8")
            ex.lean_code = new_chunk
            print(f"[semantic][rewrite] {label} pass {pass_idx} -> rewritten", file=sys.stderr)

            post = _compile_and_log(
                output_file, toolchain_dir=toolchain_dir,
                timeout=cfg.lean_timeout_seconds,
                use_lake_env=cfg.compile_use_lake_env,
                auto_cache_recovery=cfg.compile_auto_cache_recovery,
                run_label=f"semantic_rewrite_{label}_pass_{pass_idx}",
            )
            _print_compile_result(post, context=f"[semantic][rewrite] {label} pass {pass_idx}")
            if post.returncode == 0 and not post.errors:
                ex.status = ExerciseStatus.VALID
                ex.compile_returncode = 0
                ex.errors = []
                ex.warnings = post.warnings
                continue
            ex.status = ExerciseStatus.REPAIR_FAILED
            ex.compile_returncode = post.returncode
            ex.errors = post.errors
            ex.warnings = post.warnings
            sem_history.record(
                attempt=sem_history.size + 1, loop="semantic", pass_idx=pass_idx,
                lean_code=new_chunk, errors=list(post.errors),
                semantic_report_summary=f"post-rewrite compile failure (errors={len(post.errors)})",
            )

            if not do_recover:
                print(f"[semantic][recover] {label} pass {pass_idx} -> disabled", file=sys.stderr)
                semantic_exit_event = "semantic_rewrite_compile_failed_recovery_disabled"
                semantic_exit_extra = {"block_id": bid, "pass": pass_idx}
                break
            print(f"[semantic][recover] {label} pass {pass_idx}", file=sys.stderr)
            ok = _recover_combined_file_for_item(
                get_client=get_client, ex=ex,
                get_api_client=get_api_client,
                get_cli_client=get_cli_client,
                output_file=output_file, input_stem=input_stem,
                toolchain_dir=toolchain_dir, cfg=cfg,
                base_report_hint=report, history=sem_history,
                current_block_id=bid,
                dedupe_relevance_checker=dedupe_relevance_checker,
            )
            if not ok:
                print(f"[semantic][recover] {label} pass {pass_idx} -> failed", file=sys.stderr)
                semantic_exit_event = "semantic_rewrite_recovery_failed"
                semantic_exit_extra = {"block_id": bid, "pass": pass_idx}
                break
            # Refresh ex.lean_code from file
            refreshed = output_file.read_text(encoding="utf-8")
            refreshed_data = extract_block_by_id(refreshed, bid)
            if refreshed_data:
                ex.lean_code = refreshed_data[0]
            print(f"[semantic][recover] {label} pass {pass_idx} -> fixed", file=sys.stderr)

        if not stabilized:
            print(f"[semantic][item] {label} -> not stabilized after <= {cfg.semantic_max_rounds} pass(es), continuing", file=sys.stderr)
            max_rounds = int(cfg.semantic_max_rounds)
            if not semantic_exit_event:
                semantic_exit_event = (
                    "semantic_not_usable_after_max_rounds"
                    if semantic_passes_run >= max_rounds and not usable_seen
                    else "semantic_not_usable"
                )
            extra = {
                "block_id": bid,
                "section": section_name,
                "passes": semantic_passes_run,
                "max_rounds": max_rounds,
                "last_status": last_semantic_status,
            }
            extra.update(semantic_exit_extra)
            if isinstance(last_semantic_report, dict):
                extra["overall_status"] = last_semantic_report.get("overall_status", "")
                extra["top_priority_fix"] = last_semantic_report.get("top_priority_fix", "")
                extra["issue_count"] = len(last_semantic_report.get("issues") or [])
                extra["truth_judgement"] = last_semantic_report.get("truth_judgement", "")
                extra["counterexample"] = str(last_semantic_report.get("counterexample", "") or "")[:300]
            tag_semantic_not_usable(
                ex,
                passes=semantic_passes_run,
                max_rounds=max_rounds,
                last_status=last_semantic_status,
                phase=semantic_exit_event,
                message=(
                    f"semantic loop exited without usable result: {semantic_exit_event} "
                    f"(passes={semantic_passes_run}, max_rounds={max_rounds}, "
                    f"last_status={last_semantic_status or 'unknown'})"
                ),
            )
            if emit_failure_event is not None:
                emit_failure_event(ex, semantic_exit_event, extra)
            elif emit_realtime_event is not None:
                emit_realtime_event(semantic_exit_event, extra)
        if semantic_checkpoint_path is not None:
            next_label = str(targets[i].label) if i < len(targets) else ""
            _save_checkpoint(
                semantic_checkpoint_path, input_path=input_path,
                output_file=output_file, total=len(targets), next_item=i + 1,
            )
            payload = _load_checkpoint(semantic_checkpoint_path)
            payload["next_label"] = next_label
            payload["semantic_scope_total"] = len(targets)
            payload["semantic_completed"] = not bool(next_label)
            write_json(semantic_checkpoint_path, payload)

    print(f"[semantic] report saved: {report_path}", file=sys.stderr)


def _exercise_kind(ex: Exercise) -> str:
    return str((ex.raw or {}).get("kind") or "").strip().lower()


def _load_semantic_report_list(path: Path) -> List[Dict[str, Any]]:
    """Load existing semantic reports so reruns append instead of truncating."""
    if not path.exists():
        return []
    try:
        text = path.read_text(encoding="utf-8").strip()
    except Exception:
        return []
    if not text:
        return []
    try:
        parsed = json.loads(text)
    except Exception:
        return []
    if isinstance(parsed, list):
        return [obj for obj in parsed if isinstance(obj, dict)]
    if isinstance(parsed, dict):
        return [parsed]
    return []


def _extract_original_problem_from_raw(raw: Dict[str, Any]) -> str:
    for key in ("problem", "content", "题目内容", "问题", "题目"):
        v = raw.get(key, "")
        if isinstance(v, str) and v.strip():
            return v
    return ""


def _extract_top_block_comment(lean_code: str) -> str:
    text = str(lean_code or "").lstrip()
    if not text.startswith("/-"):
        return ""
    end = text.find("-/")
    if end < 0:
        return ""
    return text[: end + 2]


def _build_single_review_row(
    ex: Exercise,
    lean_file: Path,
    lean_code: str,
    *,
    section_context: str = "",
) -> Dict[str, Any]:
    code = str(lean_code or "")
    section_name = _safe_section_name(str((ex.raw or {}).get("source_idx") or "UNSPECIFIED"))
    declaration_name = _extract_primary_declaration_name(code, expected_kind=_decl_keyword_for_exercise(ex))
    return {
        "label": str(ex.label),
        "section": section_name,
        "declaration_name": declaration_name,
        "lean_file": str(lean_file),
        "status": "matched" if code.strip() else "missing_lean",
        "original_problem": _extract_original_problem_from_raw(ex.raw if isinstance(ex.raw, dict) else {}),
        "original_raw": ex.raw if isinstance(ex.raw, dict) else {},
        "translation_record_source": "raw_block",
        "lean_comment": _extract_top_block_comment(code),
        "lean_code": code,
        "section_context": str(section_context or ""),
    }


def _issue_severity_rank(sev: str) -> int:
    s = str(sev or "").strip().upper()
    if s == "P0":
        return 0
    if s == "P1":
        return 1
    if s == "P2":
        return 2
    return 3


def _pick_top_issue(report: Dict[str, Any]) -> Dict[str, Any] | None:
    issues = report.get("issues", [])
    if not isinstance(issues, list):
        return None
    candidates = [it for it in issues if isinstance(it, dict)]
    if not candidates:
        return None
    candidates.sort(key=lambda i: _issue_severity_rank(str(i.get("severity", ""))))
    return candidates[0]


def _decl_keyword_for_exercise(ex: Exercise) -> str:
    k = _exercise_kind(ex)
    if k == "defn":
        return "def"
    if k == "thm":
        return "theorem"
    if k in {"alg", "algo"}:
        return "structure"
    return ""


def _find_section_bounds(full_text: str, section_name: str) -> tuple[int, int] | None:
    text = str(full_text or "")
    open_pat = re.compile(rf"(?m)^namespace\s+{re.escape(section_name)}\s*$")
    close_pat = re.compile(rf"(?m)^end\s+{re.escape(section_name)}\s*$")
    open_m = open_pat.search(text)
    if open_m is None:
        return None
    body_start = open_m.end()
    close_m = close_pat.search(text, body_start)
    if close_m is None:
        return None
    return body_start, close_m.start()


def _build_recovery_prompt_scope_for_block(
    full_text: str,
    *,
    section_name: str,
    block_id: str,
) -> tuple[str, str]:
    """Build recovery prompt code scoped to a single block namespace.

    Preferred mode:
    - shared preamble (imports/open directives)
    - `namespace <section_name>`
    - only the target block comment + code
    - `end <section_name>`

    Fallback mode:
    - shared preamble + full current section body
    """
    text = str(full_text or "")
    first_ns = re.search(r"(?m)^\s*namespace\s+[A-Za-z0-9_']+\s*$", text)
    preamble = text[:first_ns.start()].rstrip() if first_ns else ""

    block_scope = ""
    block_chunk = extract_block_comment_and_code(text, block_id)
    if block_chunk is not None:
        block_payload = block_chunk[0].strip()
        parts: List[str] = []
        if preamble:
            parts.extend([preamble, ""])
        parts.extend(
            [
                f"namespace {section_name}",
                "",
                block_payload,
                "",
                f"end {section_name}",
            ]
        )
        block_scope = "\n".join(parts).rstrip() + "\n"
        if extract_block_by_id(block_scope, block_id) is not None:
            return block_scope, "single_block_namespace"

    section_bounds = _find_section_bounds(text, section_name)
    if section_bounds is not None:
        scoped_start, scoped_end = section_bounds
        scoped_text = text[scoped_start:scoped_end]
    else:
        scoped_text = text
    section_scope = (preamble.rstrip() + "\n\n" + scoped_text.strip() + "\n")
    return section_scope, "section_fallback"


def _ensure_unique_labels(exercises: List[Exercise]) -> None:
    """Ensure each exercise label is unique and stable for per-item file pairing."""
    used: set[str] = set()
    for ex in exercises:
        base = str(ex.label or "").strip() or str(ex.raw.get("source_idx") or "exercise")
        idx = ex.raw.get("index", ex.index)
        candidate = base
        if candidate in used:
            candidate = f"{base}_{idx}"
        k = 2
        while candidate in used:
            candidate = f"{base}_{idx}_{k}"
            k += 1
        ex.label = candidate
        used.add(candidate)


def _safe_section_name(source_idx: str) -> str:
    name = re.sub(r"\s+", "_", str(source_idx or "").strip())
    name = re.sub(r"[^A-Za-z0-9_']", "_", name)
    if not name:
        name = "UNSPECIFIED"
    if not re.match(r"^[A-Za-z_]", name):
        name = f"S_{name}"
    return name


def _strip_lean_preamble(code: str, *, section_name: str = "") -> str:
    """Remove per-file preamble so snippets can be merged into one Lean file."""
    text = str(code or "").strip()
    if not text:
        return ""
    def _is_metadata_comment(comment_text: str) -> bool:
        s = str(comment_text or "")
        keys = (
            "index:",
            "source_idx:",
            "source:",
            "kind:",
            "term:",
            "problem:",
            "proof:",
            "direct_answer:",
        )
        return any(k in s for k in keys)

    lines = text.splitlines()
    out: List[str] = []
    in_top_comment = False
    top_comment_consumed = False
    current_comment_lines: List[str] = []
    for ln in lines:
        s = ln.strip()
        if not top_comment_consumed and not in_top_comment and s.startswith("/-"):
            # Only strip a true metadata header comment. Keep source comments.
            if "-/" in s:
                if _is_metadata_comment(s):
                    top_comment_consumed = True
                    continue
                out.append(ln)
                continue
            in_top_comment = True
            current_comment_lines = [ln]
            continue
        if in_top_comment:
            current_comment_lines.append(ln)
            if "-/" in s:
                in_top_comment = False
                block = "\n".join(current_comment_lines)
                if _is_metadata_comment(block):
                    top_comment_consumed = True
                else:
                    out.extend(current_comment_lines)
                current_comment_lines = []
            continue
        if s.startswith("import "):
            continue
        if s == "noncomputable section":
            continue
        if section_name:
            if s == f"namespace {section_name}" or s == f"end {section_name}":
                continue
        out.append(ln)
    return "\n".join(out).strip()


def _semantic_status_rank(status: str) -> int:
    s = (status or "").strip().lower()
    if s == "usable":
        return 2
    if s == "usable_with_revision":
        return 1
    if s == "not_usable_yet":
        return 0
    return -1


def _build_semantic_guard(report: Dict[str, Any]) -> str:
    label = str(report.get("label", ""))
    section = str(report.get("section", ""))
    status = str(report.get("overall_status", ""))
    top_fix = str(report.get("top_priority_fix", ""))
    truth = str(report.get("truth_judgement", "unknown"))
    counterexample = str(report.get("counterexample", "") or "")
    issues = report.get("issues", [])
    lines: List[str] = [
        f"Label: {label}",
        f"Section: {section}",
        f"Status before recovery: {status}",
        f"Truth judgement: {truth}",
        f"Top priority fix: {top_fix}",
        "Hard constraint: do not revert already-fixed semantic points.",
        "Hard constraint: do not reintroduce any issue listed below.",
    ]
    if counterexample.strip():
        lines.append(f"Counterexample witness: {counterexample.strip()}")
    if isinstance(issues, list):
        for idx, issue in enumerate(issues, 1):
            if not isinstance(issue, dict):
                continue
            sev = str(issue.get("severity", ""))
            issue_type = str(issue.get("issue_type", ""))
            location = str(issue.get("location", ""))
            reason = str(issue.get("reason", ""))
            lines.append(f"{idx}. [{sev}] {issue_type} @ {location}: {reason}")
    return "\n".join(lines).strip()


def _extract_primary_declaration_name(code: str, expected_kind: str = "") -> str:
    text = str(code or "")
    m = None
    for cand in _DECL_START_RE.finditer(text):
        if expected_kind and str(cand.group(1)) != expected_kind:
            continue
        m = cand
        break
    if not m:
        return ""
    start = m.end()
    name_match = re.search(r"[A-Za-z_][A-Za-z0-9_'.]*", text[start:])
    if not name_match:
        return ""
    return name_match.group(0)


def _recover_combined_file_for_item(
    *,
    get_client: Callable[[], Any],
    get_api_client: Callable[[], Any] | None = None,
    get_cli_client: Callable[[], Any] | None = None,
    ex: Exercise,
    output_file: Path,
    input_stem: str,
    toolchain_dir: str,
    cfg: Any,
    base_report_hint: Dict[str, Any] | None,
    history: RepairHistory | None = None,
    current_block_id: str = "",
    dedupe_relevance_checker: Callable[[str, str, str, str], bool] | None = None,
) -> bool:
    """Attempt compile-fix recovery for a single exercise.

    When *current_block_id* is given the repair is scoped to that block:
    - API warmup rounds use block-scoped prompting.
    - Later CLI rounds (if enabled) switch to full-file prompting.
    """
    label = str(ex.label)
    section = _safe_section_name(str((ex.raw or {}).get("source_idx") or "UNSPECIFIED"))
    expected_kind = _decl_keyword_for_exercise(ex)
    declaration_name = _extract_primary_declaration_name(ex.lean_code, expected_kind=expected_kind)
    semantic_guard = ""
    if base_report_hint:
        semantic_guard = _build_semantic_guard(base_report_hint)
    persisted_guard = _load_persisted_review_guard(
        Path(__file__).resolve().parent,
        input_stem,
        section,
        declaration_name=declaration_name,
    )
    if persisted_guard:
        semantic_guard = (semantic_guard + "\n\n" + persisted_guard).strip() if semantic_guard else persisted_guard
    target_decl = _extract_primary_declaration_name(ex.lean_code)
    tail = [
        "Hard constraint for this pass: keep edits minimal and targeted.",
        f"Target exercise label: {label}",
        f"Target section: {section}",
    ]
    if target_decl:
        tail.append(f"Preferred declaration to modify: {target_decl}")
    if current_block_id:
        tail.append(f"You may ONLY modify the code in block `{current_block_id}`. All earlier blocks are frozen.")
    semantic_guard = ((semantic_guard + "\n\n") if semantic_guard else "") + "\n".join(tail)
    semantic_report_text = (
        json.dumps(base_report_hint, ensure_ascii=False, indent=2)
        if isinstance(base_report_hint, dict)
        else ""
    )

    full_text = output_file.read_text(encoding="utf-8")

    def _apply_block_merge_from_combined(
        *,
        combined_text: str,
        original_text: str,
    ) -> bool:
        """Merge repaired target block back with section-local dedupe, then validate."""
        repaired_data = extract_block_by_id(combined_text, current_block_id)
        if repaired_data is None:
            print(f"[recover] {label}: block {current_block_id} disappeared after recovery", file=sys.stderr)
            return False
        repaired_block = repaired_data[0].strip()
        frozen = frozen_context_in_section(original_text, current_block_id, section)
        block_comment = extract_block_comment_text(original_text, current_block_id) or ""
        keep_if_related = None
        if dedupe_relevance_checker is not None and block_comment.strip():
            keep_if_related = (
                lambda kind, removed_text, _bid=current_block_id, _comment=block_comment:
                dedupe_relevance_checker(_bid, _comment, kind, removed_text)
            )
        updated, dedup_stat = replace_block_code(
            original_text,
            current_block_id,
            repaired_block,
            frozen_context=frozen,
            keep_if_related=keep_if_related,
        )
        if dedup_stat["removed_declarations"] > 0 or dedup_stat["removed_lines"] > 0:
            print(
                f"[recover] {label}: dedupe removed "
                f"decls={dedup_stat['removed_declarations']} lines={dedup_stat['removed_lines']}",
                file=sys.stderr,
            )
        output_file.write_text(updated, encoding="utf-8")

        post = _compile_and_log(
            output_file, toolchain_dir=toolchain_dir,
            timeout=cfg.lean_timeout_seconds,
            use_lake_env=cfg.compile_use_lake_env,
            auto_cache_recovery=cfg.compile_auto_cache_recovery,
            run_label=f"recover_block_{label}",
        )
        _print_compile_result(post, context=f"[recover] {label} block recovery validation")
        ex.compile_returncode = post.returncode
        ex.errors = post.errors
        ex.warnings = post.warnings
        if post.returncode == 0 and not post.errors:
            ex.status = ExerciseStatus.VALID
            return True
        ex.status = ExerciseStatus.REPAIR_FAILED
        return False

    # --- block-scoped recovery path ---
    if current_block_id:
        code_data = extract_block_by_id(full_text, current_block_id)
        if code_data is None:
            print(f"[recover] {label}: block {current_block_id} not found", file=sys.stderr)
            return False
        original_full_text = full_text
        # Keep recovery prompt scoped to the current block namespace.
        scoped_for_recover, scoped_mode = _build_recovery_prompt_scope_for_block(
            full_text,
            section_name=section,
            block_id=current_block_id,
        )
        print(
            f"[recover] {label}: prompt scope={scoped_mode} section={section} block={current_block_id}",
            file=sys.stderr,
        )
        # Recover directly on the original combined file content.
        recover_label = f"{output_file.stem}__{current_block_id}"

        combined_ex = Exercise(
            raw={"source_idx": "combined"},
            index=1, label=recover_label, problem="",
        )
        combined_ex.lean_code = original_full_text
        combined_ex.errors = list(ex.errors)
        combined_ex.warnings = list(ex.warnings)
        combined_ex.compile_returncode = int(ex.compile_returncode)

        total_rounds = max(1, int(getattr(cfg, "recovery_max_retries", 8) or 8))
        api_first_rounds = max(0, int(getattr(cfg, "recovery_api_first_rounds", 2) or 0))
        api_first_rounds = min(api_first_rounds, total_rounds)
        hybrid_ready = (
            get_api_client is not None
            and get_cli_client is not None
            and str(getattr(cfg, "llm_backend", "api") or "api").strip().lower() == "codex_cli"
        )
        history_payload = {recover_label: history} if history else None
        semantic_guard_payload = {recover_label: semantic_guard}
        semantic_report_payload = {recover_label: semantic_report_text} if semantic_report_text else None

        if hybrid_ready and api_first_rounds > 0:
            api_mcp_enabled = bool(getattr(cfg, "recovery_api_first_mcp_enabled", True))
            print(
                f"[recover] {label}: hybrid strategy api_rounds={api_first_rounds} "
                f"cli_rounds={max(0, total_rounds - api_first_rounds)} "
                f"api_mcp={'on' if api_mcp_enabled else 'off'}",
                file=sys.stderr,
            )
            still_broken = recover_all(
                get_api_client(), [combined_ex], output_file.parent,
                toolchain_dir=toolchain_dir,
                lean_timeout=cfg.lean_timeout_seconds,
                max_tokens=cfg.recovery_max_tokens,
                max_retries=api_first_rounds,
                mcp_enabled=api_mcp_enabled,
                mcp_pool_size=cfg.recovery_mcp_pool_size,
                mcp_repo_path=cfg.recovery_mcp_repo_path,
                mcp_tool_mode=cfg.recovery_mcp_tool_mode,
                mcp_tools=cfg.recovery_mcp_tools,
                semantic_guard_by_label=semantic_guard_payload,
                semantic_report_by_label=semantic_report_payload,
                history_by_label=history_payload,
                source_file=output_file,
                prompt_code_by_label={recover_label: scoped_for_recover},
                merge_block_id_by_label={recover_label: current_block_id},
                use_common_errors=cfg.recovery_use_common_errors,
            )
            if not still_broken:
                return _apply_block_merge_from_combined(
                    combined_text=combined_ex.lean_code,
                    original_text=original_full_text,
                )

            remaining_rounds = max(0, total_rounds - api_first_rounds)
            ex.compile_returncode = int(combined_ex.compile_returncode or ex.compile_returncode or 1)
            ex.errors = list(combined_ex.errors or ex.errors)
            ex.warnings = list(combined_ex.warnings or ex.warnings)
            if remaining_rounds <= 0:
                return False
            print(
                f"[recover] {label}: switch to CLI full-file recovery (remaining={remaining_rounds})",
                file=sys.stderr,
            )
            still_broken = recover_all(
                get_cli_client(),
                [combined_ex],
                output_file.parent,
                toolchain_dir=toolchain_dir,
                lean_timeout=cfg.lean_timeout_seconds,
                max_tokens=cfg.recovery_max_tokens,
                max_retries=remaining_rounds,
                mcp_enabled=cfg.recovery_mcp_enabled,
                mcp_pool_size=cfg.recovery_mcp_pool_size,
                mcp_repo_path=cfg.recovery_mcp_repo_path,
                mcp_tool_mode=cfg.recovery_mcp_tool_mode,
                mcp_tools=cfg.recovery_mcp_tools,
                semantic_guard_by_label=semantic_guard_payload,
                semantic_report_by_label=semantic_report_payload,
                history_by_label=history_payload,
                source_file=output_file,
                use_common_errors=cfg.recovery_use_common_errors,
            )
            if still_broken:
                ex.compile_returncode = int(combined_ex.compile_returncode or ex.compile_returncode or 1)
                ex.errors = list(combined_ex.errors or ex.errors)
                ex.warnings = list(combined_ex.warnings or ex.warnings)
                return False
            output_file.write_text(combined_ex.lean_code + "\n", encoding="utf-8")
            post = _compile_and_log(
                output_file, toolchain_dir=toolchain_dir,
                timeout=cfg.lean_timeout_seconds,
                use_lake_env=cfg.compile_use_lake_env,
                auto_cache_recovery=cfg.compile_auto_cache_recovery,
                run_label=f"recover_full_{label}",
            )
            _print_compile_result(post, context=f"[recover] {label} full-file recovery validation")
            ex.compile_returncode = post.returncode
            ex.errors = post.errors
            ex.warnings = post.warnings
            if post.returncode == 0 and not post.errors:
                ex.status = ExerciseStatus.VALID
                return True
            ex.status = ExerciseStatus.REPAIR_FAILED
            return False

        still_broken = recover_all(
            get_client(), [combined_ex], output_file.parent,
            toolchain_dir=toolchain_dir,
            lean_timeout=cfg.lean_timeout_seconds,
            max_tokens=cfg.recovery_max_tokens,
            max_retries=cfg.recovery_max_retries,
            mcp_enabled=cfg.recovery_mcp_enabled,
            mcp_pool_size=cfg.recovery_mcp_pool_size,
            mcp_repo_path=cfg.recovery_mcp_repo_path,
            mcp_tool_mode=cfg.recovery_mcp_tool_mode,
            mcp_tools=cfg.recovery_mcp_tools,
            semantic_guard_by_label=semantic_guard_payload,
            semantic_report_by_label=semantic_report_payload,
            history_by_label=history_payload,
            source_file=output_file,
            prompt_code_by_label={recover_label: scoped_for_recover},
            merge_block_id_by_label={recover_label: current_block_id},
            use_common_errors=cfg.recovery_use_common_errors,
        )
        if still_broken:
            ex.compile_returncode = int(combined_ex.compile_returncode or ex.compile_returncode or 1)
            ex.errors = list(combined_ex.errors or ex.errors)
            ex.warnings = list(combined_ex.warnings or ex.warnings)
            return False
        return _apply_block_merge_from_combined(
            combined_text=combined_ex.lean_code,
            original_text=original_full_text,
        )

    # --- legacy section-based recovery path (fallback) ---
    recover_label = output_file.stem

    combined_ex = Exercise(
        raw={"source_idx": "combined"},
        index=1,
        label=recover_label,
        problem="",
    )
    combined_ex.lean_code = full_text
    combined_ex.errors = list(ex.errors)
    combined_ex.warnings = list(ex.warnings)
    combined_ex.compile_returncode = int(ex.compile_returncode)

    still_broken = recover_all(
        get_client(),
        [combined_ex],
        output_file.parent,
        toolchain_dir=toolchain_dir,
        lean_timeout=cfg.lean_timeout_seconds,
        max_tokens=cfg.recovery_max_tokens,
        max_retries=cfg.recovery_max_retries,
        mcp_enabled=cfg.recovery_mcp_enabled,
        mcp_pool_size=cfg.recovery_mcp_pool_size,
        mcp_repo_path=cfg.recovery_mcp_repo_path,
        mcp_tool_mode=cfg.recovery_mcp_tool_mode,
        mcp_tools=cfg.recovery_mcp_tools,
        semantic_guard_by_label={recover_label: semantic_guard},
        semantic_report_by_label={recover_label: semantic_report_text} if semantic_report_text else None,
        history_by_label={recover_label: history} if history else None,
        source_file=output_file,
        use_common_errors=cfg.recovery_use_common_errors,
    )
    if still_broken:
        ex.compile_returncode = int(combined_ex.compile_returncode or ex.compile_returncode or 1)
        ex.errors = list(combined_ex.errors or ex.errors)
        ex.warnings = list(combined_ex.warnings or ex.warnings)
        cr = CompileResult(
            filename=output_file.name,
            stdout="",
            returncode=ex.compile_returncode,
            warnings=ex.warnings,
            errors=ex.errors,
        )
        _print_compile_result(cr, context=f"[recover] {label} section recovery failed")
        return False

    output_file.write_text(combined_ex.lean_code + "\n", encoding="utf-8")
    post = _compile_and_log(
        output_file,
        toolchain_dir=toolchain_dir,
        timeout=cfg.lean_timeout_seconds,
        use_lake_env=cfg.compile_use_lake_env,
        auto_cache_recovery=cfg.compile_auto_cache_recovery,
        run_label=f"recover_section_{label}",
    )
    _print_compile_result(post, context=f"[semantic] final validation after recovery")
    ex.compile_returncode = post.returncode
    ex.errors = post.errors
    ex.warnings = post.warnings
    if post.returncode == 0 and not post.errors:
        ex.status = ExerciseStatus.VALID
        return True
    ex.status = ExerciseStatus.REPAIR_FAILED
    return False


def _load_persisted_review_guard(
    project_root: Path,
    input_stem: str,
    section: str,
    declaration_name: str = "",
) -> str:
    review_dir = project_root / "review_log"
    if not review_dir.exists():
        return ""
    paths = sorted(review_dir.glob(f"{input_stem}_semantic_report_round*.json")) + sorted(
        review_dir.glob(f"{input_stem}_semantic_report_round*.jsonl")
    )
    if not paths:
        return ""

    latest_report: Dict[str, Any] | None = None
    for path in paths:
        try:
            text = path.read_text(encoding="utf-8")
        except Exception:
            continue
        stripped = text.strip()
        if not stripped:
            continue
        try:
            parsed = json.loads(stripped)
            if isinstance(parsed, list):
                for obj in parsed:
                    if isinstance(obj, dict) and (
                        (
                            str(obj.get("section", "")) == section
                            and (
                                not declaration_name
                                or str(obj.get("declaration_name", "")) == declaration_name
                            )
                        )
                    ):
                        latest_report = obj
                continue
            if isinstance(parsed, dict):
                if (
                    (
                        str(parsed.get("section", "")) == section
                        and (
                            not declaration_name
                            or str(parsed.get("declaration_name", "")) == declaration_name
                        )
                    )
                ):
                    latest_report = parsed
                continue
        except Exception:
            pass

        # Backward compatibility for old JSONL files
        for line in text.splitlines():
            line = line.strip()
            if not line:
                continue
            try:
                obj = json.loads(line)
            except Exception:
                continue
            if isinstance(obj, dict) and (
                (
                    str(obj.get("section", "")) == section
                    and (
                        not declaration_name
                        or str(obj.get("declaration_name", "")) == declaration_name
                    )
                )
            ):
                latest_report = obj
    if not latest_report:
        return ""
    return _build_semantic_guard(latest_report)


def _load_persisted_review_report(
    project_root: Path,
    input_stem: str,
    section: str,
) -> Dict[str, Any] | None:
    review_dir = project_root / "review_log"
    if not review_dir.exists():
        return None
    paths = sorted(review_dir.glob(f"{input_stem}_semantic_report_round*.json")) + sorted(
        review_dir.glob(f"{input_stem}_semantic_report_round*.jsonl")
    )
    if not paths:
        return None

    latest_report: Dict[str, Any] | None = None
    for path in paths:
        try:
            text = path.read_text(encoding="utf-8")
        except Exception:
            continue
        stripped = text.strip()
        if not stripped:
            continue
        try:
            parsed = json.loads(stripped)
            if isinstance(parsed, list):
                for obj in parsed:
                    if isinstance(obj, dict) and str(obj.get("section", "")) == section:
                        latest_report = obj
                continue
            if isinstance(parsed, dict):
                if str(parsed.get("section", "")) == section:
                    latest_report = parsed
                continue
        except Exception:
            pass

        for line in text.splitlines():
            line = line.strip()
            if not line:
                continue
            try:
                obj = json.loads(line)
            except Exception:
                continue
            if isinstance(obj, dict) and str(obj.get("section", "")) == section:
                latest_report = obj
    return latest_report


def _safe_dirname(name: str) -> str:
    return re.sub(r"[^\w\-.]", "_", str(name)) or "input"


# ------------------------------------------------------------------
# Entry-point
# ------------------------------------------------------------------

def main() -> None:
    parser = build_parser()
    args = parser.parse_args()
    try:
        run_pipeline(args)
    except KeyboardInterrupt:
        print("\n[pipeline] Interrupted by user.", file=sys.stderr)
        sys.exit(130)
    except Exception as fatal_err:
        print(
            f"\n[pipeline] FATAL uncaught exception: {fatal_err}\n"
            f"The pipeline attempted to continue through individual failures,\n"
            f"but this error was outside the per-exercise recovery scope.",
            file=sys.stderr,
        )
        import traceback
        traceback.print_exc(file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
