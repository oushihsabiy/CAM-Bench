#!/usr/bin/env python3
"""Batch/single-file preprocessing runner for JSON2LEAN.

Default behavior (no positional input):
- iterate all JSON files under <project>/data
- preprocess one by one
- write outputs to <project>/preprocessed_data/<stem>.json
- skip files whose preprocessed artifact already exists

Single-file behavior:
- pass one positional JSON path to preprocess only that file
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Dict, List


PROJECT_ROOT = Path(__file__).resolve().parents[1]
SRC_DIR = PROJECT_ROOT / "src"
if str(SRC_DIR) not in sys.path:
    sys.path.insert(0, str(SRC_DIR))


def _safe_stem(name: str) -> str:
    return re.sub(r"[^\w\-.]", "_", str(name)) or "input"


def _normalize_argv(argv: list[str]) -> list[str]:
    """Support shorthand forms like `--config5.json` / `--config5`."""
    out: list[str] = []
    for tok in argv:
        if tok.startswith("--config="):
            out.extend(["--config", tok.split("=", 1)[1]])
            continue
        if tok.startswith("--config") and tok != "--config":
            name = tok[2:]  # e.g. "config5.json" / "config5"
            if name.startswith("config"):
                if not name.endswith(".json"):
                    name = f"{name}.json"
                out.extend(["--config", name])
                continue
        out.append(tok)
    return out


def _resolve_input_path(arg: str, data_dir: Path) -> Path:
    raw = Path(arg).expanduser()
    if raw.is_absolute():
        return raw.resolve()
    candidates = [
        (Path.cwd() / raw).resolve(),
        (PROJECT_ROOT / raw).resolve(),
        (data_dir / raw).resolve(),
        (data_dir / raw.name).resolve(),
    ]
    for p in candidates:
        if p.exists():
            return p
    return candidates[0]


def _resolve_config_path(arg: str | None, find_config_fn) -> Path:
    if not arg:
        return find_config_fn(PROJECT_ROOT)
    raw = Path(arg).expanduser()
    if raw.is_absolute():
        return raw.resolve()
    candidates = [
        (Path.cwd() / raw).resolve(),
        (PROJECT_ROOT / raw).resolve(),
    ]
    for p in candidates:
        if p.exists():
            return p
    return candidates[0]


def _read_json_array(path: Path) -> List[Dict[str, Any]]:
    if not path.exists():
        return []
    try:
        text = path.read_text(encoding="utf-8").strip()
    except Exception:
        return []
    if not text:
        return []
    try:
        payload = json.loads(text)
    except Exception:
        return []
    if isinstance(payload, list):
        return [it for it in payload if isinstance(it, dict)]
    if isinstance(payload, dict) and isinstance(payload.get("exercises"), list):
        return [it for it in payload["exercises"] if isinstance(it, dict)]
    return []


def _normalize_text(text: Any) -> str:
    return re.sub(r"\W+", "", str(text or "").strip().lower())


def _stable_row_key(row: Dict[str, Any]) -> str:
    source_idx = _normalize_text(row.get("source_idx", ""))
    kind = _normalize_text(row.get("kind", ""))
    term = _normalize_text(row.get("term", ""))
    source = _normalize_text(row.get("source", ""))
    content = _normalize_text(row.get("content", row.get("problem", "")))
    if source_idx or content:
        return f"{source_idx}|{kind}|{term}|{source}|{content}"
    return json.dumps(row, ensure_ascii=False, sort_keys=True)


def _append_rows_to_errors_json(
    *,
    errors_json_path: Path,
    rows: List[Dict[str, Any]],
) -> int:
    if not rows:
        return 0
    existing = _read_json_array(errors_json_path)
    seen = {_stable_row_key(r) for r in existing}
    inserted = 0
    for row in rows:
        if not isinstance(row, dict):
            continue
        key = _stable_row_key(row)
        if key in seen:
            continue
        existing.append(row)
        seen.add(key)
        inserted += 1
    if inserted > 0:
        errors_json_path.parent.mkdir(parents=True, exist_ok=True)
        errors_json_path.write_text(
            json.dumps(existing, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )
    return inserted


def _exercise_source_idx(ex: Any) -> str:
    raw = getattr(ex, "raw", {}) or {}
    return str(raw.get("source_idx") or "").strip()


def _exercise_kind(ex: Any) -> str:
    raw = getattr(ex, "raw", {}) or {}
    return str(raw.get("kind") or "").strip().lower()


def _to_preprocessed_fallback_row(ex: Any) -> Dict[str, Any]:
    raw = getattr(ex, "raw", {}) or {}
    content = (
        str(raw.get("content") or "").strip()
        or str(raw.get("problem") or "").strip()
        or str(raw.get("题目内容") or "").strip()
    )
    row: Dict[str, Any] = {
        "index": int(raw.get("index", getattr(ex, "index", 0)) or 0),
        "source": str(raw.get("source") or ""),
        "source_idx": str(raw.get("source_idx") or getattr(ex, "label", "")),
        "kind": str(raw.get("kind") or "preprocess_failed"),
        "content": content,
    }
    term = str(raw.get("term") or "").strip()
    if term:
        row["term"] = term
    return row


def _rows_for_failed_exercises(
    *,
    preprocessed_rows: List[Dict[str, Any]],
    failed_exercises: List[Any],
) -> List[Dict[str, Any]]:
    out: List[Dict[str, Any]] = []
    for ex in failed_exercises:
        sid = _normalize_text(_exercise_source_idx(ex))
        k = _exercise_kind(ex)
        matched = []
        if sid:
            matched = [
                row
                for row in preprocessed_rows
                if _normalize_text(row.get("source_idx", "")) == sid
            ]
            if matched and k:
                matched_kind = [
                    row
                    for row in matched
                    if _normalize_text(row.get("kind", "")) == _normalize_text(k)
                ]
                if matched_kind:
                    matched = matched_kind
        if matched:
            out.extend(matched)
        else:
            out.append(_to_preprocessed_fallback_row(ex))
    return out


def _build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        description="Run JSON2LEAN preprocessing on one file or all files under data/."
    )
    p.add_argument(
        "input_json",
        nargs="?",
        help="Optional single input json path. If omitted, process all data/*.json.",
    )
    p.add_argument(
        "--data-dir",
        default=str(PROJECT_ROOT / "data"),
        help="Directory scanned when input_json is omitted (default: project/data).",
    )
    p.add_argument(
        "--output-dir",
        default=str(PROJECT_ROOT / "preprocessed_data"),
        help="Preprocessed output dir (default: project/preprocessed_data).",
    )
    p.add_argument(
        "--config",
        default=None,
        help="Path to config.json (default: auto-discover project config).",
    )
    p.add_argument(
        "--settings",
        default=None,
        help="Path to settings.json (default: project/settings.json if exists).",
    )
    p.add_argument(
        "--force",
        action="store_true",
        help="Re-run preprocessing even if output artifact already exists.",
    )
    p.add_argument(
        "--show-config",
        action="store_true",
        help="Print effective config (after settings overlay) and exit.",
    )
    return p


def _mask_secret(value: str) -> str:
    s = str(value or "")
    if len(s) <= 8:
        return "*" * len(s)
    return f"{s[:4]}...{s[-4:]}"


def _effective_config_dict(cfg, config_path: Path, settings_path: Path | None) -> dict:
    return {
        "config_path": str(config_path),
        "settings_path": str(settings_path) if settings_path else None,
        "api_key_masked": _mask_secret(cfg.api_key),
        "base_url": cfg.base_url,
        "model": cfg.model,
        "timeout_seconds": cfg.timeout_seconds,
        "preprocessing": {
            "enabled": cfg.preprocessing_enabled,
            "max_tokens": cfg.preprocessing_max_tokens,
            "max_attempts": cfg.preprocessing_max_attempts,
            "exclude_hints": cfg.preprocessing_exclude_hints,
            "normalize_skip_thm": cfg.preprocessing_normalize_skip_thm,
        },
        "translation": {
            "max_tokens": cfg.translation_max_tokens,
            "max_attempts": cfg.translation_max_attempts,
            "mcp_enabled": cfg.translation_mcp_enabled,
            "mcp_pool_size": cfg.translation_mcp_pool_size,
            "mcp_repo_path": cfg.translation_mcp_repo_path,
            "mcp_tool_mode": cfg.translation_mcp_tool_mode,
            "mcp_tools": cfg.translation_mcp_tools,
        },
        "recovery": {
            "max_tokens": cfg.recovery_max_tokens,
            "max_retries": cfg.recovery_max_retries,
            "mcp_enabled": cfg.recovery_mcp_enabled,
            "mcp_pool_size": cfg.recovery_mcp_pool_size,
            "mcp_repo_path": cfg.recovery_mcp_repo_path,
            "mcp_tool_mode": cfg.recovery_mcp_tool_mode,
            "mcp_tools": cfg.recovery_mcp_tools,
            "use_common_errors": cfg.recovery_use_common_errors,
        },
        "semantic": {
            "enabled": cfg.semantic_enabled,
            "max_rounds": cfg.semantic_max_rounds,
            "review_max_tokens": cfg.semantic_review_max_tokens,
            "review_max_attempts": cfg.semantic_review_max_attempts,
            "rewrite_max_tokens": cfg.semantic_rewrite_max_tokens,
            "rewrite_max_attempts": cfg.semantic_rewrite_max_attempts,
        },
        "lean": {
            "toolchain_dir": cfg.lean_toolchain_dir,
            "timeout_seconds": cfg.lean_timeout_seconds,
        },
        "compile": {
            "use_lake_env": cfg.compile_use_lake_env,
            "auto_cache_recovery": cfg.compile_auto_cache_recovery,
        },
    }


def main() -> int:
    args = _build_parser().parse_args(_normalize_argv(sys.argv[1:]))

    try:
        from json2lean.loader import find_config, load_config, load_settings
    except ModuleNotFoundError as err:
        print(
            f"[preprocess-runner] missing dependency: {err}. "
            "Please run with the project venv, e.g. "
            "`/root/workspace/benchmark/.venv/bin/python scripts/run_preprocess.py`.",
            file=sys.stderr,
        )
        return 3

    data_dir = Path(args.data_dir).expanduser().resolve()
    out_dir = Path(args.output_dir).expanduser().resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    config_path = _resolve_config_path(args.config, find_config)
    cfg = load_config(config_path)

    settings_raw = args.settings
    if not settings_raw:
        auto_settings = PROJECT_ROOT / "settings.json"
        if auto_settings.exists():
            settings_raw = str(auto_settings)
    settings_path = Path(settings_raw).expanduser().resolve() if settings_raw else None
    settings_dict = load_settings(settings_path) if settings_path else {}
    if settings_dict:
        cfg = cfg.overlay_settings(settings_dict)

    if args.show_config:
        print(
            json.dumps(
                _effective_config_dict(cfg, config_path, settings_path),
                ensure_ascii=False,
                indent=2,
            )
        )
        return 0

    print(
        f"[preprocess-runner] using config={config_path} settings={settings_path}",
        file=sys.stderr,
    )

    try:
        from json2lean.config.api_client import APIClient
        from json2lean.loader import load_json
        from json2lean.parser import parse_exercises
        from json2lean.preprocess import preprocess_all
        from postprocess.failure_report import append_failure_event
        from postprocess.fault_tolerance import tag_preprocess_failure
    except ModuleNotFoundError as err:
        print(
            f"[preprocess-runner] missing dependency: {err}. "
            "Please run with the project venv, e.g. "
            "`/root/workspace/benchmark/.venv/bin/python scripts/run_preprocess.py`.",
            file=sys.stderr,
        )
        return 3

    client = APIClient(
        api_key=cfg.api_key,
        base_url=cfg.base_url,
        model=cfg.model,
        timeout=cfg.timeout_seconds,
        token_log_dir=PROJECT_ROOT / "logs",
        realtime_token_log=True,
    )

    inputs: List[Path]
    if args.input_json:
        inputs = [_resolve_input_path(args.input_json, data_dir)]
    else:
        if not data_dir.exists():
            print(f"[preprocess-runner] data dir not found: {data_dir}", file=sys.stderr)
            return 2
        inputs = sorted(p.resolve() for p in data_dir.glob("*.json"))

    if not inputs:
        print("[preprocess-runner] no input json files found.", file=sys.stderr)
        return 0

    total = len(inputs)
    processed = 0
    skipped = 0
    failed_files = 0
    failed_items_total = 0
    report_dir = PROJECT_ROOT / "logs" / "failure_reports"
    errors_json_path = PROJECT_ROOT / "error_problem" / "errors.json"

    print(
        f"[preprocess-runner] start: files={total} data_dir={data_dir} output_dir={out_dir}",
        file=sys.stderr,
    )

    for idx, input_path in enumerate(inputs, 1):
        if not input_path.exists():
            failed_files += 1
            print(f"[preprocess-runner] [{idx}/{total}] missing input: {input_path}", file=sys.stderr)
            continue

        stem = _safe_stem(input_path.stem)
        out_path = out_dir / f"{stem}.json"

        if out_path.exists() and not args.force:
            skipped += 1
            print(f"[preprocess-runner] [{idx}/{total}] skip (exists): {out_path}", file=sys.stderr)
            continue

        try:
            data = load_json(input_path)
            exercises = parse_exercises(data)
            if not exercises:
                failed_files += 1
                print(
                    f"[preprocess-runner] [{idx}/{total}] no exercises found: {input_path}",
                    file=sys.stderr,
                )
                continue

            print(
                f"[preprocess-runner] [{idx}/{total}] preprocess: {input_path.name} "
                f"(exercises={len(exercises)})",
                file=sys.stderr,
            )
            failed_exercises: List[Any] = []
            failed_exercise_ids: set[int] = set()

            def _on_preprocess_failure(ex: Any, err: Exception) -> None:
                label = str(getattr(ex, "label", "") or "").strip()
                if not label:
                    return
                ex_id = id(ex)
                if ex_id not in failed_exercise_ids:
                    failed_exercises.append(ex)
                    failed_exercise_ids.add(ex_id)
                if str(getattr(ex, "failure_type", "") or "").strip():
                    return
                tag_preprocess_failure(ex, err, phase="preprocess")
                append_failure_event(
                    ex,
                    report_dir,
                    event="preprocess_failed",
                    lean_file=str(out_path),
                )

            failed_labels = preprocess_all(
                client,
                exercises,
                max_tokens=cfg.preprocessing_max_tokens,
                max_attempts=cfg.preprocessing_max_attempts,
                normalize_skip_thm=cfg.preprocessing_normalize_skip_thm,
                exclude_hints=cfg.preprocessing_exclude_hints,
                output_dir=out_dir,
                input_stem=stem,
                on_failure=_on_preprocess_failure,
            )

            # Backfill edge-cases where callback wasn't triggered for a failed label.
            failed_label_set = set(failed_labels)
            for ex in exercises:
                label = str(getattr(ex, "label", "") or "").strip()
                if label not in failed_label_set:
                    continue
                ex_id = id(ex)
                if ex_id not in failed_exercise_ids:
                    failed_exercises.append(ex)
                    failed_exercise_ids.add(ex_id)
                if not str(getattr(ex, "failure_type", "") or "").strip():
                    err = RuntimeError(f"preprocess_all failed for {label}")
                    tag_preprocess_failure(ex, err, phase="preprocess")
                    append_failure_event(
                        ex,
                        report_dir,
                        event="preprocess_failed",
                        lean_file=str(out_path),
                    )

            if failed_exercises:
                preprocessed_rows = _read_json_array(out_path)
                error_rows = _rows_for_failed_exercises(
                    preprocessed_rows=preprocessed_rows,
                    failed_exercises=failed_exercises,
                )
                inserted = _append_rows_to_errors_json(
                    errors_json_path=errors_json_path,
                    rows=error_rows,
                )
                print(
                    f"[preprocess-runner] [{idx}/{total}] error_problem updated: "
                    f"added={inserted} candidate_rows={len(error_rows)}",
                    file=sys.stderr,
                )

            processed += 1
            if failed_labels:
                failed_items_total += len(failed_labels)
                print(
                    f"[preprocess-runner] [{idx}/{total}] done with partial failures: "
                    f"{len(failed_labels)} exercise(s)",
                    file=sys.stderr,
                )
            else:
                print(f"[preprocess-runner] [{idx}/{total}] done: {out_path}", file=sys.stderr)
        except Exception as err:
            failed_files += 1
            print(
                f"[preprocess-runner] [{idx}/{total}] FAILED {input_path}: {err}",
                file=sys.stderr,
            )

    print(
        f"[preprocess-runner] summary: processed={processed} skipped={skipped} "
        f"failed_files={failed_files} failed_items={failed_items_total}",
        file=sys.stderr,
    )
    return 1 if failed_files > 0 else 0


if __name__ == "__main__":
    raise SystemExit(main())
