"""Automatic Lean code recovery via LLM.

When validation fails, this module sends the broken Lean code together with
the compiler errors to the LLM and asks it to produce a corrected version.
The validate → recover cycle repeats up to a configurable limit.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Callable, Dict, List

from ..config.api_client import APIClient, extract_lean_code
from ..semantic.declaration_policy import validate_top_level_contract
from ..loader import load_prompt
from ..models import Exercise, ExerciseStatus
from ..repair_history import RepairHistory
from ..semantic.source_comment_policy import enforce_exact_source_comments
from .compiling_checker import validate_exercise
from .compiling_checker import print_compile_result
from ..writer import write_lean_file
from ..block_parser import extract_block_by_id, replace_block_code


_DECL_KEYWORDS = (
    "def",
    "theorem",
    "lemma",
    "structure",
    "class",
    "inductive",
    "abbrev",
    "opaque",
    "axiom",
    "constant",
    "instance",
)


def _format_errors(exercise: Exercise) -> str:
    """Format compiler errors into a readable block for the LLM."""
    parts: List[str] = []
    for err in exercise.errors:
        loc = f"line {err.get('line', '?')}:{err.get('column', '?')}"
        parts.append(f"  {loc}: {err.get('message', '')}")
        lc = err.get("line_content", "")
        if lc:
            parts.append(f"    | {lc}")
    return "\n".join(parts)


def _error_signature(exercise: Exercise) -> str:
    """Compact signature for repeated-error detection across attempts.

    Uses the first two non-empty lines of each error message (instead of only
    the first line) so that generic openers like 'application type mismatch'
    are distinguished by their second context line.
    """
    if not exercise.errors:
        return "no_structured_error"
    items: List[str] = []
    for err in exercise.errors[:5]:
        line = int(err.get("line") or 0)
        col = int(err.get("column") or 0)
        msg_lines = [
            ln for ln in str(err.get("message", "")).strip().splitlines()
            if ln.strip()
        ]
        # Take up to two lines for a more discriminating signature.
        msg = " // ".join(re.sub(r"\s+", " ", ln) for ln in msg_lines[:2])
        items.append(f"{line}:{col}:{msg}")
    return " | ".join(items)


def _extract_already_declared_name(exercise: Exercise) -> str:
    """Extract duplicated declaration name from Lean error messages."""
    for err in exercise.errors:
        msg = str(err.get("message", "") or "")
        if "has already been declared" not in msg:
            continue
        patterns = [
            r"`([A-Za-z_][A-Za-z0-9_']*)`\s+has already been declared",
            r"'([A-Za-z_][A-Za-z0-9_']*)'\s+has already been declared",
            r"\"([A-Za-z_][A-Za-z0-9_']*)\"\s+has already been declared",
            r"([A-Za-z_][A-Za-z0-9_']*)\s+has already been declared",
        ]
        for pat in patterns:
            m = re.search(pat, msg)
            if m:
                return m.group(1)
    return ""


def _next_fresh_name(code: str, base_name: str) -> str:
    """Return a fresh Lean identifier by appending one or more apostrophes."""
    candidate = f"{base_name}'"
    while re.search(
        rf"(?<![A-Za-z0-9_']){re.escape(candidate)}(?![A-Za-z0-9_'])",
        code,
    ):
        candidate += "'"
    return candidate


def _rename_declaration_once(code: str, old: str, new: str) -> tuple[str, bool]:
    """Rename one top-level declaration head from ``old`` to ``new``."""
    pattern = re.compile(
        rf"(^\s*(?:{'|'.join(_DECL_KEYWORDS)})\s+){re.escape(old)}(?![A-Za-z0-9_'])",
        re.MULTILINE,
    )
    replaced, n = pattern.subn(rf"\1{new}", code, count=1)
    return replaced, n > 0


def _auto_fix_already_declared(exercise: Exercise) -> tuple[bool, str]:
    """Try local fix for duplicated declaration names.

    If error contains ``has already been declared``, rename conflicting
    declaration to a fresh name by appending apostrophes.
    """
    dup_name = _extract_already_declared_name(exercise)
    if not dup_name:
        return False, ""
    if not exercise.lean_code.strip():
        return False, ""
    new_name = _next_fresh_name(exercise.lean_code, dup_name)
    rewritten, ok = _rename_declaration_once(exercise.lean_code, dup_name, new_name)
    if not ok:
        return False, ""
    exercise.lean_code = rewritten
    return True, f"{dup_name} -> {new_name}"


def _load_common_errors() -> str:
    """Load the common errors reference file (常见错误.md) if it exists."""
    # Project root is 3 levels up from src/json2lean/compile/
    root = Path(__file__).resolve().parents[3]
    candidate = root / "常见错误.md"
    if candidate.exists():
        return candidate.read_text(encoding="utf-8").strip()
    return ""


def _build_prompt(
    base_prompt: str,
    lean_code: str,
    error_text: str,
    mcp_context: str = "",
    semantic_guard: str = "",
    semantic_report: str = "",
    retry_guidance: str = "",
    history_block: str = "",
    common_errors: str = "",
) -> str:
    extra = ""
    if mcp_context.strip():
        extra = f"== Additional MCP context ==\n{mcp_context.strip()}\n\n"
    semantic_extra = ""
    if semantic_guard.strip():
        semantic_extra = (
            "== Semantic guard (must preserve) ==\n"
            f"{semantic_guard.strip()}\n\n"
        )
    semantic_report_extra = ""
    if semantic_report.strip():
        semantic_report_extra = (
            "== Semantic review report (issues + suggested fixes) ==\n"
            f"{semantic_report.strip()}\n\n"
        )
    semantic_priority_extra = ""
    if semantic_report.strip():
        semantic_priority_extra = (
            "== Required recovery policy ==\n"
            "1) Treat semantic report as primary guidance.\n"
            "2) Apply top_priority_fix and issues[*].suggested_fix first.\n"
            "3) Then resolve remaining Lean compiler errors with minimal edits.\n"
            "4) Do not rewrite unrelated parts.\n"
            "5) Do not reintroduce reported semantic issues.\n\n"
        )
    retry_extra = ""
    if retry_guidance.strip():
        retry_extra = (
            "== Retry guidance (must follow) ==\n"
            f"{retry_guidance.strip()}\n\n"
        )
    history_extra = ""
    if history_block.strip():
        history_extra = f"{history_block.strip()}\n\n"
    common_errors_extra = ""
    if common_errors.strip():
        common_errors_extra = (
            "== Known common errors and rules (must check before fixing) ==\n"
            f"{common_errors.strip()}\n\n"
        )
    return (
        f"{base_prompt}\n\n"
        f"{common_errors_extra}"
        f"{semantic_priority_extra}"
        f"{retry_extra}"
        f"{history_extra}"
        f"== Lean code ==\n```lean\n{lean_code}\n```\n\n"
        f"== Compiler errors ==\n{error_text}\n\n"
        f"{semantic_extra}"
        f"{semantic_report_extra}"
        f"{extra}"
        "Output ONLY the corrected Lean file. No explanations."
    )

def _safe_label(label: str) -> str:
    return re.sub(r"[^\w\-.]", "_", str(label)) or "exercise"


def _mcp_tool_names(
    tool_mode: str,
    has_focus_pos: bool,
    configured_tools: List[str] | None = None,
) -> List[str]:
    if configured_tools is not None:
        # When settings.recovery.mcp_tools is explicitly provided, recovery must
        # follow this list exactly (null means "use mode defaults").
        seen: set[str] = set()
        picked: List[str] = []
        for name in configured_tools:
            n = str(name or "").strip()
            if n and n not in seen:
                seen.add(n)
                picked.append(n)
        return picked

    mode = (tool_mode or "").strip().lower()
    if mode == "targeted":
        names = [
            "lean_unified_search",
            "lean_leansearch",
            "lean_loogle",
            "lean_leanfinder",
        ]
        return names

    names = [
        "lean_unified_search",
        "lean_leansearch",
        "lean_loogle",
        "lean_leanfinder",
    ]
    if (tool_mode or "").strip().lower() == "all":
        names.extend(
            [
                "lean_file_contents",
                "lean_local_search",
            ]
        )
    return names


def _resolve_mcp_tool_mode(config_mode: str, attempt: int) -> str:
    """Resolve MCP tool mode for current recovery attempt.

    Supported config values:
    - "dynamic"/"auto": attempts 1-3 => targeted, 4+ => all
    - "targeted" | "focused" | "all": fixed mode for all attempts
    """
    mode = (config_mode or "").strip().lower()
    if mode in {"dynamic", "auto"}:
        return "targeted" if attempt <= 3 else "all"
    if mode in {"targeted", "focused", "all"}:
        return mode
    # Backward-compatible default.
    return "focused"


def _extract_decl_bodies(code: str) -> Dict[str, str]:
    """Return theorem/lemma declaration bodies keyed by declaration name."""
    pat = re.compile(
        r"^\s*(?:theorem|lemma)\s+([A-Za-z0-9_']+)\b(?P<body>[\s\S]*?)\s*:=\s*by\b",
        re.MULTILINE,
    )
    out: Dict[str, str] = {}
    for m in pat.finditer(code or ""):
        out[m.group(1)] = m.group("body")
    return out


def _looks_like_semantic_weakening(before_code: str, after_code: str) -> bool:
    """Heuristic guard for major statement weakening during recovery."""
    before = _extract_decl_bodies(before_code)
    after = _extract_decl_bodies(after_code)
    if not before or not after:
        return False

    before_goal_names = {n for n in before if "goal" in n.lower()}
    after_goal_names = {n for n in after if "goal" in n.lower()}
    if before_goal_names and not before_goal_names.issubset(after_goal_names):
        return True

    for name, before_body in before.items():
        after_body = after.get(name)
        if after_body is None:
            continue
        b = " ".join(before_body.split()).lower()
        a = " ".join(after_body.split()).lower()
        if not re.search(r'\btrue\b', b) and re.search(r'\btrue\b', a):
            return True
        if not re.search(r'\bfalse\b', b) and re.search(r'\bfalse\b', a):
            return True
        before_has_zero_disj = bool(re.search(r"=\s*0\s*∨|∨\s*[^:]*=\s*0", b))
        after_has_zero_disj = bool(re.search(r"=\s*0\s*∨|∨\s*[^:]*=\s*0", a))
        if after_has_zero_disj and not before_has_zero_disj:
            return True
    return False


def recover_exercise(
    client: APIClient,
    exercise: Exercise,
    output_dir: Path,
    *,
    toolchain_dir: str = "lean",
    lean_timeout: int = 120,
    max_tokens: int = 4096,
    max_retries: int = 8,
    prompt_text: str | None = None,
    mcp_context_provider: Callable[[Path, Exercise, str], str] | None = None,
    mcp_tool_mode: str = "focused",
    mcp_tools: List[str] | None = None,
    semantic_guard: str = "",
    semantic_report: str = "",
    history: RepairHistory | None = None,
    source_file: Path | None = None,
    prompt_code_override: str | None = None,
    merge_block_id: str = "",
    use_common_errors: bool = True,
) -> bool:
    """Attempt to fix *exercise* through repeated validate→recover cycles.

    When *source_file* is given the repaired code is written directly to that
    file (instead of creating a temporary file via ``write_lean_file``) and
    the compiler is invoked on it.

    Returns ``True`` if the exercise eventually compiles, ``False`` otherwise.
    """
    if prompt_text is None:
        prompt_text = load_prompt("compiling_fixer")

    common_errors = ""
    if use_common_errors:
        common_errors = _load_common_errors()
        if common_errors:
            print("[recover]   common errors reference loaded", file=sys.stderr)

    if history is None:
        history = RepairHistory(keep_recent=5)

    signature_counts: Dict[str, int] = {}
    for attempt in range(1, max_retries + 1):
        if exercise.is_valid:
            return True

        error_text = _format_errors(exercise)
        if not error_text:
            error_text = "(no structured errors; returncode was non-zero)"
        sig = _error_signature(exercise)
        # signature_counts is incremented only *after* an actual compile attempt
        # (see bottom of loop). Check counts accumulated from previous validated attempts.
        retry_guidance = ""
        if signature_counts.get(sig, 0) >= 2:
            retry_guidance = (
                "The same core errors have repeated across attempts.\n"
                "Do NOT repeat the same fix pattern.\n"
                "Switch to a different formalization strategy: "
                "redefine the problematic local notion with a simpler and more canonical "
                "type-stable definition, then minimally update dependent theorem signatures."
            )

        # Record current state into history before sending to LLM
        history.record(
            attempt=attempt,
            loop="compile",
            lean_code=exercise.lean_code,
            errors=list(exercise.errors),
            error_signature=sig,
        )
        history_block = history.format_for_prompt()
        # Compute how many recent entries are actually included in the prompt.
        # `RepairHistory.format_for_prompt()` keeps only the most recent
        # `history.keep_recent` attempts; `history.size` is the total recorded.
        try:
            keep_recent = int(getattr(history, "keep_recent", history.size))
            included = min(history.size, keep_recent)
        except Exception:
            included = history.size

        if history.size > 0:
            print(
                f"[recover]   history: {included} entries included in prompt (total {history.size})",
                file=sys.stderr,
            )

        print(
            f"[recover] {exercise.label} attempt {attempt}/{max_retries}",
            file=sys.stderr,
        )
        if retry_guidance:
            print(
                "[recover]   repeated error signature detected; enforcing alternative strategy",
                file=sys.stderr,
            )

        mcp_context = ""
        if mcp_context_provider is not None:
            lean_file_for_context = source_file if source_file is not None else output_dir / f"{_safe_label(exercise.label)}.lean"
            has_focus_pos = bool(exercise.errors) and bool(exercise.errors[0].get("line"))
            resolved_mode = _resolve_mcp_tool_mode(mcp_tool_mode, attempt)
            tool_names = _mcp_tool_names(
                resolved_mode,
                has_focus_pos,
                configured_tools=mcp_tools,
            )
            print(
                f"[recover]   MCP tools: {', '.join(tool_names)}",
                file=sys.stderr,
            )
            try:
                mcp_context = mcp_context_provider(
                    lean_file_for_context,
                    exercise,
                    resolved_mode,
                )
                if mcp_context.strip():
                    print(
                        f"[recover]   MCP context loaded ({len(mcp_context)} chars)",
                        file=sys.stderr,
                    )
                else:
                    print("[recover]   MCP context empty", file=sys.stderr)
            except Exception as err:
                print(f"[recover]   MCP context unavailable: {err}", file=sys.stderr)

        prompt_code = prompt_code_override if (prompt_code_override is not None) else exercise.lean_code
        full_prompt = _build_prompt(
            prompt_text,
            prompt_code,
            error_text,
            mcp_context,
            semantic_guard,
            semantic_report,
            retry_guidance,
            history_block=history_block,
            common_errors=common_errors,
        )
        try:
            response = client.chat(
                prompt=full_prompt,
                max_tokens=max_tokens,
                call_type="recover",
                exercise_label=exercise.label,
            )
        except Exception as err:
            print(f"[recover]   API call failed: {err}", file=sys.stderr)
            continue

        try:
            new_code = extract_lean_code(response)
        except Exception as err:
            print(f"[recover]   extraction failed: {err}", file=sys.stderr)
            continue

        if not new_code.strip():
            print("[recover]   empty code returned, skipping", file=sys.stderr)
            # Record rejection in history
            history.record(
                attempt=attempt,
                loop="compile",
                lean_code="",
                error_signature=sig,
                rejection_reason="empty_output",
            )
            continue
        new_code = enforce_exact_source_comments(new_code, exercise.raw)
        if (semantic_guard.strip() or semantic_report.strip()) and _looks_like_semantic_weakening(
            exercise.lean_code,
            new_code,
        ):
            print(
                "[recover]   rejected candidate: semantic weakening detected; keep previous code",
                file=sys.stderr,
            )
            history.record(
                attempt=attempt,
                loop="compile",
                lean_code=new_code,
                error_signature=sig,
                rejection_reason="semantic_weakening",
            )
            continue

        if prompt_code_override is not None and merge_block_id.strip():
            # In section-scoped prompting mode, merge the repaired block back
            # into the full-file code kept in exercise.lean_code.
            candidate = new_code.strip()
            extracted = extract_block_by_id(candidate, merge_block_id)
            repaired_block = (extracted[0].strip() if extracted is not None else candidate)
            merged, _ = replace_block_code(exercise.lean_code, merge_block_id, repaired_block, frozen_context=None)
            exercise.lean_code = merged
        else:
            exercise.lean_code = new_code
        exercise.repair_attempts = attempt

        # Re-write and re-validate
        if source_file is not None:
            source_file.write_text(exercise.lean_code + "\n", encoding="utf-8")
            lean_file = source_file
        else:
            lean_file = write_lean_file(exercise, output_dir)
        result = validate_exercise(exercise, lean_file, toolchain_dir, lean_timeout)

        if exercise.is_valid:
            print(f"[recover]   FIXED on attempt {attempt}", file=sys.stderr)
            exercise.status = ExerciseStatus.VALID
            return True

        print_compile_result(result, context=f"[recover] {exercise.label} attempt {attempt}")
        # Count this sig only after an actual compile attempt confirmed it persists.
        # This prevents premature 'repeated error' when previous attempts were
        # rejected (empty code / contract violation / semantic weakening) without
        # ever reaching compile.
        signature_counts[sig] = signature_counts.get(sig, 0) + 1
        print(
            f"[recover]   still {len(exercise.errors)} error(s) after attempt {attempt}",
            file=sys.stderr,
        )

    exercise.status = ExerciseStatus.REPAIR_FAILED
    return False


def recover_all(
    client: APIClient,
    exercises: List[Exercise],
    output_dir: Path,
    *,
    toolchain_dir: str = "lean",
    lean_timeout: int = 120,
    max_tokens: int = 4096,
    max_retries: int = 8,
    mcp_enabled: bool = False,
    mcp_pool_size: int = 1,
    mcp_repo_path: str | None = None,
    mcp_tool_mode: str = "focused",
    mcp_tools: list[str] | None = None,
    semantic_guard_by_label: dict[str, str] | None = None,
    semantic_report_by_label: dict[str, str] | None = None,
    history_by_label: dict[str, RepairHistory] | None = None,
    source_file: Path | None = None,
    prompt_code_by_label: dict[str, str] | None = None,
    merge_block_id_by_label: dict[str, str] | None = None,
    use_common_errors: bool = True,
) -> List[str]:
    """Attempt recovery for every exercise that failed validation.

    When *source_file* is given every recovery attempt writes directly to that
    file instead of creating a temporary file per exercise.

    Returns labels that could not be fixed.
    """
    prompt_text = load_prompt("compiling_fixer")
    still_broken: List[str] = []

    mcp_context_provider: Callable[[Path, Exercise, str], str] | None = None
    if mcp_enabled:
        from ..config.mcp_helper import gather_recovery_context

        project_root = Path(toolchain_dir).resolve()

        def _provider(lean_file: Path, ex: Exercise, tool_mode: str) -> str:
            if not lean_file.exists():
                return ""
            line = None
            col = None
            if ex.errors:
                line = int(ex.errors[0].get("line") or 0)
                col = int(ex.errors[0].get("column") or 0)
            return gather_recovery_context(
                file_path=lean_file.resolve(),
                project_root=project_root,
                lean_path="lean",
                pool_size=mcp_pool_size,
                focus_line=line,
                focus_column=col,
                mcp_repo_path=mcp_repo_path,
                tool_mode=tool_mode or mcp_tool_mode,
                errors=list(ex.errors or []),
                enabled_tools=mcp_tools,
            )

        mcp_context_provider = _provider

    for ex in exercises:
        if ex.is_valid or ex.status == ExerciseStatus.ERROR:
            continue

        entry_history = (history_by_label or {}).get(str(ex.label))
        if entry_history is None:
            entry_history = RepairHistory(keep_recent=5)
            if history_by_label is not None:
                history_by_label[str(ex.label)] = entry_history

        ok = recover_exercise(
            client, ex, output_dir,
            toolchain_dir=toolchain_dir,
            lean_timeout=lean_timeout,
            max_tokens=max_tokens,
            max_retries=max_retries,
            prompt_text=prompt_text,
            mcp_context_provider=mcp_context_provider,
            mcp_tool_mode=mcp_tool_mode,
            mcp_tools=mcp_tools,
            semantic_guard=(semantic_guard_by_label or {}).get(str(ex.label), ""),
            semantic_report=(semantic_report_by_label or {}).get(str(ex.label), ""),
            history=entry_history,
            source_file=source_file,
            prompt_code_override=(prompt_code_by_label or {}).get(str(ex.label)),
            merge_block_id=(merge_block_id_by_label or {}).get(str(ex.label), ""),
            use_common_errors=use_common_errors,
        )
        if not ok:
            still_broken.append(ex.label)

    return still_broken
