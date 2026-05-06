#!/usr/bin/env python3
"""Aggressively add boundary-condition assumptions to Lean exercise namespaces.

The script reads combined Lean files, treats each top-level namespace as one
exercise, asks an LLM to harden the whole namespace against corner cases, writes
the result to a sibling output tree, then optionally invokes the existing
compile checker and compile repair loop on the output file.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


PROJECT_ROOT = Path(__file__).resolve().parents[2]


def _reexec_with_local_venv() -> None:
    if os.environ.get("JSON2LEAN_NO_AUTO_VENV") == "1":
        return
    venv_dir = PROJECT_ROOT / ".venv"
    venv_python = venv_dir / "bin" / "python"
    if not venv_python.exists():
        return
    try:
        if Path(sys.prefix).resolve() == venv_dir.resolve():
            return
    except OSError:
        return
    os.execv(str(venv_python), [str(venv_python), *sys.argv])


if __name__ == "__main__":
    _reexec_with_local_venv()

SRC_ROOT = PROJECT_ROOT / "src"
if str(SRC_ROOT) not in sys.path:
    sys.path.insert(0, str(SRC_ROOT))
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from json2lean.compile.compiling_checker import compile_lean_file, validate_exercise
from json2lean.compile.compiling_fixer import recover_all
from json2lean.config.api_client import APIClient, extract_lean_code
from json2lean.loader import load_config, load_prompt, load_settings
from json2lean.models import Exercise


DEFAULT_INPUT_DIR = PROJECT_ROOT / "lean" / "Leanproject"
DEFAULT_OUTPUT_DIR = PROJECT_ROOT / "lean" / "Leanproject_corner-fix"
DEFAULT_LOG_DIR = PROJECT_ROOT / "logs" / "corner_fix"


_NS_OPEN_RE = re.compile(r"^\s*namespace\s+(\S+)\s*$")
_NS_CLOSE_RE = re.compile(r"^\s*end(?:\s+(\S+))?\s*$")
_BLOCK_COMMENT_RE = re.compile(r"/-\s*\[BLOCK\b.*?-\s*/", re.DOTALL)
_SOURCE_COMMENT_RE = re.compile(r"/-.*?-/", re.DOTALL)
_DECL_RE = re.compile(
    r"(?m)^[ \t]*(?:private\s+|protected\s+)?"
    r"(def|theorem|lemma|example|instance|structure|class|inductive|axiom)\s+([^\s(:]+)"
)


@dataclass(frozen=True)
class NamespaceSpan:
    name: str
    start: int
    end: int
    text: str


class SemanticReviewFailure(RuntimeError):
    def __init__(self, message: str, report: dict[str, Any] | None = None) -> None:
        super().__init__(message)
        self.report = report or {}


def parse_top_level_namespaces(text: str) -> list[NamespaceSpan]:
    """Return top-level ``namespace ... end ...`` spans in file order."""
    spans: list[NamespaceSpan] = []
    stack: list[str] = []
    ns_name = ""
    ns_start = -1
    pos = 0
    for line in text.splitlines(keepends=True):
        stripped = line.rstrip("\r\n")
        open_m = _NS_OPEN_RE.match(stripped)
        close_m = _NS_CLOSE_RE.match(stripped)

        if open_m:
            if not stack:
                ns_name = open_m.group(1)
                ns_start = pos
            stack.append(open_m.group(1))
        elif close_m and stack:
            close_name = close_m.group(1)
            if close_name and close_name in stack:
                while stack:
                    popped = stack.pop()
                    if popped == close_name:
                        break
            else:
                stack.pop()
            if not stack and ns_start >= 0:
                end = pos + len(line)
                spans.append(NamespaceSpan(ns_name, ns_start, end, text[ns_start:end]))
                ns_name = ""
                ns_start = -1

        pos += len(line)
    return spans


def extract_decl_names(text: str) -> set[str]:
    return {m.group(2) for m in _DECL_RE.finditer(text)}


def extract_block_comments(text: str) -> list[str]:
    return [m.group(0) for m in _BLOCK_COMMENT_RE.finditer(text)]


def extract_source_comments(text: str) -> list[str]:
    return [m.group(0) for m in _SOURCE_COMMENT_RE.finditer(text)]


def has_degenerate_theorem_goal(original: str, candidate: str) -> bool:
    """Reject new trivial theorem/lemma goals not present in the original."""
    if re.search(r"(?ms)^[ \t]*(?:theorem|lemma)\s+[A-Za-z0-9_'.]+.*?:\s*(?:True|False)\s*:=", original):
        return False
    return bool(
        re.search(r"(?ms)^[ \t]*(?:theorem|lemma)\s+[A-Za-z0-9_'.]+.*?:\s*(?:True|False)\s*:=", candidate)
    )


def validate_namespace_candidate(original: str, candidate: str, name: str) -> tuple[bool, str]:
    """Check that LLM output still represents the same namespace exercise."""
    stripped = candidate.strip()
    candidate_for_parse = stripped + ("\n" if not stripped.endswith("\n") else "")
    spans = parse_top_level_namespaces(candidate_for_parse)
    if len(spans) != 1:
        return False, f"expected exactly one namespace, got {len(spans)}"
    if spans[0].name != name:
        return False, f"namespace renamed from {name!r} to {spans[0].name!r}"
    if candidate_for_parse[:spans[0].start].strip() or candidate_for_parse[spans[0].end:].strip():
        return False, "candidate contains text outside the namespace"

    for comment in extract_source_comments(original):
        if comment not in candidate:
            return False, "original source comment was modified or removed"

    missing = extract_decl_names(original) - extract_decl_names(candidate)
    if missing:
        return False, f"declarations removed: {', '.join(sorted(missing)[:8])}"

    if has_degenerate_theorem_goal(original, candidate):
        return False, "candidate introduced a trivial True/False theorem goal"

    return True, ""


def mandatory_boundary_issues(original: str, candidate: str) -> list[str]:
    """Return missing aggressive boundary hardening signals.

    This is intentionally heuristic. It does not try to prove the statement is
    mathematically complete; it catches the common case where the LLM simply
    echoes the original namespace without adding the boundary assumptions that
    the prompt requires.
    """
    issues: list[str] = []

    if re.search(r"\bFin\s+n\b", original) and not re.search(r"0\s*<\s*n", candidate):
        issues.append("missing explicit dimension positivity assumption for n, e.g. (hn : 0 < n)")
    if re.search(r"\bFin\s+m\b", original) and not re.search(r"0\s*<\s*m", candidate):
        issues.append("missing explicit dimension positivity assumption for m, e.g. (hm : 0 < m)")
    if re.search(r"\bFin\s+r\b", original) and not re.search(r"0\s*<\s*r", candidate):
        issues.append("missing explicit dimension positivity assumption for r, e.g. (hr : 0 < r)")

    matrix_vars = sorted(set(re.findall(r"\(([A-Za-z][A-Za-z0-9_']*)\s*:\s*Matrix\b", original)))
    for var in matrix_vars:
        if not re.search(rf"\b{re.escape(var)}\s*≠\s*0\b", candidate):
            issues.append(f"missing nonzero matrix assumption for {var}, e.g. (h{var}_ne_zero : {var} ≠ 0)")

    optimization_markers = (
        "argmin",
        "argmax",
        "sSup",
        "sInf",
        "optimalValue",
        "feasibleSet",
        "is_feasible",
        "primalFeasible",
        "dualFeasible",
        "inverseOptimalitySet",
    )
    if any(marker in original for marker in optimization_markers):
        if not re.search(r"\bNonempty\b|\.Nonempty\b|Set\.Nonempty\b|nonempty", candidate):
            issues.append("missing explicit feasible/domain/optimality set nonempty assumptions using Nonempty")
        if ("sSup" in original or "sInf" in original or "optimalValue" in original) and not re.search(
            r"finite|Finite|attain|Attain|attained|bounded|Bounded|\(.*:\s*EReal\)", candidate
        ):
            issues.append("missing finite/boundedness/attainment assumptions for sSup/sInf/optimal values")

    return issues


def parse_json_object(text: str) -> dict[str, Any]:
    stripped = text.strip()
    if stripped.startswith("```"):
        stripped = re.sub(r"^```(?:json)?\s*", "", stripped)
        stripped = re.sub(r"\s*```$", "", stripped).strip()
    try:
        obj = json.loads(stripped)
    except json.JSONDecodeError:
        start = stripped.find("{")
        end = stripped.rfind("}")
        if start < 0 or end <= start:
            raise
        obj = json.loads(stripped[start : end + 1])
    if not isinstance(obj, dict):
        raise ValueError("review response is not a JSON object")
    return obj


def build_prompt(prompt_template: str, *, file_path: str, namespace_name: str, namespace_text: str) -> str:
    return (
        f"{prompt_template.strip()}\n\n"
        f"## File\n{file_path}\n\n"
        f"## Namespace\n{namespace_name}\n\n"
        "## Input Lean namespace\n"
        f"{namespace_text.strip()}\n"
    )


def build_semantic_review_prompt(
    prompt_template: str,
    *,
    file_path: str,
    namespace_name: str,
    original_namespace: str,
    fixed_namespace: str,
) -> str:
    return (
        f"{prompt_template.strip()}\n\n"
        f"## File\n{file_path}\n\n"
        f"## Namespace\n{namespace_name}\n\n"
        "## ORIGINAL Lean namespace\n"
        "```lean\n"
        f"{original_namespace.strip()}\n"
        "```\n\n"
        "## FIXED Lean namespace\n"
        "```lean\n"
        f"{fixed_namespace.strip()}\n"
        "```\n"
    )


def semantic_review_namespace(
    *,
    client: APIClient,
    review_prompt_template: str,
    file_rel_path: str,
    namespace: NamespaceSpan,
    candidate: str,
    max_tokens: int,
    log_path: Path,
) -> tuple[bool, dict[str, Any]]:
    prompt = build_semantic_review_prompt(
        review_prompt_template,
        file_path=file_rel_path,
        namespace_name=namespace.name,
        original_namespace=namespace.text,
        fixed_namespace=candidate,
    )
    try:
        response = client.chat(
            prompt=prompt,
            max_tokens=max_tokens,
            call_type="corner_fix_semantic_review",
            exercise_label=f"{file_rel_path}:{namespace.name}:semantic_review",
        )
        report = parse_json_object(response)
    except Exception as err:
        report = {
            "status": "fail",
            "summary": f"semantic review failed to return valid JSON: {err}",
            "error": str(err),
        }
        append_jsonl(log_path, {
            "event": "namespace_semantic_review_failed",
            "time": now_iso(),
            "rel_path": file_rel_path,
            "namespace": namespace.name,
            "reason": "review_error",
            "report": report,
        })
        return False, report

    status = str(report.get("status", "")).strip().lower()
    ok = status == "pass"
    append_jsonl(log_path, {
        "event": "namespace_semantic_review_completed" if ok else "namespace_semantic_review_failed",
        "time": now_iso(),
        "rel_path": file_rel_path,
        "namespace": namespace.name,
        "status": status,
        "report": report,
    })
    return ok, report


def load_include_file_list(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    stripped = text.strip()
    if not stripped:
        return []
    try:
        obj = json.loads(stripped)
        if isinstance(obj, list):
            return [str(x).strip() for x in obj if str(x).strip()]
        if isinstance(obj, dict) and isinstance(obj.get("files"), list):
            return [str(x).strip() for x in obj["files"] if str(x).strip()]
    except json.JSONDecodeError:
        pass
    out: list[str] = []
    for raw in text.splitlines():
        line = raw.strip()
        if line and not line.startswith("#"):
            out.append(line)
    return out


def resolve_single_lean_file(input_dir: Path, item: str, all_files: list[Path]) -> Path:
    by_name: dict[str, list[Path]] = {}
    by_rel: dict[str, Path] = {}
    for p in all_files:
        rel = p.relative_to(input_dir).as_posix()
        by_rel[rel] = p
        by_rel[str(Path(rel))] = p
        by_name.setdefault(p.name, []).append(p)

    raw = Path(item)
    if raw.is_absolute() and raw.exists():
        return raw.resolve()
    norm = item.replace("\\", "/")
    if norm in by_rel:
        return by_rel[norm]
    candidate = input_dir / item
    if candidate.exists():
        return candidate.resolve()
    matches = by_name.get(Path(item).name, [])
    if len(matches) == 1:
        return matches[0]
    if len(matches) > 1:
        raise ValueError(f"Ambiguous include entry {item!r}; use a relative path")
    raise FileNotFoundError(f"Included Lean file not found: {item}")


def resolve_lean_files(input_dir: Path, include_file: Path | None = None) -> list[Path]:
    all_files = sorted(p for p in input_dir.rglob("*.lean") if p.is_file())
    if include_file is None:
        return all_files

    include_text = str(include_file)
    if include_file.suffix == ".lean" or include_text.replace("\\", "/").endswith(".lean"):
        return [resolve_single_lean_file(input_dir, include_text, all_files)]

    requested = load_include_file_list(include_file)
    resolved = [resolve_single_lean_file(input_dir, item, all_files) for item in requested]
    return sorted(dict.fromkeys(resolved))


def append_jsonl(path: Path, record: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as f:
        f.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")


def load_completed_files(log_path: Path) -> set[str]:
    completed: set[str] = set()
    if not log_path.exists():
        return completed
    for line in log_path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        try:
            rec = json.loads(line)
        except json.JSONDecodeError:
            continue
        if rec.get("event") == "file_completed" and rec.get("status") == "completed":
            rel_path = rec.get("rel_path")
            if isinstance(rel_path, str) and rel_path:
                completed.add(rel_path)
    return completed


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def error_summary(errors: list[dict[str, Any]], limit: int = 5) -> list[dict[str, Any]]:
    out = []
    for err in errors[:limit]:
        out.append({
            "line": err.get("line"),
            "column": err.get("column"),
            "message": str(err.get("message", ""))[:600],
        })
    return out


def harden_namespace(
    *,
    client: APIClient,
    prompt_template: str,
    semantic_review_template: str,
    file_rel_path: str,
    namespace: NamespaceSpan,
    max_tokens: int,
    log_path: Path,
) -> str:
    base_prompt = build_prompt(
        prompt_template,
        file_path=file_rel_path,
        namespace_name=namespace.name,
        namespace_text=namespace.text,
    )
    rejection_notes: list[str] = []
    max_attempts = 3
    last_candidate = ""
    for attempt in range(1, max_attempts + 1):
        prompt = base_prompt
        if rejection_notes:
            prompt += (
                "\n\n## Previous output rejected\n"
                "Your previous output was rejected because it did not satisfy the mandatory "
                "boundary-condition checklist. Produce the full namespace again and fix ALL "
                "of these concrete missing items:\n"
            )
            for note in rejection_notes:
                prompt += f"- {note}\n"
            prompt += (
                "\nDo not explain. Do not output markdown. Output only the complete Lean namespace.\n"
            )
        try:
            response = client.chat(
                prompt=prompt,
                max_tokens=max_tokens,
                call_type="corner_fix",
                exercise_label=f"{file_rel_path}:{namespace.name}:attempt{attempt}",
            )
            candidate = extract_lean_code(response)
            last_candidate = candidate
        except Exception as err:
            append_jsonl(log_path, {
                "event": "namespace_failed",
                "time": now_iso(),
                "rel_path": file_rel_path,
                "namespace": namespace.name,
                "attempt": attempt,
                "reason": "llm_error",
                "error": str(err),
            })
            raise

        ok, reason = validate_namespace_candidate(namespace.text, candidate, namespace.name)
        if not ok:
            rejection_notes = [reason]
            append_jsonl(log_path, {
                "event": "namespace_rejected",
                "time": now_iso(),
                "rel_path": file_rel_path,
                "namespace": namespace.name,
                "attempt": attempt,
                "reason": reason,
            })
            continue

        issues = mandatory_boundary_issues(namespace.text, candidate)
        if issues:
            rejection_notes = issues
            append_jsonl(log_path, {
                "event": "namespace_rejected",
                "time": now_iso(),
                "rel_path": file_rel_path,
                "namespace": namespace.name,
                "attempt": attempt,
                "reason": "mandatory_boundary_issues",
                "issues": issues,
            })
            continue

        review_ok, review_report = semantic_review_namespace(
            client=client,
            review_prompt_template=semantic_review_template,
            file_rel_path=file_rel_path,
            namespace=namespace,
            candidate=candidate,
            max_tokens=max_tokens,
            log_path=log_path,
        )
        if not review_ok:
            raise SemanticReviewFailure(
                f"semantic review failed for {file_rel_path}:{namespace.name}",
                review_report,
            )

        changed = candidate.strip() != namespace.text.strip()
        append_jsonl(log_path, {
            "event": "namespace_completed",
            "time": now_iso(),
            "rel_path": file_rel_path,
            "namespace": namespace.name,
            "attempt": attempt,
            "changed": changed,
        })
        return candidate.strip() + "\n"

    report = {
        "status": "fail",
        "summary": "mandatory boundary checklist was still unsatisfied after all attempts",
        "missing_original_conditions": [],
        "task_drift": [],
        "weakened_or_changed_conditions": [],
        "comment_preservation_issues": [],
        "mandatory_boundary_issues": rejection_notes,
    }
    append_jsonl(log_path, {
        "event": "namespace_failed",
        "time": now_iso(),
        "rel_path": file_rel_path,
        "namespace": namespace.name,
        "reason": "mandatory_boundary_issues_exhausted",
        "issues": rejection_notes,
        "last_candidate_changed": bool(last_candidate.strip() and last_candidate.strip() != namespace.text.strip()),
    })
    raise SemanticReviewFailure(
        f"mandatory boundary issues exhausted for {file_rel_path}:{namespace.name}",
        report,
    )


def rewrite_file_namespaces(
    *,
    client: APIClient,
    prompt_template: str,
    semantic_review_template: str,
    input_path: Path,
    output_path: Path,
    input_dir: Path,
    max_tokens: int,
    log_path: Path,
) -> tuple[str, int]:
    original = input_path.read_text(encoding="utf-8")
    spans = parse_top_level_namespaces(original)
    rel_path = input_path.relative_to(input_dir).as_posix()
    if not spans:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(original, encoding="utf-8")
        append_jsonl(log_path, {
            "event": "file_no_namespaces",
            "time": now_iso(),
            "rel_path": rel_path,
        })
        return original, 0

    replacements: list[tuple[int, int, str]] = []
    for span in spans:
        new_text = harden_namespace(
            client=client,
            prompt_template=prompt_template,
            semantic_review_template=semantic_review_template,
            file_rel_path=rel_path,
            namespace=span,
            max_tokens=max_tokens,
            log_path=log_path,
        )
        replacements.append((span.start, span.end, new_text))

    rewritten = original
    for start, end, new_text in sorted(replacements, reverse=True):
        rewritten = rewritten[:start] + new_text + rewritten[end:]

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(rewritten, encoding="utf-8")
    return rewritten, len(spans)


def write_failure_artifacts(
    *,
    input_path: Path,
    output_path: Path,
    failure_root: Path,
    rel_path: str,
    status: str,
    reason: str,
    report: dict[str, Any] | None = None,
) -> Path:
    failure_path = failure_root / rel_path
    failure_path.parent.mkdir(parents=True, exist_ok=True)
    failure_path.write_text(input_path.read_text(encoding="utf-8"), encoding="utf-8")

    candidate_path = None
    if output_path.exists():
        candidate_path = failure_path.with_suffix(failure_path.suffix + ".candidate")
        candidate_path.write_text(output_path.read_text(encoding="utf-8"), encoding="utf-8")

    meta_path = failure_path.with_suffix(failure_path.suffix + ".failure.json")
    meta = {
        "time": now_iso(),
        "rel_path": rel_path,
        "status": status,
        "reason": reason,
        "source_path": str(input_path),
        "failure_path": str(failure_path),
        "candidate_path": str(candidate_path) if candidate_path else None,
        "report": report or {},
    }
    meta_path.write_text(json.dumps(meta, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return failure_path


def semantic_review_file(
    *,
    client: APIClient,
    review_prompt_template: str,
    original_text: str,
    fixed_text: str,
    rel_path: str,
    max_tokens: int,
    log_path: Path,
) -> None:
    original_spans = parse_top_level_namespaces(original_text)
    fixed_spans = parse_top_level_namespaces(fixed_text)
    fixed_by_name = {span.name: span for span in fixed_spans}
    for original_span in original_spans:
        fixed_span = fixed_by_name.get(original_span.name)
        if fixed_span is None:
            report = {
                "status": "fail",
                "summary": f"fixed file is missing namespace {original_span.name}",
                "missing_original_conditions": [],
                "task_drift": [f"namespace {original_span.name} was removed"],
                "weakened_or_changed_conditions": [],
                "comment_preservation_issues": [],
            }
            append_jsonl(log_path, {
                "event": "namespace_semantic_review_failed",
                "time": now_iso(),
                "rel_path": rel_path,
                "namespace": original_span.name,
                "reason": "namespace_missing_after_compile",
                "report": report,
            })
            raise SemanticReviewFailure(f"final semantic review failed for {rel_path}:{original_span.name}", report)
        ok, report = semantic_review_namespace(
            client=client,
            review_prompt_template=review_prompt_template,
            file_rel_path=rel_path,
            namespace=original_span,
            candidate=fixed_span.text,
            max_tokens=max_tokens,
            log_path=log_path,
        )
        if not ok:
            raise SemanticReviewFailure(f"final semantic review failed for {rel_path}:{original_span.name}", report)


def compile_and_repair_file(
    *,
    client: APIClient,
    output_path: Path,
    rel_path: str,
    toolchain_dir: Path,
    lean_timeout: int,
    max_tokens: int,
    compile_fix_retries: int,
    settings: dict[str, Any],
    log_path: Path,
) -> bool:
    result = compile_lean_file(output_path, toolchain_dir=toolchain_dir, timeout=lean_timeout)
    append_jsonl(log_path, {
        "event": "compile_checked",
        "time": now_iso(),
        "rel_path": rel_path,
        "returncode": result.returncode,
        "errors": error_summary(result.errors),
    })
    if result.returncode == 0 and not result.errors:
        return True
    if compile_fix_retries <= 0:
        return False

    label = output_path.stem
    ex = Exercise(
        raw={"source_idx": rel_path, "problem": "corner-fixed combined Lean file"},
        index=0,
        label=label,
        problem="corner-fixed combined Lean file",
    )
    ex.lean_code = output_path.read_text(encoding="utf-8")
    validate_exercise(ex, output_path, toolchain_dir=str(toolchain_dir), timeout=lean_timeout)

    recovery = settings.get("recovery", {}) if isinstance(settings.get("recovery", {}), dict) else {}
    semantic_guard = (
        "This file was produced by aggressive boundary-condition hardening. "
        "During compile repair, do not remove, weaken, or trivialize added boundary assumptions. "
        "Only repair Lean syntax/type errors while preserving the hardened statement intent."
    )
    broken = recover_all(
        client,
        [ex],
        output_path.parent,
        toolchain_dir=str(toolchain_dir),
        lean_timeout=lean_timeout,
        max_tokens=max_tokens,
        max_retries=compile_fix_retries,
        mcp_enabled=bool(recovery.get("mcp_enabled", False)),
        mcp_pool_size=int(recovery.get("mcp_pool_size", 1) or 1),
        mcp_repo_path=recovery.get("mcp_repo_path"),
        mcp_tool_mode=str(recovery.get("mcp_tool_mode", "focused")),
        mcp_tools=recovery.get("mcp_tools"),
        semantic_guard_by_label={label: semantic_guard},
        source_file=output_path,
        use_common_errors=bool(recovery.get("use_common_errors", True)),
    )
    final_ok = not broken and ex.is_valid
    append_jsonl(log_path, {
        "event": "compile_repair_completed",
        "time": now_iso(),
        "rel_path": rel_path,
        "success": final_ok,
        "repair_attempts": ex.repair_attempts,
        "errors": error_summary(ex.errors),
    })
    return final_ok


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Aggressively add boundary-condition assumptions to Lean namespaces."
    )
    parser.add_argument("--input-dir", type=Path, default=DEFAULT_INPUT_DIR)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--config", type=Path, default=None)
    parser.add_argument("--settings", type=Path, default=PROJECT_ROOT / "settings.json")
    parser.add_argument("--include-file", type=Path, default=None, help="Single .lean file/name/relative path, or a list file containing Lean files.")
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--max-tokens", type=int, default=8192)
    parser.add_argument("--compile-fix-retries", type=int, default=None)
    parser.add_argument("--force", action="store_true")
    parser.add_argument("--log-dir", type=Path, default=DEFAULT_LOG_DIR)
    parser.add_argument(
        "--skip-compile-fix",
        action="store_true",
        help="Write LLM-hardened files without running compile checker/fixer.",
    )
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    args = build_arg_parser().parse_args(list(argv) if argv is not None else None)
    input_dir = args.input_dir.resolve()
    output_dir = args.output_dir.resolve()
    failure_root = output_dir / "failure"
    log_dir = args.log_dir.resolve()
    log_path = log_dir / "corner_fix.jsonl"

    cfg = load_config(args.config)
    settings = load_settings(args.settings)
    recovery = settings.get("recovery", {}) if isinstance(settings.get("recovery", {}), dict) else {}
    lean_settings = settings.get("lean", {}) if isinstance(settings.get("lean", {}), dict) else {}
    compile_fix_retries = (
        int(args.compile_fix_retries)
        if args.compile_fix_retries is not None
        else int(recovery.get("max_retries", cfg.recovery_max_retries) or 8)
    )
    lean_timeout = int(lean_settings.get("timeout_seconds", cfg.lean_timeout_seconds) or 120)
    toolchain_dir = Path(lean_settings.get("toolchain_dir", cfg.lean_toolchain_dir) or "lean")
    if not toolchain_dir.is_absolute():
        toolchain_dir = PROJECT_ROOT / toolchain_dir

    client = APIClient(
        api_key=cfg.api_key,
        base_url=cfg.base_url,
        model=cfg.model,
        timeout=cfg.timeout_seconds,
        token_log_dir=log_dir,
        realtime_token_log=True,
    )
    prompt_template = load_prompt("corner_fix")
    semantic_review_template = load_prompt("corner_fix_semantic_review")

    files = resolve_lean_files(input_dir, args.include_file)
    if args.limit is not None:
        files = files[: max(0, int(args.limit))]
    completed = load_completed_files(log_path)

    print(f"[corner_fix] input: {input_dir}", file=sys.stderr)
    print(f"[corner_fix] output: {output_dir}", file=sys.stderr)
    print(f"[corner_fix] files: {len(files)}", file=sys.stderr)

    ok_count = 0
    skipped_count = 0
    failed_count = 0
    for idx, input_path in enumerate(files, start=1):
        rel_path = input_path.relative_to(input_dir).as_posix()
        output_path = output_dir / rel_path
        if not args.force and output_path.exists() and rel_path in completed:
            skipped_count += 1
            print(f"[corner_fix] skip completed {idx}/{len(files)}: {rel_path}", file=sys.stderr)
            continue

        print(f"[corner_fix] process {idx}/{len(files)}: {rel_path}", file=sys.stderr)
        try:
            _, ns_count = rewrite_file_namespaces(
                client=client,
                prompt_template=prompt_template,
                semantic_review_template=semantic_review_template,
                input_path=input_path,
                output_path=output_path,
                input_dir=input_dir,
                max_tokens=args.max_tokens,
                log_path=log_path,
            )
            compiled = True
            if not args.skip_compile_fix:
                compiled = compile_and_repair_file(
                    client=client,
                    output_path=output_path,
                    rel_path=rel_path,
                    toolchain_dir=toolchain_dir,
                    lean_timeout=lean_timeout,
                    max_tokens=int(recovery.get("max_tokens", cfg.recovery_max_tokens) or cfg.recovery_max_tokens),
                    compile_fix_retries=compile_fix_retries,
                    settings=settings,
                    log_path=log_path,
                )
            if compiled:
                semantic_review_file(
                    client=client,
                    review_prompt_template=semantic_review_template,
                    original_text=input_path.read_text(encoding="utf-8"),
                    fixed_text=output_path.read_text(encoding="utf-8"),
                    rel_path=rel_path,
                    max_tokens=args.max_tokens,
                    log_path=log_path,
                )
            status = "completed" if compiled else "compile_failed"
            append_jsonl(log_path, {
                "event": "file_completed",
                "time": now_iso(),
                "rel_path": rel_path,
                "status": status,
                "namespace_count": ns_count,
                "output_path": str(output_path),
            })
            if compiled:
                ok_count += 1
            else:
                failed_count += 1
        except SemanticReviewFailure as err:
            failed_count += 1
            failure_path = write_failure_artifacts(
                input_path=input_path,
                output_path=output_path,
                failure_root=failure_root,
                rel_path=rel_path,
                status="semantic_review_failed",
                reason=str(err),
                report=err.report,
            )
            append_jsonl(log_path, {
                "event": "file_completed",
                "time": now_iso(),
                "rel_path": rel_path,
                "status": "semantic_review_failed",
                "output_path": str(output_path),
                "failure_path": str(failure_path),
                "error": str(err),
                "review_report": err.report,
            })
            print(f"[corner_fix] SEMANTIC FAIL {rel_path}: {err}", file=sys.stderr)
        except Exception as err:
            failed_count += 1
            failure_path = write_failure_artifacts(
                input_path=input_path,
                output_path=output_path,
                failure_root=failure_root,
                rel_path=rel_path,
                status="failed",
                reason=str(err),
                report={"error": str(err)},
            )
            append_jsonl(log_path, {
                "event": "file_failed",
                "time": now_iso(),
                "rel_path": rel_path,
                "failure_path": str(failure_path),
                "error": str(err),
            })
            print(f"[corner_fix] ERROR {rel_path}: {err}", file=sys.stderr)

    print(
        f"[corner_fix] done: ok={ok_count}, skipped={skipped_count}, failed={failed_count}",
        file=sys.stderr,
    )
    return 0 if failed_count == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
