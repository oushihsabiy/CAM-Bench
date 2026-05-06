"""Semantic rewriter: update Lean code from semantic review reports."""

from __future__ import annotations

import json
import sys
from typing import Any, Dict, List

from ..config.api_client import APIClient, extract_lean_code
from ..loader import load_prompt
from ..repair_history import RepairHistory

_SUPPORTED_ISSUE_TYPES = {
    "missing_assumption",
    "wrong_boundary_case",
    "task_drift",
}


def _kind_contract(kind: str) -> str:
    k = str(kind or "").strip().lower()
    if k == "defn":
        return "Expected main declaration form: `def`."
    if k == "thm":
        return "Expected main declaration form: `theorem`."
    if k in {"alg", "algo"}:
        return "Expected main declaration form: `structure`."
    return "Expected main declaration form: infer from source semantics."


def _build_runtime_constraints(row: Dict[str, Any]) -> str:
    lines = [
        "Current pipeline constraints (must be preserved after rewrite):",
        "- Primary goal: align declaration semantics with immediate source comments.",
        "- Apply a two-stage gate: first check mathematical equivalence; if equivalent, avoid rewriting.",
        "- Quantifier fidelity hard rule: when source explicitly fixes logical form (existence/for-all/implication/iff), preserve that logical form in rewrites.",
        "- Use `section_context` as auxiliary context for local definitions that appear earlier in the same section.",
        "- Prefer reusing existing section-local definitions from `section_context` rather than introducing new top-level declarations.",
        "- Gradient equivalence policy: treat `fderiv` + basis-vector component forms as valid (e.g. `(fderiv ℝ f x) (Pi.single i (1 : ℝ))` or equivalent `if` basis form), and avoid rewrite oscillation between equivalent forms.",
        "- When `hf : DifferentiableAt ℝ f x` is already present for this gradient pattern, do not add extra slice assumptions unless strictly required by source semantics.",
        "- Hessian equivalence policy: treat iterated `fderiv` + basis-vector component forms as valid Hessian encodings, and avoid rewrite oscillation between equivalent second-derivative forms.",
        "- For Hessian, if explicit second-order differentiability at `x` is already present (e.g. `ContDiffAt ℝ 2 f x` or equivalent), do not add differently shaped equivalent assumptions unless source semantics require more.",
        "- Local-minimizer equivalence policy: keep `IsLocalMin` and explicit ball-inequality local-min forms as equivalent encodings; do not rewrite solely to swap these forms.",
        "- For `def`, body must not be `sorry`.",
        "- For `theorem`, proof may remain `by sorry` in this pipeline.",
        "- Every generated `def` / `theorem` / `structure` must keep an immediate source comment.",
        "- Declarations must start on the next line immediately after source comments; no blank line and no other statement between them.",
        "- Inside each `namespace`, place `open` / `open scoped` / `variable` / `set_option` at namespace beginning.",
        "- Same-namespace reuse rule: when `section_context` already defines a needed symbol (e.g. `def xSeq`), reuse it directly and do not keep/add equivalent local `let` redefinitions in the theorem.",
        "- `variable` is only for parameters/typeclass assumptions; never rewrite concrete definitions into `variable` declarations.",
        "- Source comments must use `/- ... -/` block style (not `-- ...`).",
        "- Source comment text must stay verbatim-exact to JSON `content` (fallback `problem` only if `content` is empty).",
        "- For `kind=thm`, keep exactly one top-level `theorem`; helper terms should preferably use local `let`.",
        "- Only supported issue types in this rewrite pass:",
        "  missing_assumption, wrong_boundary_case, task_drift.",
    ]
    return "\n".join(lines)


def _collect_issue_locations(report: Dict[str, Any]) -> List[str]:
    issues = report.get("issues", [])
    if not isinstance(issues, list):
        return []
    out: List[str] = []
    for issue in issues:
        if not isinstance(issue, dict):
            continue
        loc = str(issue.get("location", "")).strip()
        if not loc:
            continue
        if loc not in out:
            out.append(loc)
    return out


def _filter_supported_issues(report: Dict[str, Any]) -> Dict[str, Any]:
    out = dict(report or {})
    issues = out.get("issues", [])
    if not isinstance(issues, list):
        out["issues"] = []
        out["dominant_issue_types"] = []
        return out
    kept: List[Dict[str, Any]] = []
    for issue in issues:
        if not isinstance(issue, dict):
            continue
        t = str(issue.get("issue_type", "")).strip()
        if t in _SUPPORTED_ISSUE_TYPES:
            kept.append(issue)
    out["issues"] = kept
    dom = out.get("dominant_issue_types", [])
    if isinstance(dom, list):
        out["dominant_issue_types"] = [x for x in dom if str(x) in _SUPPORTED_ISSUE_TYPES]
    else:
        out["dominant_issue_types"] = []
    if kept:
        out["top_priority_fix"] = str(out.get("top_priority_fix", "")).strip()
    return out


def _build_prompt(
    base_prompt: str,
    row: Dict[str, Any],
    report: Dict[str, Any],
    *,
    target_issue: Dict[str, Any] | None = None,
    resolved_issues: List[Dict[str, Any]] | None = None,
    locked_locations: List[str] | None = None,
    strategy_hint: str = "",
    history_block: str = "",
) -> str:
    report = _filter_supported_issues(report)
    row_json = json.dumps(row, ensure_ascii=False, indent=2)
    report_json = json.dumps(report, ensure_ascii=False, indent=2)
    report_locations = _collect_issue_locations(report)
    if target_issue and isinstance(target_issue, dict):
        target_locations = [
            str(target_issue.get("location", "")).strip()
        ]
        target_locations = [x for x in target_locations if x]
    else:
        target_locations = report_locations
    if target_locations:
        location_block = (
            "Allowed edit locations (hard constraint):\n"
            + "\n".join(f"- {x}" for x in target_locations)
            + "\n"
        )
    else:
        location_block = (
            "Allowed edit locations: (none explicitly provided)\n"
            "Keep edits minimal and focused on report-indicated problems.\n"
        )
    target_issue_block = ""
    if target_issue and isinstance(target_issue, dict):
        target_issue_block = (
            "Target issue for this rewrite (only this issue may be modified now):\n"
            f"{json.dumps(target_issue, ensure_ascii=False, indent=2)}\n\n"
        )
    resolved_block = ""
    if resolved_issues:
        resolved_block = (
            "Already resolved issues (must stay fixed):\n"
            f"{json.dumps(resolved_issues, ensure_ascii=False, indent=2)}\n\n"
        )
    lock_block = ""
    if locked_locations:
        lock_block = (
            "Locked locations (DO NOT MODIFY):\n"
            + "\n".join(f"- {x}" for x in locked_locations)
            + "\n\n"
        )
    strategy_block = ""
    if strategy_hint.strip():
        strategy_block = f"Strategy hint:\n{strategy_hint.strip()}\n\n"
    history_extra = ""
    if history_block.strip():
        history_extra = f"{history_block.strip()}\n\n"
    constraints_block = _build_runtime_constraints(row) + "\n\n"
    return (
        f"{base_prompt}\n\n"
        f"{strategy_block}"
        f"{history_extra}"
        f"{constraints_block}"
        f"{target_issue_block}"
        f"{resolved_block}"
        f"{lock_block}"
        f"{location_block}\n"
        f"Input record:\n{row_json}\n\n"
        f"Semantic report:\n{report_json}\n\n"
        "Output ONLY the corrected Lean file content."
    )


def rewrite_from_report(
    client: APIClient,
    row: Dict[str, Any],
    report: Dict[str, Any],
    *,
    max_tokens: int = 4096,
    max_attempts: int = 2,
    prompt_text: str | None = None,
    target_issue: Dict[str, Any] | None = None,
    resolved_issues: List[Dict[str, Any]] | None = None,
    locked_locations: List[str] | None = None,
    strategy_hint: str = "",
    history: RepairHistory | None = None,
) -> str:
    """Return rewritten Lean code from a semantic report.

    Returns an empty string if no usable rewrite is produced.
    """
    if prompt_text is None:
        prompt_text = load_prompt("semantic_rewrite")

    label = str(row.get("label", ""))
    last_error = ""
    history_block = history.format_for_prompt() if history else ""
    for attempt in range(1, max_attempts + 1):
        try:
            response = client.chat(
                prompt=_build_prompt(
                    prompt_text,
                    row,
                    report,
                    target_issue=target_issue,
                    resolved_issues=resolved_issues,
                    locked_locations=locked_locations,
                    strategy_hint=strategy_hint,
                    history_block=history_block,
                ),
                max_tokens=max_tokens,
                call_type="semantic_rewrite",
                exercise_label=label,
            )
            code = extract_lean_code(response)
            if not code.strip():
                raise ValueError("Empty Lean code returned")
            return code
        except Exception as err:
            last_error = str(err)
            print(
                f"[semantic_rewrite] attempt {attempt}/{max_attempts} failed for {label}: {err}",
                file=sys.stderr,
            )
    print(f"[semantic_rewrite] giving up for {label}: {last_error}", file=sys.stderr)
    return ""
