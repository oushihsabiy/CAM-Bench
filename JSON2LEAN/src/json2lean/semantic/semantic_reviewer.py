"""Semantic reviewer for compiled Lean exercise files."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Any, Dict, List

from ..config.api_client import APIClient, extract_json_value
from ..loader import load_prompt

_TRUTH_VALUES = {"true", "false", "unknown", "not_applicable"}


def _to_bool(v: Any) -> bool | None:
    if isinstance(v, bool):
        return v
    if isinstance(v, (int, float)):
        return bool(v)
    if isinstance(v, str):
        s = v.strip().lower()
        if s in {"true", "yes", "1"}:
            return True
        if s in {"false", "no", "0"}:
            return False
    return None


def _apply_two_stage_gate(report: Dict[str, Any]) -> Dict[str, Any]:
    out = dict(report or {})
    eq_flag = _to_bool(out.get("math_equivalent", None))
    if eq_flag is None:
        eq_flag = _to_bool(out.get("semantic_equivalent", None))
    if eq_flag is not True and _looks_like_shape_only_non_equivalence(out):
        eq_flag = True
    if eq_flag is True:
        out["overall_status"] = "usable"
        out["issues"] = []
        out["dominant_issue_types"] = []
        out["top_priority_fix"] = "none"
    return out


def _default_truth_judgement(row: Dict[str, Any], eq_flag: bool | None) -> str:
    raw = row.get("original_raw", {})
    kind = str(raw.get("kind", "")).strip().lower() if isinstance(raw, dict) else ""
    if kind == "thm":
        return "true" if eq_flag is True else "unknown"
    if kind in {"defn", "alg", "algo"}:
        return "not_applicable"
    return "unknown"


def _normalize_truth_judgement(report: Dict[str, Any], row: Dict[str, Any]) -> Dict[str, Any]:
    out = dict(report or {})
    eq_flag = _to_bool(out.get("math_equivalent", None))
    if eq_flag is None:
        eq_flag = _to_bool(out.get("semantic_equivalent", None))

    raw_truth = out.get(
        "truth_judgement",
        out.get("statement_truth", out.get("proposition_truth", "")),
    )
    truth = str(raw_truth or "").strip().lower()
    alias = {
        "na": "not_applicable",
        "n/a": "not_applicable",
        "not applicable": "not_applicable",
        "not-applicable": "not_applicable",
    }
    truth = alias.get(truth, truth)
    if truth not in _TRUTH_VALUES:
        truth = _default_truth_judgement(row, eq_flag)

    raw_counterexample = out.get("counterexample", "")
    if isinstance(raw_counterexample, (dict, list)):
        counterexample = json.dumps(raw_counterexample, ensure_ascii=False)
    else:
        counterexample = str(raw_counterexample or "").strip()

    if truth != "false":
        counterexample = ""
    else:
        if not counterexample:
            counterexample = "(missing counterexample from reviewer)"
        out["overall_status"] = "not_usable_yet"
        out["math_equivalent"] = False
        issues = out.get("issues", [])
        if not isinstance(issues, list):
            issues = []
        if not issues:
            issues = [
                {
                    "severity": "P0",
                    "issue_type": "task_drift",
                    "location": "current declaration",
                    "reason": "Statement judged false under the source interpretation.",
                    "suggested_fix": (
                        "Revise quantifiers/assumptions/boundary conditions so the "
                        "provided counterexample no longer applies."
                    ),
                }
            ]
        out["issues"] = issues
        dom = out.get("dominant_issue_types", [])
        if not isinstance(dom, list):
            dom = []
        if "task_drift" not in dom:
            dom = ["task_drift"] + [x for x in dom if x != "task_drift"]
        out["dominant_issue_types"] = dom
        if not str(out.get("top_priority_fix", "")).strip():
            out["top_priority_fix"] = "Fix the false statement using the counterexample."

    out["truth_judgement"] = truth
    out["counterexample"] = counterexample
    return out


def _looks_like_shape_only_non_equivalence(report: Dict[str, Any]) -> bool:
    issues = report.get("issues", [])
    if not isinstance(issues, list) or not issues:
        return False
    for it in issues:
        if not isinstance(it, dict):
            return False
        sev = str(it.get("severity", "")).strip().upper()
        typ = str(it.get("issue_type", "")).strip().lower()
        if sev == "P0":
            return False
        if typ not in {"task_drift", "missing_assumption"}:
            return False

    blobs = [
        str(report.get("top_priority_fix", "")),
        str(report.get("summary", "")),
    ]
    for it in issues:
        blobs.append(str(it.get("reason", "")))
        blobs.append(str(it.get("suggested_fix", "")))
    text = " ".join(blobs).lower()
    quantifier_markers = [
        "quantifier",
        "for all",
        "for-all",
        "forall",
        "exists",
        "existential",
        "universal",
        "implication",
        "iff",
        "→",
        "↔",
        "∀",
        "∃",
    ]
    if any(m in text for m in quantifier_markers):
        return False
    shape_markers = [
        "api",
        "canonical",
        "style",
        "extra binder",
        "extra conjunct",
        "assumption shape",
        "equivalent assumption",
        "contdiffat",
        "islocalmin f xstar",
    ]
    return any(m in text for m in shape_markers)


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
        "Current pipeline constraints (must be enforced in review):",
        "- Compare declaration semantics primarily against its immediate source comment.",
        "- Use a two-stage decision: first mathematical equivalence judgment, then issue emission only when non-equivalent.",
        "- Quantifier fidelity hard rule: when source comment explicitly specifies logical form (existence/for-all/implication/iff), preserve that form; do not waive quantifier-shape mismatches as style.",
        "- Do not emit issues solely due to API/canonical-style preference when semantics are equivalent.",
        "- Use `section_context` as auxiliary context for previously defined local symbols in the same section.",
        "- Do not treat missing local symbol context as semantic drift when `section_context` provides that definition.",
        "- Gradient equivalence policy: accept `fderiv` + basis-vector component forms as valid coordinate partial-derivative encodings (e.g. `(fderiv ℝ f x) (Pi.single i (1 : ℝ))` or equivalent `if` basis form).",
        "- For this gradient pattern, if `hf : DifferentiableAt ℝ f x` is present, do not emit `missing_assumption` only to request extra slice assumptions.",
        "- Hessian equivalence policy: accept iterated `fderiv` + basis-vector forms as valid Hessian component encodings; do not mark as drift only for using this equivalent form.",
        "- For Hessian, if an explicit twice-differentiable-at-`x` assumption is already present (e.g. `ContDiffAt ℝ 2 f x` or equivalent), do not emit `missing_assumption` only to request a different equivalent assumption shape.",
        "- Local-minimizer equivalence policy: treat `IsLocalMin` and explicit ball-inequality local-min forms as equivalent encodings; do not mark drift solely for swapping between them.",
        "- If local minimality at `xstar` is already given by an explicit radius inequality, do not require an additional explicit `IsLocalMin f xstar` conjunct.",
        "- For `def`, body should not be `sorry`.",
        "- For `theorem`, proof may remain `by sorry` in this pipeline.",
        "- Every generated `def` / `theorem` / `structure` must have an immediate source comment.",
        "- For `kind=thm`, expect exactly one top-level `theorem` (helpers should preferably be local `let`).",
        "- Same-section reuse rule: if `section_context` already defines a needed symbol (e.g. `def xSeq`), theorem statements should reuse it directly and avoid duplicate local `let` redefinitions.",
        "- `variable` is only for parameters/typeclass assumptions; do not treat concrete definitions under `variable` as valid declaration encoding.",
        "- Declarations should start on the next line immediately after source comments, with no blank line between.",
        "- Source comments should use `/- ... -/` block style (not `-- ...`).",
        "- Source comment text should be verbatim-exact to JSON `content` (fallback `problem` only if `content` is empty).",
        "- Add proposition truth judgment: true/false/unknown/not_applicable.",
        "- If judgment is false, provide a concrete counterexample witness.",
    ]
    return "\n".join(lines)


def _build_prompt(base_prompt: str, row: Dict[str, Any]) -> str:
    payload = json.dumps(_build_compare_payload(row), ensure_ascii=False, indent=2)
    constraints = _build_runtime_constraints(row)
    return f"{base_prompt}\n\n{constraints}\n\nInput record:\n{payload}"


_DECL_START_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(def|theorem|lemma|structure|abbrev|class|inductive|instance|axiom|opaque)\b",
    re.MULTILINE,
)

_TOP_LEVEL_NEXT_RE = re.compile(
    r"^\s*(open\b|namespace\b|end\b|"
    r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(def|theorem|lemma|structure|abbrev|class|inductive|instance|axiom|opaque)\b)",
    re.MULTILINE,
)


def _extract_comment_declaration_pairs(lean_code: str) -> List[Dict[str, str]]:
    text = str(lean_code or "")
    pairs: List[Dict[str, str]] = []
    pos = 0
    while True:
        cstart = text.find("/-", pos)
        if cstart < 0:
            break
        cend = text.find("-/", cstart + 2)
        if cend < 0:
            break
        comment_text = text[cstart : cend + 2].strip()
        after = cend + 2
        while after < len(text) and text[after] in " \t\r\n":
            after += 1
        m = _DECL_START_RE.search(text, after)
        if not m or m.start() != after:
            pos = cend + 2
            continue
        dstart = m.start()
        dkind = m.group(1)
        next_comment = text.find("\n/-", dstart + 1)
        next_cmd_match = _TOP_LEVEL_NEXT_RE.search(text, dstart + 1)
        next_cmd = next_cmd_match.start() if next_cmd_match else -1
        candidates = [x for x in (next_comment, next_cmd) if x >= 0]
        dend = min(candidates) if candidates else len(text)
        decl_text = text[dstart:dend].rstrip()
        if decl_text:
            pairs.append(
                {
                    "declaration_kind": dkind,
                    "source_comment": comment_text,
                    "declaration_code": decl_text,
                }
            )
        pos = dend
    return pairs


def _build_compare_payload(row: Dict[str, Any]) -> Dict[str, Any]:
    lean_code = str(row.get("lean_code", "") or "")
    return {
        "label": row.get("label", ""),
        "section": row.get("section", ""),
        "declaration_name": row.get("declaration_name", ""),
        "lean_file": row.get("lean_file", ""),
        "status": row.get("status", ""),
        "lean_code": lean_code,
        "section_context": str(row.get("section_context", "") or ""),
        "comment_declaration_pairs": _extract_comment_declaration_pairs(lean_code),
    }


def _fallback_report(row: Dict[str, Any], reason: str) -> Dict[str, Any]:
    return {
        "label": row.get("label", ""),
        "section": row.get("section", ""),
        "declaration_name": row.get("declaration_name", ""),
        "lean_file": row.get("lean_file", ""),
        "truth_judgement": "unknown",
        "counterexample": "",
        "overall_status": "not_usable_yet",
        "dominant_issue_types": ["task_drift"],
        "top_priority_fix": "Rerun semantic review and return valid JSON.",
        "summary": f"Semantic review failed to produce parseable JSON: {reason}",
        "issues": [
            {
                "severity": "P1",
                "issue_type": "task_drift",
                "location": "global",
                "reason": f"Reviewer output parsing failed: {reason}",
                "suggested_fix": "Regenerate the semantic review report with valid JSON output.",
            }
        ],
        "confidence": 0.0,
    }


def review_record(
    client: APIClient,
    row: Dict[str, Any],
    *,
    max_tokens: int = 4096,
    max_attempts: int = 2,
    prompt_text: str | None = None,
) -> Dict[str, Any]:
    """Run semantic review for one exercise record and return JSON report."""
    if prompt_text is None:
        prompt_text = load_prompt("semantic_review")

    last_error = ""
    for attempt in range(1, max_attempts + 1):
        try:
            response = client.chat(
                prompt=_build_prompt(prompt_text, row),
                max_tokens=max_tokens,
                call_type="semantic_review",
                exercise_label=str(row.get("label", "")),
                json_mode=True,
            )
            report = extract_json_value(response)
            if not isinstance(report, dict):
                raise ValueError("Reviewer output is not a JSON object.")
            report = _apply_two_stage_gate(report)
            report = _normalize_truth_judgement(report, row)
            report.setdefault("label", row.get("label", ""))
            report.setdefault("section", row.get("section", ""))
            report.setdefault("declaration_name", row.get("declaration_name", ""))
            report.setdefault("lean_file", row.get("lean_file", ""))
            return report
        except Exception as err:
            last_error = str(err)
            print(
                f"[semantic_review] attempt {attempt}/{max_attempts} failed for "
                f"{row.get('label', '?')}: {err}",
                file=sys.stderr,
            )
    return _fallback_report(row, last_error or "unknown error")


def write_reports_jsonl(reports: List[Dict[str, Any]], out_path: Path) -> None:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8") as f:
        for report in reports:
            f.write(json.dumps(report, ensure_ascii=False) + "\n")
