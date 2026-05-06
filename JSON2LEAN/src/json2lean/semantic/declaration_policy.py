"""Top-level declaration policy checks for generated Lean code."""

from __future__ import annotations

import re
from typing import List

_TOP_DECL_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(def|theorem|lemma|structure|abbrev|class|inductive|instance|axiom|opaque)\b",
    re.MULTILINE,
)


def top_level_decl_kinds(code: str) -> List[str]:
    text = str(code or "")
    return [m.group(1) for m in _TOP_DECL_RE.finditer(text)]


def validate_top_level_contract(kind: str, code: str) -> str:
    """Return an error string if top-level declaration contract is violated."""
    k = str(kind or "").strip().lower()
    decls = top_level_decl_kinds(code)
    if k in ("algo", "alg"):
        structure_count = sum(1 for d in decls if d == "structure")
        if structure_count < 1:
            return (
                "kind=algo requires at least one top-level `structure`; "
                f"found {structure_count} (top-level declarations: {decls})."
            )
        return ""
    # hints should not produce Lean declarations
    if k == "hints":
        return ""
    return ""
