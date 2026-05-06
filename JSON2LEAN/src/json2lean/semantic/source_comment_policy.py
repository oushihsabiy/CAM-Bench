"""Enforce exact source-comment policy for generated Lean declarations."""

from __future__ import annotations

import re
from typing import Any, Dict

_DECL_START_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(def|theorem|structure)\b",
    re.MULTILINE,
)


def source_comment_text(raw: Dict[str, Any] | None) -> str:
    """Return the exact source text used for declaration comments."""
    data = raw if isinstance(raw, dict) else {}
    content = data.get("content", "")
    if isinstance(content, str) and content.strip():
        return content
    problem = data.get("problem", "")
    if isinstance(problem, str) and problem.strip():
        return problem
    return ""


def _format_block_comment(text: str) -> str:
    if "\n" in text:
        return f"/-\n{text}\n-/"
    return f"/- {text} -/"


def enforce_exact_source_comments(lean_code: str, raw: Dict[str, Any] | None) -> str:
    """Force immediate declaration comments to equal source ``content`` exactly.

    For each top-level ``def`` / ``theorem`` / ``structure``, ensure there is a
    block comment immediately above it, the declaration starts on the very next
    line, and comment body exactly equals source text (prefer ``content``,
    fallback ``problem``).
    """
    text = str(lean_code or "")
    source_text = source_comment_text(raw)
    if not text.strip() or not source_text.strip():
        return text

    comment_block = _format_block_comment(source_text)
    matches = list(_DECL_START_RE.finditer(text))
    if not matches:
        return text

    for m in reversed(matches):
        dstart = m.start()
        i = dstart - 1
        while i >= 0 and text[i] in " \t\r\n":
            i -= 1
        if i >= 1 and text[i - 1 : i + 1] == "-/":
            cend = i + 1
            cstart = text.rfind("/-", 0, cend - 1)
            if cstart >= 0 and not text[cend:dstart].strip():
                text = text[:cstart] + comment_block + "\n" + text[dstart:]
                continue
        text = text[:dstart] + comment_block + "\n" + text[dstart:]

    return text
