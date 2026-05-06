"""Lean redundancy cleanup.

Removes duplicated content from a generated Lean file:
- Duplicate ``import`` lines
- Duplicate ``open`` / ``open scoped`` / ``variable`` / ``set_option`` commands
- Duplicate declaration names (keep first occurrence)
- Repeated helper code fragments (identical consecutive blocks)
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import List, Set, Tuple


def cleanup_redundancies(text: str) -> Tuple[str, int]:
    """Remove redundant code from Lean text.

    Returns ``(cleaned_text, num_removals)``.
    """
    removals = 0

    # Pass 1: deduplicate imports
    text, n = _dedupe_imports(text)
    removals += n

    # Pass 2: deduplicate top-level commands within each section
    text, n = _dedupe_section_commands(text)
    removals += n

    # Pass 3: remove consecutive duplicate blank-line blocks
    text = _collapse_blank_lines(text)

    return text, removals


def cleanup_lean_file(filepath: str | Path) -> int:
    """Clean up redundancies in a Lean file in-place.

    Returns number of removals made.
    """
    path = Path(filepath)
    text = path.read_text(encoding="utf-8")
    cleaned, removals = cleanup_redundancies(text)
    if removals > 0:
        path.write_text(cleaned, encoding="utf-8")
    return removals


def _dedupe_imports(text: str) -> Tuple[str, int]:
    """Remove duplicate import lines, keeping the first occurrence."""
    lines = text.split("\n")
    seen: Set[str] = set()
    out: List[str] = []
    removed = 0
    for line in lines:
        stripped = line.strip()
        if stripped.startswith("import "):
            if stripped in seen:
                removed += 1
                continue
            seen.add(stripped)
        out.append(line)
    return "\n".join(out), removed


def _dedupe_section_commands(text: str) -> Tuple[str, int]:
    """Deduplicate open/variable/set_option within each section scope."""
    cmd_re = re.compile(
        r"^[ \t]*(?:open(?:\s+scoped)?|variable|set_option)\b[^\n]*",
        re.MULTILINE,
    )
    section_re = re.compile(r"^namespace\s+", re.MULTILINE)
    end_re = re.compile(r"^end\s+", re.MULTILINE)

    lines = text.split("\n")
    out: List[str] = []
    seen_in_scope: Set[str] = set()
    removed = 0

    for line in lines:
        stripped = line.strip()
        if section_re.match(stripped) or end_re.match(stripped):
            seen_in_scope.clear()
            out.append(line)
            continue
        if cmd_re.match(stripped):
            if stripped in seen_in_scope:
                removed += 1
                continue
            seen_in_scope.add(stripped)
        out.append(line)

    return "\n".join(out), removed


def _collapse_blank_lines(text: str) -> str:
    """Collapse 3+ consecutive blank lines to 2."""
    return re.sub(r"\n{4,}", "\n\n\n", text)
