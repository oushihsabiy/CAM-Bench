"""Deterministic block-comment generation and parsing for the combined Lean file.

Every block in the combined Lean file is delimited by a **block comment** of the
form::

    /- [BLOCK <source_idx> | <index> | <kind>]
    <verbatim content text>
    -/

The comment serves two purposes simultaneously:

1. **Structural delimiter** – ``parse_blocks`` splits the file into blocks by
   these comments.  All downstream stages (translation, semantic review,
   semantic rewrite, compile repair) use the same parser.
2. **Source comment** – the body carries the verbatim source ``content`` (or
   ``problem``), so every Lean declaration is preceded by a human-readable
   description.

Non-negotiable invariant: block comments are inserted by the pipeline
orchestrator **before** block translation and are **never** freely generated
by the translator LLM, nor rewritten by postprocess, semantic rewrite, or
compile repair.
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from typing import Any, Callable, Dict, List, Tuple, Optional


# ---------------------------------------------------------------------------
# Block-comment format constants
# ---------------------------------------------------------------------------

_BLOCK_HEADER_RE = re.compile(
    r"/-\s*\[BLOCK\s+(?P<source_idx>[^|]+?)\s*\|\s*(?P<index>[^|]+?)\s*\|\s*(?P<kind>[^\]]+?)\]",
)

# Supports both:
#   /- [BLOCK ...]
# and
#   /-
#   [BLOCK ...]
_BLOCK_COMMENT_START_RE = re.compile(r"/-\s*\[BLOCK\b", re.MULTILINE)

# Match the full block comment (handles the common case – no nested comments).
# We locate the header and then search forward for the closing ``-/``.

# Regex for top-level declarations with names (def, theorem, lemma, etc.)
_DECL_WITH_NAME_RE = re.compile(
    r"^(\s*(?:def|theorem|lemma|example|instance|structure|class|inductive|axiom)\s+(\w+))",
    re.MULTILINE,
)

# Match top-level commands that may be duplicated across blocks (open, variable, set_option)
_TOP_LEVEL_CMD_RE = re.compile(
    r"^[ \t]*(?:open(?:\s+scoped)?|variable|set_option)\b[^\n]*",
    re.MULTILINE,
)


# ---------------------------------------------------------------------------
# Deduplication helpers
# ---------------------------------------------------------------------------

def _collect_decl_names(text: str) -> set:
    """Extract all top-level declaration names from Lean code."""
    names = set()
    for m in _DECL_WITH_NAME_RE.finditer(text):
        decl_name = m.group(2)
        if decl_name:
            names.add(decl_name)
    return names


def _collect_top_level_commands(text: str) -> set:
    """Extract all top-level open/variable/set_option commands from Lean code."""
    cmds = set()
    for m in _TOP_LEVEL_CMD_RE.finditer(text):
        cmd = m.group(0).strip()
        if cmd:
            cmds.add(cmd)
    return cmds


def dedupe_block_code_against_frozen(
    block_code: str,
    frozen_text: str,
    keep_if_related: Optional[Callable[[str, str], bool]] = None,
) -> tuple[str, Dict[str, int]]:
    """Remove duplicated declarations/lines from current block against frozen context.
    
    Args:
        block_code: the code block to potentially deduplicate
        frozen_text: the earlier frozen context (all blocks before this one)
        keep_if_related: optional predicate ``(kind, removed_text) -> bool``.
            If it returns ``True``, the candidate removal is kept (not deleted).
            ``kind`` is one of ``declaration`` or ``command``.
    
    Returns:
        (deduplicated_code, stats_dict) where stats_dict contains:
            - removed_declarations: count of declaration removals
            - removed_lines: count of line removals
    """
    current = str(block_code or "")
    frozen = str(frozen_text or "")
    frozen_decl_names = _collect_decl_names(frozen)

    removed_decl = 0
    decl_matches = list(_DECL_WITH_NAME_RE.finditer(current))
    drop_ranges: List[tuple[int, int]] = []
    for idx, m in enumerate(decl_matches):
        decl_name = m.group(2)
        if decl_name not in frozen_decl_names:
            continue
        start = m.start()
        end = decl_matches[idx + 1].start() if idx + 1 < len(decl_matches) else len(current)
        candidate = current[start:end]
        if keep_if_related is not None:
            try:
                if keep_if_related("declaration", candidate):
                    continue
            except Exception:
                # Fail-safe: keep candidate when relatedness check is unavailable.
                continue
        drop_ranges.append((start, end))
        removed_decl += 1

    if drop_ranges:
        rebuilt_parts: List[str] = []
        pos = 0
        for start, end in drop_ranges:
            if start > pos:
                rebuilt_parts.append(current[pos:start])
            pos = max(pos, end)
        if pos < len(current):
            rebuilt_parts.append(current[pos:])
        current = "".join(rebuilt_parts)

    # Stage 2: remove duplicate top-level commands (open / variable / set_option)
    frozen_cmds = _collect_top_level_commands(frozen)
    removed_lines = 0
    if frozen_cmds:
        kept_lines: List[str] = []
        for ln in current.splitlines():
            if _TOP_LEVEL_CMD_RE.match(ln) and ln.strip() in frozen_cmds:
                if keep_if_related is not None:
                    try:
                        if keep_if_related("command", ln):
                            kept_lines.append(ln)
                            continue
                    except Exception:
                        # Fail-safe: keep candidate when relatedness check is unavailable.
                        kept_lines.append(ln)
                        continue
                removed_lines += 1
                continue
            kept_lines.append(ln)
        current = "\n".join(kept_lines)

    cleaned = current.strip()
    return cleaned, {
        "removed_declarations": removed_decl,
        "removed_lines": removed_lines,
    }


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class BlockSpan:
    """Byte-offset span of one block inside the combined Lean file."""

    block_id: str
    comment_start: int
    comment_end: int    # exclusive – points right after the closing ``-/``
    code_start: int     # first char after comment (may equal code_end if empty)
    code_end: int       # exclusive – start of next block comment or end of section/file


# ---------------------------------------------------------------------------
# Block-comment generation (deterministic)
# ---------------------------------------------------------------------------

def _block_id(source_idx: str, index: Any, kind: str) -> str:
    """Canonical block identifier derived from raw fields."""
    return f"{source_idx}|{index}|{kind}"


def generate_block_comment(raw: Dict[str, Any]) -> str:
    """Generate the structural block comment from an exercise's *raw* dict.

    The comment embeds the verbatim ``content`` (fallback ``problem``) so that
    later stages can compare Lean code against the source text.
    """
    source_idx = str(raw.get("source_idx") or "UNSPECIFIED").strip()
    index = str(raw.get("index") or "0").strip()
    kind = str(raw.get("kind") or "unknown").strip()
    content = str(raw.get("content") or raw.get("problem") or "").strip()

    header = f"[BLOCK {source_idx} | {index} | {kind}]"
    if content:
        return f"/- {header}\n{content}\n-/"
    return f"/- {header} -/"


def block_id_for(raw: Dict[str, Any]) -> str:
    """Return the canonical block-id that ``generate_block_comment`` would produce."""
    source_idx = str(raw.get("source_idx") or "UNSPECIFIED").strip()
    index = str(raw.get("index") or "0").strip()
    kind = str(raw.get("kind") or "unknown").strip()
    return _block_id(source_idx, index, kind)


# ---------------------------------------------------------------------------
# Block parsing
# ---------------------------------------------------------------------------

def _find_comment_end(text: str, start: int) -> int:
    """Find the end of a ``/- ... -/`` block comment handling nesting."""
    depth = 1
    i = start + 2  # skip the opening ``/-``
    length = len(text)
    while i < length:
        if text[i] == '/' and i + 1 < length and text[i + 1] == '-':
            depth += 1
            i += 2
            continue
        if text[i] == '-' and i + 1 < length and text[i + 1] == '/':
            depth -= 1
            i += 2
            if depth == 0:
                return i  # exclusive end right after ``-/``
            continue
        i += 1
    return length  # unterminated – treat rest as comment


def parse_blocks(lean_text: str) -> List[BlockSpan]:
    """Parse all ``[BLOCK …]`` delimited blocks in *lean_text*.

    Returns blocks **in file order**.  Code that does not belong to any block
    (e.g. the preamble ``import Mathlib`` / ``noncomputable section`` / section
    wrappers) is not included.
    """
    text = lean_text
    blocks: List[BlockSpan] = []
    pos = 0
    while pos < len(text):
        # Look for a block-header comment, including newline-separated header style.
        mstart = _BLOCK_COMMENT_START_RE.search(text, pos)
        if mstart is None:
            break
        idx = mstart.start()
        m = _BLOCK_HEADER_RE.match(text, idx)
        if m is None:
            pos = idx + 2
            continue

        comment_start = idx
        comment_end = _find_comment_end(text, comment_start)
        source_idx = m.group("source_idx").strip()
        index_val = m.group("index").strip()
        kind_val = m.group("kind").strip()
        bid = _block_id(source_idx, index_val, kind_val)

        # Code region: from comment_end to start of next block comment or
        # section/file boundary.
        code_start = comment_end
        next_m = _BLOCK_COMMENT_START_RE.search(text, comment_end)
        next_block = next_m.start() if next_m is not None else -1
        # Also consider section ``end`` as boundary
        end_marker = _find_next_section_end(text, comment_end)
        candidates = [c for c in (next_block, end_marker) if c >= 0]
        code_end = min(candidates) if candidates else len(text)

        blocks.append(BlockSpan(
            block_id=bid,
            comment_start=comment_start,
            comment_end=comment_end,
            code_start=code_start,
            code_end=code_end,
        ))
        pos = comment_end

    return blocks


def _find_next_section_end(text: str, start: int) -> int:
    """Find the position of the next ``end <SectionName>`` line after *start*.

    Skips occurrences that appear inside block comments (``/- ... -/``) to
    avoid truncating a block's code region at an ``end`` that is part of a
    comment or a nested structure.

    Returns -1 if not found.
    """
    pattern = re.compile(r"^\s*end\s+\w+", re.MULTILINE)
    pos = start
    while True:
        m = pattern.search(text, pos)
        if m is None:
            return -1
        # Check whether this match falls inside a block comment.
        # Walk from `start` tracking comment depth at m.start().
        depth = 0
        i = start
        target = m.start()
        while i < target:
            if text[i] == '/' and i + 1 < target and text[i + 1] == '-':
                depth += 1
                i += 2
                continue
            if text[i] == '-' and i + 1 < target and text[i + 1] == '/':
                if depth > 0:
                    depth -= 1
                i += 2
                continue
            i += 1
        if depth == 0:
            return m.start()
        # Inside a comment – skip past the closing '-/' and retry.
        close = text.find('-/', m.end())
        if close < 0:
            return -1
        pos = close + 2


# ---------------------------------------------------------------------------
# Single-block access helpers
# ---------------------------------------------------------------------------

def extract_block_by_id(lean_text: str, block_id: str) -> Tuple[str, int, int] | None:
    """Return ``(code_text, code_start, code_end)`` for *block_id*, or ``None``."""
    for b in parse_blocks(lean_text):
        if b.block_id == block_id:
            return lean_text[b.code_start:b.code_end].strip(), b.code_start, b.code_end
    return None


def extract_block_comment_and_code(lean_text: str, block_id: str) -> Tuple[str, int, int] | None:
    """Return ``(comment+code_text, span_start, span_end)`` for *block_id*."""
    for b in parse_blocks(lean_text):
        if b.block_id == block_id:
            return lean_text[b.comment_start:b.code_end].strip(), b.comment_start, b.code_end
    return None


def extract_block_comment_text(lean_text: str, block_id: str) -> str | None:
    """Return raw block-comment text for *block_id*, or ``None``."""
    for b in parse_blocks(lean_text):
        if b.block_id == block_id:
            return lean_text[b.comment_start:b.comment_end].strip()
    return None


def replace_block_code(
    lean_text: str,
    block_id: str,
    new_code: str,
    frozen_context: Optional[str] = None,
    keep_if_related: Optional[Callable[[str, str], bool]] = None,
) -> tuple[str, Dict[str, int]]:
    """Replace **only** the code region of *block_id*, with automatic deduplication.
    
    This function performs block replacement in the temporary in-memory state,
    applying deduplication if frozen_context is provided (all earlier blocks).
    
    Args:
        lean_text: the full Lean file text
        block_id: the target block ID to replace
        new_code: the new code to insert
        frozen_context: optional earlier context (all prior blocks) to dedupe against
                       If provided, new_code will be deduplicated first.
        keep_if_related: optional predicate passed to deduplication. If it
            returns ``True`` for a candidate removal, that candidate is kept.
    
    Returns:
        (updated_file_text, dedup_stats) where dedup_stats contains:
            - removed_declarations: count of deduplications applied
            - removed_lines: count of line deduplications applied
    """
    dedup_stats = {
        "removed_declarations": 0,
        "removed_lines": 0,
    }
    
    # Apply deduplication if frozen context is provided
    code_to_insert = new_code.strip()
    if frozen_context is not None:
        code_to_insert, dedup_stats = dedupe_block_code_against_frozen(
            code_to_insert,
            frozen_context,
            keep_if_related=keep_if_related,
        )
    
    # Replace the block code
    for b in parse_blocks(lean_text):
        if b.block_id == block_id:
            before = lean_text[:b.code_start]
            after = lean_text[b.code_end:]
            if code_to_insert:
                result = before + "\n" + code_to_insert + "\n\n" + after.lstrip("\n")
            else:
                result = before + "\n" + after.lstrip("\n")
            return result, dedup_stats
    
    # Block not found – return unchanged with no deduplications
    return lean_text, dedup_stats


def frozen_context_before(lean_text: str, block_id: str) -> str:
    """Return same-section text before *block_id*'s comment.

    This intentionally excludes earlier/later sibling sections. If a matching
    section header cannot be found, falls back to all text before the block.
    """
    for b in parse_blocks(lean_text):
        if b.block_id == block_id:
            before = lean_text[:b.comment_start]
            section_starts = list(
                re.finditer(r"^\s*namespace\s+[A-Za-z0-9_']+\s*$", before, re.MULTILINE)
            )
            if section_starts:
                return before[section_starts[-1].start():].rstrip()
            return before.rstrip()
    return lean_text.rstrip()


def frozen_context_in_section(lean_text: str, block_id: str, section_name: str) -> str:
    """Return only the text within *section_name* that precedes *block_id*'s comment.

    Limits deduplication scope to the current section so that identically-named
    declarations in different sections are not incorrectly removed.  Falls back
    to ``frozen_context_before`` when the section bounds cannot be located.
    """
    open_pat = re.compile(rf"(?m)^namespace\s+{re.escape(section_name)}\s*$")
    close_pat = re.compile(rf"(?m)^end\s+{re.escape(section_name)}\s*$")
    open_m = open_pat.search(lean_text)
    if open_m is None:
        print(
            f"[dedupe][warn] namespace '{section_name}' not found for block '{block_id}', skip dedupe context",
            file=sys.stderr,
        )
        return ""
    body_start = open_m.end()
    close_m = close_pat.search(lean_text, body_start)
    if close_m is None:
        print(
            f"[dedupe][warn] end '{section_name}' not found for block '{block_id}', skip dedupe context",
            file=sys.stderr,
        )
        return ""
    sec_end = close_m.start()
    for b in parse_blocks(lean_text):
        if b.block_id == block_id:
            if body_start <= b.comment_start <= sec_end:
                return lean_text[body_start:b.comment_start].rstrip()
            break
    print(
        f"[dedupe][warn] block '{block_id}' is outside namespace '{section_name}' bounds, skip dedupe context",
        file=sys.stderr,
    )
    return ""


def insert_block_comment(lean_text: str, section_name: str, block_comment: str) -> str:
    """Insert *block_comment* just before the ``end <section_name>`` line.

    If the section doesn't exist yet, append it as a new section.
    """
    close_pat = re.compile(rf"(?m)^end\s+{re.escape(section_name)}\s*$")
    matches = list(close_pat.finditer(lean_text))
    idx = matches[-1].start() if matches else -1
    if idx < 0:
        # Section not found – append new section
        return (
            lean_text.rstrip() + "\n\n"
            f"namespace {section_name}\n\n"
            f"{block_comment}\n\n"
            f"end {section_name}\n"
        )
    before = lean_text[:idx].rstrip()
    after = lean_text[idx:]
    return before + "\n\n" + block_comment + "\n\n" + after


def insert_code_after_comment(lean_text: str, block_id: str, code: str) -> str:
    """Insert *code* directly after the block comment for *block_id*.

    This is used after translation: the comment is already in the file but
    the code region is empty.
    """
    for b in parse_blocks(lean_text):
        if b.block_id == block_id:
            before = lean_text[:b.comment_end]
            after = lean_text[b.comment_end:]
            stripped_code = code.strip()
            if stripped_code:
                return before + "\n" + stripped_code + "\n" + after.lstrip("\n")
            return lean_text
    return lean_text
