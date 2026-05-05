#!/usr/bin/env python3
"""Organize data-pair/ into proof-bench/problems/ with a 3-level structure.

Output structure:
    proof-bench/problems/
    └── {chapter}/          e.g. convex-ch2/
        └── {problem_id}/   e.g. Exercise_2_1/
            ├── formal.lean   (original lean + Source: header prepended)
            └── informal.json (single dict with problem entry)

Usage:
    python organize_problems.py                # process all chapters
    python organize_problems.py --chapter convex-ch2  # single chapter
    python organize_problems.py --dry-run      # preview without writing
"""

import argparse
import json
import re
import sys
from pathlib import Path

# ── paths ──────────────────────────────────────────────────────────────────────
REPO_ROOT = Path(__file__).resolve().parent
DATA_PAIR_DIR = REPO_ROOT / "data-pair"
PROBLEMS_DIR = REPO_ROOT / "proof-bench" / "problems"

# Regex to extract source_idx from BLOCK comment:
# /- [BLOCK Exercise 2.11-(a) | 11 | defn]
_BLOCK_RE = re.compile(r"/- \[BLOCK ([^\|]+?)\s*\|")

# Regex to decode a lean file stem into a canonical source_idx string:
# Exercise_2_10__a_  →  Exercise 2.10-(a)
# Exercise_2_11      →  Exercise 2.11
_STEM_RE = re.compile(r"^Exercise_(\d+)_(\d+)(?:__([a-z])_)?$")


# ── helpers ────────────────────────────────────────────────────────────────────

def _source_idx_from_block(content: str) -> str | None:
    """Extract source_idx from the first BLOCK comment in a lean file."""
    m = _BLOCK_RE.search(content)
    return m.group(1).strip() if m else None


def _source_idx_from_stem(stem: str) -> str | None:
    """Derive source_idx from a lean file stem as fallback."""
    m = _STEM_RE.match(stem)
    if not m:
        return None
    major, minor, letter = m.group(1), m.group(2), m.group(3)
    base = f"Exercise {major}.{minor}"
    return f"{base}-({letter})" if letter else base


def _build_informal_lookup(informal_path: Path) -> dict[str, dict]:
    """Return a dict mapping source_idx → entry from the chapter informal.json."""
    try:
        with open(informal_path, encoding="utf-8") as f:
            entries = json.load(f)
    except (OSError, json.JSONDecodeError) as e:
        print(f"  ERROR: could not read {informal_path}: {e}", file=sys.stderr)
        return {}
    return {entry["source_idx"]: entry for entry in entries}


def _build_formal_content(original_content: str, source: str) -> str:
    """Prepend a Source: metadata header to the lean file content."""
    header = f"/-\nSource: {source}\n-/\n"
    return header + original_content


def _process_lean_file(
    lean_path: Path,
    informal_lookup: dict[str, dict],
    chapter_dir: Path,
    dry_run: bool,
) -> bool:
    """Process one lean file and write problem_id/ folder. Returns True on success."""
    stem = lean_path.stem  # e.g. Exercise_2_10__a_
    content = lean_path.read_text(encoding="utf-8")

    # Determine source_idx for informal lookup
    source_idx = _source_idx_from_block(content) or _source_idx_from_stem(stem)
    if source_idx is None:
        print(f"  WARN: cannot derive source_idx for {lean_path.name}, skipping")
        return False

    informal_entry = informal_lookup.get(source_idx)
    if informal_entry is None:
        print(f"  WARN: no informal entry for '{source_idx}' ({lean_path.name}), skipping")
        return False

    # Derive source string (e.g. "book/convex_optimization_Chp2")
    source = informal_entry.get("source", "")

    problem_dir = chapter_dir / stem
    formal_lean_path = problem_dir / "formal.lean"
    informal_json_path = problem_dir / "informal.json"

    print(f"  {stem}/  ← '{source_idx}'")

    if not dry_run:
        problem_dir.mkdir(parents=True, exist_ok=True)
        formal_lean_path.write_text(
            _build_formal_content(content, source), encoding="utf-8"
        )
        informal_json_path.write_text(
            json.dumps(informal_entry, ensure_ascii=False, indent=2), encoding="utf-8"
        )

    return True


def _process_chapter(chapter_path: Path, dry_run: bool) -> int:
    """Process one chapter folder under data-pair/. Returns number of problems written."""
    chapter_name = chapter_path.name
    informal_path = chapter_path / "informal.json"
    formal_dir = chapter_path / "formal"

    if not informal_path.exists():
        print(f"  WARN: {informal_path} not found, skipping chapter")
        return 0
    if not formal_dir.exists():
        print(f"  WARN: {formal_dir} not found, skipping chapter")
        return 0

    informal_lookup = _build_informal_lookup(informal_path)
    if not informal_lookup:
        return 0

    chapter_out = PROBLEMS_DIR / chapter_name
    print(f"\nChapter: {chapter_name}  ({len(list(formal_dir.glob('*.lean')))} lean files)")

    if not dry_run:
        chapter_out.mkdir(parents=True, exist_ok=True)

    count = 0
    for lean_path in sorted(formal_dir.glob("*.lean")):
        if _process_lean_file(lean_path, informal_lookup, chapter_out, dry_run):
            count += 1

    print(f"  → {count} problems {'(dry-run)' if dry_run else 'written'}")
    return count


# ── main ────────────────────────────────────────────────────────────────────────

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Organize data-pair/ into proof-bench/problems/ 3-level structure"
    )
    parser.add_argument(
        "--chapter",
        metavar="NAME",
        help="Process only this chapter (e.g. convex-ch2)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Preview actions without writing any files",
    )
    args = parser.parse_args()

    if not DATA_PAIR_DIR.exists():
        print(f"ERROR: data-pair directory not found: {DATA_PAIR_DIR}", file=sys.stderr)
        sys.exit(1)

    if args.dry_run:
        print("=== DRY RUN (no files will be written) ===")

    if args.chapter:
        chapter_path = DATA_PAIR_DIR / args.chapter
        if not chapter_path.exists():
            print(f"ERROR: chapter not found: {chapter_path}", file=sys.stderr)
            sys.exit(1)
        chapters = [chapter_path]
    else:
        chapters = sorted(p for p in DATA_PAIR_DIR.iterdir() if p.is_dir())

    total = 0
    for chapter_path in chapters:
        total += _process_chapter(chapter_path, args.dry_run)

    print(f"\nTotal: {total} problems {'previewed' if args.dry_run else 'written to'} {PROBLEMS_DIR}")


if __name__ == "__main__":
    main()
