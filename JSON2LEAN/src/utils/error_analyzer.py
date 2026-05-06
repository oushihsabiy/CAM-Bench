"""Frequent compile-error pattern analysis.

Reads historical compile-error JSONL logs and produces ranked error
categories with counts and representative examples.

Two analysis modes
------------------
1. **Normalized grouping** (``analyze_errors``):
   Strip paths / line numbers, collapse identifiers, group by exact
   equality of the normalized message.

2. **Semantic classification** (``classify_errors``):
   Map each error to a high-level category (e.g. LAMBDA_KEYWORD,
   TYPE_MISMATCH, UNKNOWN_CONSTANT, …) based on regex patterns
   derived from observed compile-error clusters.

Usage as CLI::

    python -m src.utils.error_analyzer [--log-dir logs/compile_errors] [--top 20]
    python -m src.utils.error_analyzer --semantic          # semantic mode
    python -m src.utils.error_analyzer --semantic --json   # JSON output
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Dict, List, Tuple

from .compile_logger import read_compile_logs


# ---------------------------------------------------------------------------
# Normalization
# ---------------------------------------------------------------------------

# Patterns that vary across invocations but carry the same semantic error
_PATH_RE = re.compile(r"[/\\][\w./\\-]+\.lean", re.ASCII)
_LINE_COL_RE = re.compile(r"\b\d+:\d+\b")
_IDENT_RE = re.compile(r"\b[A-Z][A-Za-z0-9_'.]+\b")
_NUMBER_RE = re.compile(r"\b\d{2,}\b")


def normalize_error_message(msg: str) -> str:
    """Normalize an error message for grouping."""
    s = str(msg)
    s = _PATH_RE.sub("<PATH>", s)
    s = _LINE_COL_RE.sub("<LOC>", s)
    # Keep short identifiers but replace long camelCase / dotted names
    s = _IDENT_RE.sub("<IDENT>", s)
    s = _NUMBER_RE.sub("<NUM>", s)
    s = re.sub(r"\s+", " ", s).strip()
    # Take only the first meaningful line (multi-line errors)
    first_line = s.split("\n")[0].strip()
    return first_line[:300]


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def analyze_errors(
    log_dir: str | Path | None = None,
    *,
    top_n: int = 20,
) -> List[Dict[str, Any]]:
    """Analyze compile error logs and return ranked error categories.

    Errors are grouped only when their normalized messages are exactly
    identical.  No fuzzy / similarity matching is performed.

    Returns up to *top_n* groups, each with:
    - ``canonical``: the normalized message that defines the group
    - ``total_count``: number of occurrences
    - ``variants``: ``[{"message": canonical, "count": total_count}]``
    - ``examples``: up to 3 raw error examples
    """
    entries = read_compile_logs(log_dir)
    if not entries:
        return []

    # Collect all errors with raw text
    raw_by_normalized: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
    normalized_counts: Counter[str] = Counter()

    for entry in entries:
        for err in entry.get("errors", []):
            raw_msg = str(err.get("message", ""))
            if not raw_msg.strip():
                continue
            norm = normalize_error_message(raw_msg)
            normalized_counts[norm] += 1
            raw_by_normalized[norm].append({
                "lean_file": entry.get("lean_file", ""),
                "timestamp": entry.get("timestamp", ""),
                "line": err.get("line", 0),
                "column": err.get("column", 0),
                "message": raw_msg[:500],
            })

    # Sort by count descending — exact match only, no merging
    sorted_items = sorted(normalized_counts.items(), key=lambda kv: -kv[1])

    results: List[Dict[str, Any]] = []
    for norm, count in sorted_items[:top_n]:
        examples = raw_by_normalized[norm][:3]
        results.append({
            "rank": len(results) + 1,
            "canonical": norm,
            "total_count": count,
            "variants": [{"message": norm, "count": count}],
            "examples": examples,
        })

    return results


# ---------------------------------------------------------------------------
# Semantic classification
# ---------------------------------------------------------------------------

# Each rule is (category, short description, regex on raw message).
# Order matters: first match wins.
_SEMANTIC_RULES: List[Tuple[str, str, re.Pattern[str]]] = [
    (
        "LAMBDA_KEYWORD",
        "λ 用作标识符 (Lean 4 保留关键字)",
        re.compile(r"unexpected token 'λ'"),
    ),
    (
        "MATRIX_MUL_SYMBOL",
        "矩阵乘法符号 ⬝ 或转置 ᵀ 写法错误",
        re.compile(r"(⬝|ᵀ|Qᵀ)"),
    ),
    (
        "ALREADY_DECLARED",
        "重复声明同名定义",
        re.compile(r"has already been declared"),
    ),
    (
        "UNKNOWN_CONSTANT",
        "引用了不存在的 API / 常量",
        re.compile(r"Unknown constant"),
    ),
    (
        "SYNTH_FAILED",
        "类型类实例合成失败",
        re.compile(r"failed to synthesize"),
    ),
    (
        "TYPE_MISMATCH",
        "类型不匹配 (含 EuclideanSpace vs Fin n → ℝ)",
        re.compile(r"[Tt]ype mismatch|[Aa]pplication type mismatch"),
    ),
    (
        "UNSOLVED_GOALS",
        "未解决的证明目标",
        re.compile(r"unsolved goals"),
    ),
    (
        "UNKNOWN_TACTIC",
        "未知 tactic",
        re.compile(r"unknown tactic"),
    ),
    (
        "UNKNOWN_IDENTIFIER",
        "未知标识符",
        re.compile(r"unknown identifier"),
    ),
    (
        "FUNCTION_EXPECTED",
        "function expected",
        re.compile(r"[Ff]unction expected"),
    ),
    (
        "TIMEOUT",
        "编译超时",
        re.compile(r"timed out"),
    ),
    (
        "EXPECTED_TOKEN",
        "语法错误 (expected / unexpected token)",
        re.compile(r"expected token|unexpected token"),
    ),
    (
        "SYNTAX_ERROR",
        "其他语法错误",
        re.compile(r"expected|unexpected", re.IGNORECASE),
    ),
]


def _classify_message(msg: str) -> Tuple[str, str]:
    """Return (category, detail) for a single error message."""
    for category, _desc, pattern in _SEMANTIC_RULES:
        if pattern.search(msg):
            # Build a concise detail string
            first_line = msg.split("\n")[0].strip()[:200]
            return category, first_line
    first_line = msg.split("\n")[0].strip()[:200]
    return "OTHER", first_line


def classify_errors(
    log_dir: str | Path | None = None,
    *,
    top_n: int = 20,
) -> List[Dict[str, Any]]:
    """Semantic classification of compile errors.

    Returns up to *top_n* categories sorted by frequency, each with:
    - ``category``: high-level error class (e.g. ``LAMBDA_KEYWORD``)
    - ``description``: short Chinese description
    - ``count``: total occurrences
    - ``details``: sub-breakdown ``{detail_str: count}``
    - ``examples``: up to 3 raw error dicts
    """
    entries = read_compile_logs(log_dir)
    if not entries:
        return []

    cat_counter: Counter[str] = Counter()
    detail_counter: Counter[Tuple[str, str]] = Counter()
    cat_examples: Dict[str, List[Dict[str, Any]]] = defaultdict(list)

    for entry in entries:
        for err in entry.get("errors", []):
            raw_msg = str(err.get("message", "")).strip()
            if not raw_msg:
                continue
            cat, detail = _classify_message(raw_msg)
            cat_counter[cat] += 1
            detail_counter[(cat, detail)] += 1
            if len(cat_examples[cat]) < 3:
                cat_examples[cat].append({
                    "lean_file": entry.get("lean_file", ""),
                    "run_label": entry.get("run_label", ""),
                    "message": raw_msg[:500],
                    "line_content": str(err.get("line_content", ""))[:200],
                })

    # Build description lookup
    desc_map = {cat: desc for cat, desc, _ in _SEMANTIC_RULES}
    desc_map.setdefault("OTHER", "其他错误")

    results: List[Dict[str, Any]] = []
    for cat, count in cat_counter.most_common(top_n):
        # Sub-details for this category
        details = {
            detail: cnt
            for (c, detail), cnt in detail_counter.most_common()
            if c == cat
        }
        results.append({
            "rank": len(results) + 1,
            "category": cat,
            "description": desc_map.get(cat, ""),
            "count": count,
            "details": details,
            "examples": cat_examples[cat],
        })

    return results


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        prog="error_analyzer",
        description="Analyze compile error logs for high-frequency patterns.",
    )
    parser.add_argument(
        "--log-dir",
        default="logs/compile_errors",
        help="Directory containing compile error JSONL logs.",
    )
    parser.add_argument(
        "--top", type=int, default=20,
        help="Number of top error categories to display.",
    )
    parser.add_argument(
        "--json", action="store_true",
        help="Output results as JSON instead of human-readable text.",
    )
    parser.add_argument(
        "--semantic", action="store_true",
        help="Use semantic classification instead of normalized grouping.",
    )
    args = parser.parse_args()

    if args.semantic:
        results = classify_errors(args.log_dir, top_n=args.top)
    else:
        results = analyze_errors(args.log_dir, top_n=args.top)

    if not results:
        print("No compile error logs found.", file=sys.stderr)
        sys.exit(0)

    if args.json:
        print(json.dumps(results, ensure_ascii=False, indent=2))
    elif args.semantic:
        total = sum(r["count"] for r in results)
        print(f"\n{'='*70}")
        print(f"  Semantic Error Classification  (total errors: {total})")
        print(f"{'='*70}\n")
        for r in results:
            pct = r["count"] / total * 100 if total else 0
            print(f"  #{r['rank']}  {r['category']}  [{r['count']} | {pct:.0f}%]")
            print(f"       {r['description']}")
            for detail, cnt in list(r["details"].items())[:5]:
                print(f"         - [{cnt}] {detail[:120]}")
            if r["examples"]:
                ex = r["examples"][0]
                print(f"       Example: {ex['lean_file']} ({ex.get('run_label','')})")
                print(f"         {ex['message'][:150]}")
            print()
    else:
        print(f"\n{'='*70}")
        print(f"  Frequent Compile Error Patterns  (top {args.top})")
        print(f"{'='*70}\n")
        for r in results:
            print(f"  #{r['rank']}  [{r['total_count']} occurrences]")
            print(f"  Pattern: {r['canonical']}")
            if r["examples"]:
                ex = r["examples"][0]
                print(f"  Example: {ex['lean_file']}:{ex.get('line','?')} — {ex['message'][:120]}")
            print()


if __name__ == "__main__":
    main()
