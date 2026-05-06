"""Build sidecar JSON input for semantic review.

This script does not modify the existing pipeline. It only joins:
1) original (non-preprocessed) exercise entries from input JSON, and
2) generated Lean files in an output directory.

Usage example:
    python3 -m json2lean.build_semantic_review_input \
      --input-json data/picks.json \
      --lean-dir lean/LeanProject/picks
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Dict, Iterable, List

from ..loader import load_json
from ..parser import is_exercise_object, parse_exercises


def _safe_label(label: str) -> str:
    return re.sub(r"[^\w\-.]", "_", str(label)) or "exercise"


def _extract_top_block_comment(lean_code: str) -> str:
    text = lean_code.lstrip()
    if not text.startswith("/-"):
        return ""
    end = text.find("-/")
    if end < 0:
        return ""
    return text[: end + 2]


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


def _extract_comment_declaration_pairs(lean_code: str) -> List[Dict[str, Any]]:
    """Extract immediate `/- ... -/` comment + following declaration pairs."""
    text = str(lean_code or "")
    pairs: List[Dict[str, Any]] = []
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
        if m and m.start() == after:
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
            continue
        pos = cend + 2
    return pairs


def _default_output_path(project_root: Path, input_json: Path) -> Path:
    out_dir = project_root / "review_log"
    return out_dir / f"{input_json.stem}_review.json"


def _load_preprocessed_records(
    project_root: Path,
    input_json: Path,
) -> Dict[str, Dict[str, Any]]:
    """Load preprocessed records dumped by main pipeline, indexed by label."""
    input_stem = _safe_label(input_json.stem)
    path = project_root / "review_log" / f"{input_stem}_preprocessed.json"
    if not path.exists():
        return {}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {}

    records: List[Any] = []
    if isinstance(data, dict) and isinstance(data.get("records"), list):
        records = data["records"]
    elif isinstance(data, list):
        records = data

    by_label: Dict[str, Dict[str, Any]] = {}
    for rec in records:
        if not isinstance(rec, dict):
            continue
        label = str(rec.get("label", "")).strip()
        if label and label not in by_label:
            by_label[label] = rec
    return by_label


def _iter_original_exercise_dicts(node: Any) -> Iterable[Dict[str, Any]]:
    """Yield original exercise dicts without parser normalization."""
    if is_exercise_object(node):
        # Keep original object shape to preserve truly raw fields.
        if isinstance(node, dict):
            yield node
        return
    if isinstance(node, list):
        for item in node:
            yield from _iter_original_exercise_dicts(item)
        return
    if isinstance(node, dict):
        for item in node.values():
            yield from _iter_original_exercise_dicts(item)


def _extract_original_problem(ex_raw: Dict[str, Any]) -> str:
    for key in ("problem", "content", "题目内容", "问题", "题目"):
        val = ex_raw.get(key, "")
        if isinstance(val, str) and val.strip():
            return val
    return ""


def _build_row(
    ex_raw: Dict[str, Any],
    label: str,
    lean_file: Path,
    preprocessed_record: Dict[str, Any] | None = None,
) -> Dict[str, Any]:
    if lean_file.exists():
        lean_code = lean_file.read_text(encoding="utf-8")
    else:
        lean_code = ""
    return {
        "lean_code": lean_code,
        "comment_declaration_pairs": _extract_comment_declaration_pairs(lean_code),
    }


def _ensure_unique_labels(exercises: List[Any]) -> None:
    used: set[str] = set()
    for ex in exercises:
        base = str(getattr(ex, "label", "") or "").strip() or str(getattr(ex, "raw", {}).get("source_idx") or "exercise")
        raw_idx = getattr(ex, "raw", {}).get("index", getattr(ex, "index", 0))
        candidate = base
        if candidate in used:
            candidate = f"{base}_{raw_idx}"
        k = 2
        while candidate in used:
            candidate = f"{base}_{raw_idx}_{k}"
            k += 1
        ex.label = candidate
        used.add(candidate)


def build_review_input_rows(input_json: Path, lean_dir: Path) -> List[Dict[str, Any]]:
    """Build review rows by pairing original JSON entries with generated Lean files."""
    project_root = Path(__file__).resolve().parents[2]
    combined_file = lean_dir / f"{_safe_label(input_json.stem)}.lean"
    if combined_file.exists():
        return [_build_row({}, _safe_label(input_json.stem), combined_file, None)]

    data = load_json(input_json)
    exercises = parse_exercises(data)
    _ensure_unique_labels(exercises)
    original_rows = list(_iter_original_exercise_dicts(data))
    preprocessed_by_label = _load_preprocessed_records(project_root, input_json)
    rows: List[Dict[str, Any]] = []
    for idx, ex in enumerate(exercises):
        label = str(ex.label)
        lean_file = lean_dir / f"{_safe_label(label)}.lean"
        ex_raw = original_rows[idx] if idx < len(original_rows) else ex.raw
        rows.append(
            _build_row(
                ex_raw,
                label,
                lean_file,
                preprocessed_record=preprocessed_by_label.get(label),
            )
        )
    return rows


def write_review_json(rows: List[Dict[str, Any]], out_path: Path) -> Dict[str, int]:
    """Write review rows to pretty JSON array and return simple counters."""
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(
        json.dumps(rows, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    total = len(rows)
    matched = sum(1 for r in rows if str(r.get("lean_code", "")).strip())
    missing = total - matched
    return {"total": total, "matched": matched, "missing_lean": missing}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Build semantic-review input by pairing original JSON entries with generated Lean files."
    )
    parser.add_argument(
        "--input-json",
        required=True,
        help="Path to original input JSON (non-preprocessed source).",
    )
    parser.add_argument(
        "--lean-dir",
        default=None,
        help="Directory containing generated .lean files. Default: lean/LeanProject/<input-stem>",
    )
    parser.add_argument(
        "--out",
        default=None,
        help="Output JSON path. Default: review_log/<input-stem>_review.json",
    )
    return parser.parse_args()


def main() -> None:
    args = _parse_args()

    project_root = Path(__file__).resolve().parents[2]
    input_json = Path(args.input_json).expanduser().resolve()
    if not input_json.exists():
        raise FileNotFoundError(f"Input JSON not found: {input_json}")

    if args.lean_dir:
        lean_dir = Path(args.lean_dir).expanduser().resolve()
    else:
        lean_dir = (project_root / "lean" / "LeanProject" / _safe_label(input_json.stem)).resolve()

    out_path = (
        Path(args.out).expanduser().resolve()
        if args.out
        else _default_output_path(project_root, input_json).resolve()
    )
    rows = build_review_input_rows(input_json, lean_dir)
    counters = write_review_json(rows, out_path)
    print(
        f"[review_input] total={counters['total']} matched={counters['matched']} "
        f"missing_lean={counters['missing_lean']}",
        file=sys.stderr,
    )
    print(f"[review_input] output={out_path}", file=sys.stderr)


if __name__ == "__main__":
    main()
