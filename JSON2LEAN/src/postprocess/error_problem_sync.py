"""Sync realtime failure events into error_problem/errors.json."""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple


_LABEL_TAIL_RE = re.compile(r"^(?P<src>.+)_(?P<kind>[A-Za-z_]+)_(?P<idx>\d+)$")
_CHAPTER_RE = re.compile(r"chp(?P<num>\d+(?:-\d+)?)", re.IGNORECASE)


def _to_int(value: Any) -> Optional[int]:
    try:
        if value is None:
            return None
        return int(value)
    except (TypeError, ValueError):
        return None


def _read_jsonl(path: Path) -> List[Dict[str, Any]]:
    if not path.exists():
        return []
    rows: List[Dict[str, Any]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        text = line.strip()
        if not text:
            continue
        try:
            row = json.loads(text)
        except json.JSONDecodeError:
            continue
        if isinstance(row, dict):
            rows.append(row)
    return rows


def _read_json_array(path: Path) -> List[Dict[str, Any]]:
    if not path.exists():
        return []
    text = path.read_text(encoding="utf-8").strip()
    if not text:
        return []
    try:
        payload = json.loads(text)
    except json.JSONDecodeError:
        return []
    if isinstance(payload, list):
        return [it for it in payload if isinstance(it, dict)]
    if isinstance(payload, dict) and isinstance(payload.get("exercises"), list):
        return [it for it in payload["exercises"] if isinstance(it, dict)]
    return []


def _write_json_array(path: Path, rows: Sequence[Dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    data = list(rows)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _normalize_text(text: str) -> str:
    return re.sub(r"\W+", "", str(text or "").strip().lower())


def _source_base(source_idx: str) -> str:
    return re.sub(r"\s*-\([^)]+\)\s*$", "", str(source_idx or "").strip())


def _stable_record_key(record: Dict[str, Any]) -> str:
    source_idx = str(record.get("source_idx") or "").strip()
    problem = str(record.get("problem") or "").strip()
    source = str(record.get("source") or "").strip()
    idx = _to_int(record.get("index"))
    if source_idx and problem:
        return f"srcprob::{_normalize_text(source_idx)}::{_normalize_text(problem)}"
    if source_idx and idx is not None:
        return f"srcidx::{_normalize_text(source_idx)}::{idx}"
    if source and idx is not None:
        return f"fileidx::{_normalize_text(source)}::{idx}"
    return "json::" + json.dumps(record, ensure_ascii=False, sort_keys=True)


def _chapter_hints(lean_stem: str) -> List[str]:
    stem = str(lean_stem or "").strip().lower()
    if not stem:
        return []
    hints = {stem}
    match = _CHAPTER_RE.search(stem)
    if match:
        chapter = match.group("num")
        hints.add(f"ch{chapter}")
        hints.add(f"chp{chapter}")
        hints.add(f"convex_optimization_chp{chapter}")
    return sorted(hints)


def _candidate_data_files(data_dir: Path, lean_file: str) -> List[Path]:
    all_files = sorted(data_dir.glob("*.json"))
    if not all_files:
        return []
    stem = Path(str(lean_file or "").strip()).stem
    if not stem:
        return all_files

    stem_lower = stem.lower()
    exact = [p for p in all_files if p.stem.lower() == stem_lower]
    if exact:
        return exact

    hints = _chapter_hints(stem)
    fuzzy = [p for p in all_files if any(h in p.stem.lower() for h in hints)]
    if fuzzy:
        return fuzzy
    return all_files


def _extract_from_block_id(block_id: str) -> Tuple[str, Optional[int], str]:
    text = str(block_id or "").strip()
    if not text:
        return "", None, ""
    parts = [p.strip() for p in text.split("|", 2)]
    if len(parts) != 3:
        return "", None, ""
    source_idx = parts[0]
    idx = _to_int(parts[1])
    kind = parts[2].lower()
    return source_idx, idx, kind


def _extract_match_context(event: Dict[str, Any]) -> Dict[str, Any]:
    ctx: Dict[str, Any] = {
        "event": str(event.get("event") or "").strip(),
        "timestamp": str(event.get("timestamp") or "").strip(),
        "lean_file": str(event.get("lean_file") or "").strip(),
        "label": "",
        "source_idx": "",
        "index": None,
        "kind": "",
        "block_id": "",
    }

    exercise = event.get("exercise") if isinstance(event.get("exercise"), dict) else {}
    payload = event.get("payload") if isinstance(event.get("payload"), dict) else {}

    if exercise:
        ctx["label"] = str(exercise.get("label") or "").strip()
        ctx["source_idx"] = str(exercise.get("source_idx") or "").strip()
        ctx["index"] = _to_int(exercise.get("index"))
        ctx["kind"] = str(exercise.get("kind") or "").strip().lower()
    elif payload:
        ctx["label"] = str(payload.get("label") or "").strip()
        ctx["block_id"] = str(payload.get("block_id") or "").strip()
        source_idx, idx, kind = _extract_from_block_id(ctx["block_id"])
        if source_idx:
            ctx["source_idx"] = source_idx
        if idx is not None:
            ctx["index"] = idx
        if kind:
            ctx["kind"] = kind

    if (not ctx["source_idx"] or not ctx["kind"] or ctx["index"] is None) and ctx["label"]:
        match = _LABEL_TAIL_RE.match(str(ctx["label"]))
        if match:
            if not ctx["source_idx"]:
                ctx["source_idx"] = str(match.group("src") or "").strip()
            if not ctx["kind"]:
                ctx["kind"] = str(match.group("kind") or "").strip().lower()
            if ctx["index"] is None:
                ctx["index"] = _to_int(match.group("idx"))

    return ctx


def _find_record(records: Sequence[Dict[str, Any]], ctx: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    source_idx = str(ctx.get("source_idx") or "").strip()
    idx = _to_int(ctx.get("index"))

    if not records:
        return None

    if source_idx:
        exact = [r for r in records if str(r.get("source_idx") or "").strip() == source_idx]
        if len(exact) == 1:
            return exact[0]
        if len(exact) > 1 and idx is not None:
            for row in exact:
                if _to_int(row.get("index")) == idx:
                    return row
            return exact[0]

        normalized_source = _normalize_text(source_idx)
        normalized_hits = [
            r
            for r in records
            if _normalize_text(str(r.get("source_idx") or "")) == normalized_source
        ]
        if len(normalized_hits) == 1:
            return normalized_hits[0]
        if len(normalized_hits) > 1 and idx is not None:
            for row in normalized_hits:
                if _to_int(row.get("index")) == idx:
                    return row

        source_base = _source_base(source_idx)
        if source_base:
            base_hits = []
            norm_base = _normalize_text(source_base)
            for row in records:
                row_source = str(row.get("source_idx") or "").strip()
                if not row_source:
                    continue
                if _normalize_text(_source_base(row_source)) == norm_base:
                    base_hits.append(row)
            if len(base_hits) == 1:
                return base_hits[0]
            if len(base_hits) > 1 and idx is not None:
                for row in base_hits:
                    if _to_int(row.get("index")) == idx:
                        return row
                return base_hits[0]

    if idx is not None:
        for row in records:
            if _to_int(row.get("index")) == idx:
                return row

    return None


def sync_realtime_failures_to_errors(
    *,
    report_dir: str | Path,
    data_dir: str | Path,
    errors_json_path: str | Path,
) -> Dict[str, int]:
    """Sync realtime failure events into ``error_problem/errors.json``.

    Returns summary counters:
    - total_events: parsed event count
    - matched_records: events resolved to source records
    - inserted_records: new records appended to errors.json
    - skipped_existing: records already present
    - unmatched_events: events that could not be resolved
    """

    report_dir = Path(report_dir)
    data_dir = Path(data_dir)
    errors_json_path = Path(errors_json_path)
    realtime_path = report_dir / "realtime_failures.jsonl"

    events = _read_jsonl(realtime_path)
    existing = _read_json_array(errors_json_path)
    existing_keys = {_stable_record_key(row) for row in existing}

    matched_records = 0
    inserted_records = 0
    skipped_existing = 0
    unmatched_events = 0

    data_cache: Dict[Path, List[Dict[str, Any]]] = {}

    def _records_for(path: Path) -> List[Dict[str, Any]]:
        if path not in data_cache:
            data_cache[path] = _read_json_array(path)
        return data_cache[path]

    all_data_files = sorted(data_dir.glob("*.json"))

    for event in events:
        ctx = _extract_match_context(event)
        candidates = _candidate_data_files(data_dir, str(ctx.get("lean_file") or ""))
        resolved: Optional[Dict[str, Any]] = None

        for data_file in candidates:
            resolved = _find_record(_records_for(data_file), ctx)
            if resolved is not None:
                break

        if resolved is None:
            for data_file in all_data_files:
                if data_file in candidates:
                    continue
                resolved = _find_record(_records_for(data_file), ctx)
                if resolved is not None:
                    break

        if resolved is None:
            unmatched_events += 1
            continue

        matched_records += 1
        key = _stable_record_key(resolved)
        if key in existing_keys:
            skipped_existing += 1
            continue

        existing.append(resolved)
        existing_keys.add(key)
        inserted_records += 1

    _write_json_array(errors_json_path, existing)

    return {
        "total_events": len(events),
        "matched_records": matched_records,
        "inserted_records": inserted_records,
        "skipped_existing": skipped_existing,
        "unmatched_events": unmatched_events,
    }


def truncate_realtime_failures(report_dir: str | Path) -> bool:
    """Truncate realtime failure report file to empty content.

    Returns ``True`` when truncation happened, ``False`` when file is absent.
    """

    path = Path(report_dir) / "realtime_failures.jsonl"
    if not path.exists():
        return False
    path.write_text("", encoding="utf-8")
    return True
