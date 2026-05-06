"""Failure report export.

Collects all failed exercises, groups them by failure type, and writes one
JSON file per type named ``YYYYMMDD_<failure_type>.json``.
"""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List

from json2lean.models import Exercise, ExerciseStatus


_FAILURE_STATUSES = {
    ExerciseStatus.ERROR,
    ExerciseStatus.REPAIR_FAILED,
    ExerciseStatus.UNRECOVERABLE,
}


def _exercise_to_report_entry(ex: Exercise) -> Dict[str, Any]:
    return {
        "label": ex.label,
        "index": ex.index,
        "status": ex.status.value,
        "failure_type": ex.failure_type or "unknown",
        "failure_phase": ex.failure_phase,
        "failure_message": ex.failure_message,
        "failure_exception": ex.failure_exception,
        "errors": ex.errors[:10],
        "warnings": ex.warnings[:5],
        "repair_attempts": ex.repair_attempts,
        "source_idx": (ex.raw or {}).get("source_idx", ""),
        "kind": (ex.raw or {}).get("kind", ""),
    }


def export_failure_reports(
    exercises: List[Exercise],
    output_dir: str | Path,
    *,
    date_str: str | None = None,
) -> List[Path]:
    """Export failure reports grouped by failure type.

    Returns list of written file paths.
    """
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    if date_str is None:
        date_str = datetime.now(timezone.utc).strftime("%Y%m%d")

    failed = [ex for ex in exercises if ex.status in _FAILURE_STATUSES]
    if not failed:
        return []

    # Group by failure type
    groups: Dict[str, List[Dict[str, Any]]] = {}
    for ex in failed:
        ft = ex.failure_type or "unknown"
        groups.setdefault(ft, []).append(_exercise_to_report_entry(ex))

    written: List[Path] = []
    for failure_type, entries in groups.items():
        safe_name = failure_type.replace("/", "_").replace(" ", "_")
        filename = f"{date_str}_{safe_name}.json"
        path = output_dir / filename
        report = {
            "failure_type": failure_type,
            "count": len(entries),
            "generated_at": datetime.now(timezone.utc).isoformat(),
            "exercises": entries,
        }
        path.write_text(
            json.dumps(report, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )
        written.append(path)

    # Also write a combined summary
    summary_path = output_dir / f"{date_str}_summary.json"
    summary = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "total_failed": len(failed),
        "by_type": {ft: len(entries) for ft, entries in groups.items()},
        "by_status": {},
    }
    for ex in failed:
        s = ex.status.value
        summary["by_status"][s] = summary["by_status"].get(s, 0) + 1
    summary_path.write_text(
        json.dumps(summary, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    written.append(summary_path)

    return written


def append_failure_event(
    exercise: Exercise,
    output_dir: str | Path,
    *,
    event: str = "",
    extra: Dict[str, Any] | None = None,
    lean_file: str = "",
) -> Path | None:
    """Append one failure event immediately to a realtime JSONL report.

    Only statuses in ``_FAILURE_STATUSES`` are recorded.
    """
    if exercise.status not in _FAILURE_STATUSES:
        return None

    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    path = output_dir / "realtime_failures.jsonl"

    payload: Dict[str, Any] = {
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "event": event,
        "lean_file": lean_file,
        "exercise": _exercise_to_report_entry(exercise),
    }
    if extra:
        payload["extra"] = extra

    with path.open("a", encoding="utf-8") as f:
        f.write(json.dumps(payload, ensure_ascii=False) + "\n")
    return path


def append_realtime_event(
    output_dir: str | Path,
    *,
    event: str,
    payload: Dict[str, Any],
    lean_file: str = "",
) -> Path:
    """Append a realtime JSONL event without status restrictions."""
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    path = output_dir / "realtime_failures.jsonl"
    data = {
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "event": event,
        "lean_file": lean_file,
        "payload": payload,
    }
    with path.open("a", encoding="utf-8") as f:
        f.write(json.dumps(data, ensure_ascii=False) + "\n")
    return path
