"""Structured compile-error logging.

Every compile attempt is recorded as a JSON entry appended to a per-Lean-file
log.  The log directory defaults to ``logs/compile_errors/``.

Log file layout::

    logs/compile_errors/<lean_filename>.jsonl

Each line is a JSON object:

    {
        "timestamp": "2026-04-16T12:00:00Z",
        "lean_file": "ch5.lean",
        "returncode": 1,
        "num_errors": 2,
        "num_warnings": 1,
        "errors": [ ... ],
        "warnings": [ ... ],
        "run_label": "translate_block_3"
    }
"""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List


_DEFAULT_LOG_DIR = Path("logs/compile_errors")


def log_compile_result(
    *,
    lean_file: str | Path,
    returncode: int,
    errors: List[Dict[str, Any]],
    warnings: List[Dict[str, Any]],
    run_label: str = "",
    log_dir: str | Path | None = None,
) -> Path:
    """Append a structured compile-result entry to the per-file log.

    Returns the path of the log file written to.
    """
    log_root = Path(log_dir) if log_dir else _DEFAULT_LOG_DIR
    log_root.mkdir(parents=True, exist_ok=True)

    lean_name = Path(lean_file).stem
    log_path = log_root / f"{lean_name}.jsonl"

    entry: Dict[str, Any] = {
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "lean_file": str(Path(lean_file).name),
        "returncode": returncode,
        "num_errors": len(errors),
        "num_warnings": len(warnings),
        "errors": errors,
        "warnings": warnings,
    }
    if run_label:
        entry["run_label"] = run_label

    with open(log_path, "a", encoding="utf-8") as fh:
        fh.write(json.dumps(entry, ensure_ascii=False) + "\n")

    return log_path


def read_compile_logs(log_dir: str | Path | None = None) -> List[Dict[str, Any]]:
    """Read all compile-error log entries from the log directory."""
    log_root = Path(log_dir) if log_dir else _DEFAULT_LOG_DIR
    entries: List[Dict[str, Any]] = []
    if not log_root.exists():
        return entries
    for log_file in sorted(log_root.glob("*.jsonl")):
        for line in log_file.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if not line:
                continue
            try:
                entries.append(json.loads(line))
            except json.JSONDecodeError:
                continue
    return entries
