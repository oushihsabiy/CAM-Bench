#!/usr/bin/env python3
"""Utilities for pruning completed tasks from task.json."""

from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any

from .problem_loader import task_key


def load_tasks(task_path: str | Path) -> list[dict[str, Any]]:
    data = json.loads(Path(task_path).read_text(encoding="utf-8"))
    if isinstance(data, dict):
        tasks = data.get("tasks", data.get("experiments", []))
    else:
        tasks = data
    if not isinstance(tasks, list):
        raise ValueError(f"task file must contain a list or object with tasks: {task_path}")
    return [t for t in tasks if isinstance(t, dict)]


def completed_keys_from_output(output_root: str | Path) -> set[str]:
    """Scan output_root for summary.json files with generated_at_n=true."""
    root = Path(output_root)
    keys: set[str] = set()
    if not root.exists():
        return keys
    for summary_path in root.glob("**/summary.json"):
        try:
            summary = json.loads(summary_path.read_text(encoding="utf-8"))
        except Exception:
            continue
        if not isinstance(summary, dict) or not summary.get("generated_at_n"):
            continue
        chapter_path = summary.get("chapter_path")
        problem_id = summary.get("problem_id")
        model = summary.get("model")
        if chapter_path and problem_id and model:
            keys.add(task_key(chapter_path, problem_id, model))
    return keys


def task_completion_key(task: dict[str, Any]) -> str:
    return task_key(task.get("chapter_path"), task.get("problem_id"), task.get("model"))


def prune_task_file(
    task_path: str | Path,
    completed_keys: set[str],
    *,
    backup: bool = True,
) -> tuple[int, int, int]:
    """Remove completed task entries from task_path.

    Returns (before_count, removed_count, after_count).
    """
    path = Path(task_path)
    if not path.exists() or not completed_keys:
        tasks = load_tasks(path) if path.exists() else []
        return len(tasks), 0, len(tasks)

    original = json.loads(path.read_text(encoding="utf-8"))
    if isinstance(original, dict):
        task_list = original.get("tasks", original.get("experiments", []))
        if not isinstance(task_list, list):
            raise ValueError(f"task file object has no task list: {path}")
    elif isinstance(original, list):
        task_list = original
    else:
        raise ValueError(f"task file must contain a list or object: {path}")

    before = len(task_list)
    kept = [
        task
        for task in task_list
        if not isinstance(task, dict) or task_completion_key(task) not in completed_keys
    ]
    removed = before - len(kept)
    if removed <= 0:
        return before, 0, before

    if backup:
        backup_path = path.with_suffix(path.suffix + ".bak")
        if not backup_path.exists():
            backup_path.write_text(path.read_text(encoding="utf-8"), encoding="utf-8")

    if isinstance(original, dict):
        if "tasks" in original:
            original["tasks"] = kept
        else:
            original["experiments"] = kept
        payload = original
    else:
        payload = kept

    tmp_path = path.with_suffix(path.suffix + ".tmp")
    tmp_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    os.replace(tmp_path, path)
    return before, removed, len(kept)

