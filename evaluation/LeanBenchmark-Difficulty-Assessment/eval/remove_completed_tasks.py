#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Remove completed experiments from task.json.

The script matches task entries against LOG/**/config.json and summary.json.
Only non-sensitive config fields are used: model and problem.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


PROJECT_ROOT = Path(__file__).resolve().parents[1]


def load_json(path: Path) -> Any | None:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return None


def normalize_problem(problem: object) -> str | None:
    if not problem:
        return None

    value = str(problem)
    for marker in ("/Leanproject/Leanproject/", "Leanproject/Leanproject/"):
        if marker in value:
            return "Leanproject/" + value.split(marker, 1)[1]

    if value.startswith("Leanproject/"):
        return value

    return value


def completed_problems(
    log_dir: Path,
    task_problems: set[str],
    model: str,
    require_all_passed: bool,
) -> set[str]:
    completed: set[str] = set()

    for cfg_path in log_dir.glob("**/config.json"):
        cfg = load_json(cfg_path)
        if not isinstance(cfg, dict):
            continue

        if cfg.get("model") != model:
            continue

        problem = normalize_problem(cfg.get("problem"))
        if problem not in task_problems:
            continue

        summary_path = cfg_path.with_name("summary.json")
        summary = load_json(summary_path)
        if not isinstance(summary, dict):
            continue

        if require_all_passed:
            done = summary.get("all_passed") is True
        else:
            done = summary.get("termination_reason") == "completed"

        if done:
            completed.add(problem)

    return completed


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Delete completed model experiments from task.json."
    )
    parser.add_argument(
        "--task",
        default=str(PROJECT_ROOT / "eval" / "task.json"),
        help="task.json to update",
    )
    parser.add_argument(
        "--log-dir",
        default=str(PROJECT_ROOT / "LOG"),
        help="LOG directory containing run summaries",
    )
    parser.add_argument(
        "--model",
        default="claude-sonnet-4-6",
        help="model name to match in LOG config.json",
    )
    parser.add_argument(
        "--require-all-passed",
        action="store_true",
        help="remove only tasks whose summary.json has all_passed=true",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="print counts without modifying task.json",
    )
    parser.add_argument(
        "--backup",
        action="store_true",
        help="write task.json.bak before modifying task.json",
    )
    args = parser.parse_args()

    task_path = Path(args.task).resolve()
    log_dir = Path(args.log_dir).resolve()

    if not task_path.exists():
        raise FileNotFoundError(f"task.json not found: {task_path}")
    if not log_dir.exists():
        raise FileNotFoundError(f"LOG directory not found: {log_dir}")

    tasks = load_json(task_path)
    if not isinstance(tasks, list):
        raise ValueError(f"task.json must contain a JSON list: {task_path}")

    task_problems = {
        problem
        for task in tasks
        if isinstance(task, dict)
        for problem in [normalize_problem(task.get("problem"))]
        if problem is not None
    }

    done = completed_problems(
        log_dir=log_dir,
        task_problems=task_problems,
        model=args.model,
        require_all_passed=args.require_all_passed,
    )
    kept = [
        task
        for task in tasks
        if not isinstance(task, dict)
        or normalize_problem(task.get("problem")) not in done
    ]

    print(f"task: {task_path}")
    print(f"log_dir: {log_dir}")
    print(f"model: {args.model}")
    print(f"before: {len(tasks)}")
    print(f"completed matched: {len(done)}")
    print(f"after: {len(kept)}")

    if args.dry_run:
        print("dry-run: task.json was not modified")
        return 0

    if args.backup:
        backup_path = task_path.with_suffix(task_path.suffix + ".bak")
        backup_path.write_text(task_path.read_text(encoding="utf-8"), encoding="utf-8")
        print(f"backup: {backup_path}")

    task_path.write_text(
        json.dumps(kept, ensure_ascii=False, indent=4) + "\n",
        encoding="utf-8",
    )
    print("updated task.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
