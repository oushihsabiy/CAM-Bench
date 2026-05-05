#!/usr/bin/env python3
"""Reporting helpers for informal proof generation."""

from __future__ import annotations

import csv
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def write_json(path: str | Path, payload: Any) -> None:
    p = Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def build_run_report(results: list[dict[str, Any]]) -> dict[str, Any]:
    total_tasks = len(results)
    total_attempts = sum(len(r.get("attempts", [])) for r in results)
    successful_attempts = sum(
        1 for r in results for a in r.get("attempts", []) if a.get("status") == "success"
    )
    completed_tasks = sum(1 for r in results if r.get("generated_at_n"))

    per_model: dict[str, dict[str, Any]] = {}
    for result in results:
        model = str(result.get("model", "unknown"))
        row = per_model.setdefault(
            model,
            {"tasks": 0, "completed_tasks": 0, "attempts": 0, "successful_attempts": 0},
        )
        row["tasks"] += 1
        row["completed_tasks"] += int(bool(result.get("generated_at_n")))
        attempts = result.get("attempts", [])
        row["attempts"] += len(attempts)
        row["successful_attempts"] += sum(1 for a in attempts if a.get("status") == "success")

    for row in per_model.values():
        row["generation_success_rate"] = (
            row["successful_attempts"] / row["attempts"] if row["attempts"] else 0.0
        )
        row["task_generated_at_n_rate"] = (
            row["completed_tasks"] / row["tasks"] if row["tasks"] else 0.0
        )

    return {
        "generated_at": utc_now(),
        "correctness_status": "ungraded",
        "total_tasks": total_tasks,
        "completed_tasks": completed_tasks,
        "task_generated_at_n_rate": completed_tasks / total_tasks if total_tasks else 0.0,
        "total_attempts": total_attempts,
        "successful_attempts": successful_attempts,
        "generation_success_rate": successful_attempts / total_attempts if total_attempts else 0.0,
        "per_model": per_model,
        "problems": results,
    }


def write_report_csv(path: str | Path, results: list[dict[str, Any]]) -> None:
    p = Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(
            [
                "chapter_stem",
                "problem_id",
                "model",
                "pass_index",
                "retry_index",
                "status",
                "proof_file",
                "error",
                "elapsed_sec",
                "total_tokens",
            ]
        )
        for result in results:
            for attempt in result.get("attempts", []):
                writer.writerow(
                    [
                        result.get("chapter_stem", ""),
                        result.get("problem_id", ""),
                        result.get("model", ""),
                        attempt.get("pass_index", ""),
                        attempt.get("retry_index", ""),
                        attempt.get("status", ""),
                        attempt.get("proof_file", ""),
                        attempt.get("error", ""),
                        attempt.get("elapsed_sec", ""),
                        attempt.get("total_tokens", ""),
                    ]
                )
