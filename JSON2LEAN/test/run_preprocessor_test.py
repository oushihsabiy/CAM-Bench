#!/usr/bin/env python3
"""Test harness for json2lean preprocessor.

This script runs preprocessor.preprocess_all() with APIClient configured by
config.json and writes results to test/preprocessor_output.json.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from datetime import datetime

# Allow direct execution without requiring editable install.
REPO_ROOT = Path(__file__).resolve().parents[1]
SRC_DIR = REPO_ROOT / "src"
if str(SRC_DIR) not in sys.path:
    sys.path.insert(0, str(SRC_DIR))

# Import package modules after ensuring `src/` is on sys.path so the
# package can be imported when running the test script directly.
from json2lean.config.api_client import APIClient
from json2lean.loader import load_config
from json2lean.models import Exercise
from json2lean.preprocess import preprocess_all


def load_problem_lookup() -> dict[str, str]:
    picks_path = REPO_ROOT / "data" / "picks.json"
    data = json.loads(picks_path.read_text(encoding="utf-8"))
    if not isinstance(data, list):
        raise ValueError("data/picks.json must be a JSON array")

    lookup: dict[str, str] = {}
    for item in data:
        if not isinstance(item, dict):
            continue
        content = item.get("content", item)
        if not isinstance(content, dict):
            continue

        problem = content.get("problem") or content.get("题目内容") or ""
        if not problem:
            continue

        candidate_keys = [
            content.get("source_idx"),
            content.get("题目ID"),
            content.get("index"),
        ]
        for key in candidate_keys:
            if key is not None:
                lookup[str(key)] = problem

    return lookup


def load_exercise_from_picks(source_idx: str) -> dict | None:
    """Load a single exercise entry from data/picks.json by source_idx."""
    picks_path = REPO_ROOT / "data" / "picks.json"
    data = json.loads(picks_path.read_text(encoding="utf-8"))
    if not isinstance(data, list):
        return None
    for item in data:
        if not isinstance(item, dict):
            continue
        content = item.get("content", item)
        if isinstance(content, dict) and content.get("source_idx") == source_idx:
            return item
    return None


def build_exercises(items: list[dict]) -> list[Exercise]:
    """Build Exercise objects from input data, extracting 'content' if present."""
    exercises: list[Exercise] = []
    for i, obj in enumerate(items, 1):
        # If the object has a 'content' field, use that as the raw data; otherwise use the object itself
        raw = obj.get("content", obj) if isinstance(obj, dict) else obj
        exercises.append(Exercise(raw=dict(raw), index=i))
    return exercises


def get_original_problem(exercise: Exercise, lookup: dict[str, str]) -> str:
    keys = [
        exercise.label,
        exercise.raw.get("source_idx"),
        exercise.raw.get("题目ID"),
        exercise.raw.get("index"),
    ]
    for key in keys:
        if key is None:
            continue
        problem = lookup.get(str(key))
        if problem:
            return problem
    return ""


def print_exercise_detail(ex: Exercise, lookup: dict[str, str]) -> None:
    """Print detailed output for a single exercise."""
    print(f"\n{'='*70}")
    print(f"Exercise: {ex.label}")
    print(f"{'='*70}")

    orig = get_original_problem(ex, lookup)
    print(f"\n--- Original Problem ---\n{orig[:500]}{'...' if len(orig) > 500 else ''}")

    if ex.preprocessed_problem:
        print(f"\n--- Preprocessed Problem ---\n{ex.preprocessed_problem}")

    if ex.structured:
        print(f"\n--- Structured Blocks ---")
        for b in ex.structured.blocks:
            tag = f"[{b.kind}]"
            text_preview = b.text[:120] + ("..." if len(b.text) > 120 else "")
            print(f"  {tag:16s} id={b.id:16s} {text_preview}")

        # Highlight definition ordering
        defs = ex.structured.get_blocks_by_kind("definition")
        if defs:
            print(f"\n--- Definition Order ({len(defs)} blocks) ---")
            for i, d in enumerate(defs):
                is_placeholder = d.id.startswith("ph_")
                marker = " [FROM PLACEHOLDER]" if is_placeholder else ""
                text_preview = d.text[:100] + ("..." if len(d.text) > 100 else "")
                print(f"  {i+1}. id={d.id}{marker}")
                print(f"     {text_preview}")
    print()


def main() -> None:
    input_path = REPO_ROOT / "test" / "preprocessor_input.json"
    output_path = REPO_ROOT / "test" / "preprocessor_output.json"

    data = json.loads(input_path.read_text(encoding="utf-8"))
    if not isinstance(data, list):
        raise ValueError("test/preprocessor_input.json must be a JSON array")

    # Ensure Exercise 19.2-(b) is in the test data
    has_19_2b = any(
        (obj.get("content", obj) if isinstance(obj, dict) else {}).get("source_idx") == "Exercise 19.2-(b)"
        for obj in data
    )
    if not has_19_2b:
        entry = load_exercise_from_picks("Exercise 19.2-(b)")
        if entry:
            data.append(entry)
            print("Auto-added Exercise 19.2-(b) from picks.json")

    exercises = build_exercises(data)
    problem_lookup = load_problem_lookup()

    cfg = load_config()
    client = APIClient(cfg.api_key, cfg.base_url, cfg.model, timeout=cfg.timeout_seconds)
    max_tokens = cfg.preprocessing_max_tokens
    max_attempts = cfg.preprocessing_max_attempts
    failed = preprocess_all(client, exercises, max_tokens=max_tokens, max_attempts=max_attempts)

    # ---------- print details ----------
    for ex in exercises:
        print_exercise_detail(ex, problem_lookup)

    # ---------- write output ----------
    result = {
        "failed_labels": failed,
        "results": [
            {
                "label": ex.label,
                "problem_before": get_original_problem(ex, problem_lookup),
                "preprocessed_problem": ex.preprocessed_problem,
                "structured": {
                    "index": ex.structured.index,
                    "source_document": ex.structured.source_document,
                    "blocks": [
                        {"id": b.id, "kind": b.kind, "text": b.text}
                        for b in ex.structured.blocks
                    ],
                } if ex.structured else None,
            }
            for idx, ex in enumerate(exercises)
        ],
    }

    output_path.write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"Wrote: {output_path}")
    logs_dir = REPO_ROOT / "logs"
    logs_dir.mkdir(parents=True, exist_ok=True)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    usage_calls = client.dump_usage()
    totals = client.total_usage()
    token_log = {
        "timestamp": ts,
        "total": totals,
        "calls": usage_calls,
    }
    log_path = logs_dir / f"token_usage_{ts}.json"
    log_path.write_text(json.dumps(token_log, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"Wrote token usage log: {log_path}")
    print(f"Failed labels: {failed}")


if __name__ == "__main__":
    main()
