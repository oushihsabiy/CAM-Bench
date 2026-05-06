#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""show_results.py: 列出实验 summary 概览，可按时间戳过滤。"""

import argparse
import json
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parents[2]


def main() -> int:
    parser = argparse.ArgumentParser(description="显示实验结果")
    parser.add_argument("--log-dir", default=str(PROJECT_ROOT / "LOG"))
    parser.add_argument("--after", default=None, help="仅显示目录名 >= 该时间戳前缀")
    args = parser.parse_args()

    log_dir = Path(args.log_dir).resolve()
    if not log_dir.exists():
        raise FileNotFoundError(f"Log dir not found: {log_dir}")

    results = []
    for d in sorted(log_dir.iterdir()):
        if not d.is_dir() or d.name.startswith("_sbatch"):
            continue
        if args.after and d.name < args.after:
            continue

        sum_f = d / "summary.json"
        if not sum_f.exists():
            continue

        try:
            summary = json.loads(sum_f.read_text(encoding="utf-8"))
        except Exception:
            continue

        model = str(summary.get("model", "")).split("/")[-1]
        problem = Path(summary.get("problem", d.name)).name
        parts = d.name.split("_", 2)
        tag = parts[2] if len(parts) > 2 else d.name
        results.append(
            (
                model,
                tag,
                problem,
                int(summary.get("passed_count", 0)),
                int(summary.get("pass_n", 32)),
                bool(summary.get("pass_at_n", False)),
            )
        )

    if not results:
        print("No results found.")
        return 0

    print(f"{'Model':35s} {'Plan+Problem':40s} {'Passed':>8} {'pass@N':>8}")
    print("-" * 95)
    for model, tag, problem, passed, total, patn in results:
        print(f"{model:35s} {tag:40s} {passed:>5}/{total:<3} {str(patn):>8}")

    print(f"\nTotal: {len(results)} experiments")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
