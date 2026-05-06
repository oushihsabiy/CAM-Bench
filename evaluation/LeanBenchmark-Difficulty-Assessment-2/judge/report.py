#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""report.py: 按 plan/model/domain 聚合 passed/N 统计。"""

import argparse
import json
from collections import defaultdict
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parents[2]


def main() -> int:
    parser = argparse.ArgumentParser(description="汇总实验结果")
    parser.add_argument("--log-dir", default=str(PROJECT_ROOT / "LOG"))
    args = parser.parse_args()

    log_dir = Path(args.log_dir).resolve()
    if not log_dir.exists():
        raise FileNotFoundError(f"Log dir not found: {log_dir}")

    # plan -> model -> category -> [passed_sum, total_sum, n_probs]
    stats = defaultdict(lambda: defaultdict(lambda: defaultdict(lambda: [0, 0, 0])))

    for d in log_dir.iterdir():
        if not d.is_dir() or d.name.startswith("_sbatch"):
            continue

        sum_f = d / "summary.json"
        cfg_f = d / "config.json"
        if not (sum_f.exists() and cfg_f.exists()):
            continue

        try:
            summary = json.loads(sum_f.read_text(encoding="utf-8"))
            cfg = json.loads(cfg_f.read_text(encoding="utf-8"))
        except Exception:
            continue

        plan = cfg.get("plan", "?")
        model = str(cfg.get("model", "")).split("/")[-1]
        prob_path = Path(cfg.get("problem", cfg.get("local_problem", "")))

        parts = prob_path.parts
        try:
            bi = parts.index("Benchmark")
            category = parts[bi + 1]
        except Exception:
            category = "Unknown"

        passed = int(summary.get("passed_count", 0))
        total = int(summary.get("pass_n", 32))

        rec = stats[plan][model][category]
        rec[0] += passed
        rec[1] += total
        rec[2] += 1

    categories = ["Convex_Analysis", "High_dim_Probability", "Numerical_Algebra", "Optimization"]

    for plan in sorted(stats.keys()):
        print(f"\n{'=' * 90}")
        print(f"  {plan}")
        print(f"{'=' * 90}")
        print(f"{'Model':<30} {'Category':<25} {'#Prob':>6} {'Passed/N':>12} {'Rate':>7}")
        print("-" * 82)

        for model in sorted(stats[plan].keys()):
            totals = [0, 0, 0]
            model_stats = stats[plan][model]

            ordered_cats = categories + sorted(c for c in model_stats.keys() if c not in categories)
            for cat in ordered_cats:
                v = model_stats.get(cat, [0, 0, 0])
                rate = (v[0] / v[1] * 100) if v[1] > 0 else 0
                print(f"{model:<30} {cat:<25} {v[2]:>6} {v[0]:>6}/{v[1]:<5} {rate:>6.1f}%")
                totals[0] += v[0]
                totals[1] += v[1]
                totals[2] += v[2]

            total_rate = (totals[0] / totals[1] * 100) if totals[1] > 0 else 0
            print(f"{model:<30} {'[TOTAL]':<25} {totals[2]:>6} {totals[0]:>6}/{totals[1]:<5} {total_rate:>6.1f}%")
            print()

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
