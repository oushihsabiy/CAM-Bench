#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""plan12_results.py: 统计 plan1/plan2 的 clean pass@N 结果。"""

import argparse
import json
import re
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parents[2]


def get_prob_key(prob_str: str) -> str:
    p = Path(prob_str)
    parts = p.parts
    for i, part in enumerate(parts):
        if part == "Benchmark" and i + 2 < len(parts):
            return f"{parts[i + 1]}/{p.stem}"
    return f"{p.parent.name}/{p.stem}"


def is_clean(lean_file: Path) -> bool:
    try:
        src = lean_file.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return False
    if re.search(r"\bsorry\b", src):
        return False
    if re.search(r"\baxiom\b", src):
        return False
    if not re.search(r"\b(theorem|lemma)\b", src):
        return False
    if not re.search(r"\b(by|:=)\b", src):
        return False
    non_empty = [l for l in src.splitlines() if l.strip() and not l.strip().startswith("--")]
    return len(non_empty) >= 5


def count_clean(exp_dir: Path, summary: dict) -> int:
    details = summary.get("details", [])
    cnt = 0
    for d in details:
        if not d.get("passed"):
            continue
        lf = exp_dir / f"pass_{d['pass_idx']:03d}.lean"
        if lf.exists() and is_clean(lf):
            cnt += 1
    return cnt


def collect_best(log_dir: Path, plans: set[str]) -> dict:
    best = {}
    for cfg_f in log_dir.rglob("config.json"):
        try:
            cfg = json.loads(cfg_f.read_text(encoding="utf-8"))
        except Exception:
            continue

        plan = cfg.get("plan", "")
        if plan not in plans:
            continue

        sum_f = cfg_f.parent / "summary.json"
        if not sum_f.exists():
            continue

        try:
            summary = json.loads(sum_f.read_text(encoding="utf-8"))
        except Exception:
            continue

        model = str(cfg.get("model", "")).split("/")[-1]
        if "qwen" in model.lower() or "gpt" in model.lower():
            continue

        prob = cfg.get("problem", cfg.get("local_problem", ""))
        prob_key = get_prob_key(prob)
        key = (plan, model, prob_key)

        clean = count_clean(cfg_f.parent, summary)
        if key not in best or clean > best[key][1]:
            best[key] = (cfg_f.parent, clean)
    return best


def main() -> int:
    parser = argparse.ArgumentParser(description="统计 plan1/plan2 clean pass@N")
    parser.add_argument("--log-dir", default=str(PROJECT_ROOT / "LOG"))
    parser.add_argument("--benchmark", default=str(PROJECT_ROOT / "Benchmark"))
    parser.add_argument("--plans", default="plan1_baseline,plan2_rag")
    parser.add_argument("--models", default="Goedel-Prover-V2-32B,Kimina-Prover-72B")
    args = parser.parse_args()

    log_dir = Path(args.log_dir).resolve()
    benchmark = Path(args.benchmark).resolve()
    plans = [p.strip() for p in args.plans.split(",") if p.strip()]
    models = [m.strip() for m in args.models.split(",") if m.strip()]

    if not log_dir.exists():
        raise FileNotFoundError(f"Log dir not found: {log_dir}")
    if not benchmark.exists():
        raise FileNotFoundError(f"Benchmark dir not found: {benchmark}")

    domains = sorted([d.name for d in benchmark.iterdir() if d.is_dir()])
    best = collect_best(log_dir, set(plans))

    for plan in plans:
        print(f"\n{'=' * 72}")
        print(f"  {plan}  (clean pass@N, strict no sorry/axiom)")
        print(f"{'=' * 72}")

        if len(models) >= 2:
            print(f"{'Domain':<28} {models[0]:>10} {'Rate':>7}  {models[1]:>10} {'Rate':>7}")
        else:
            print(f"{'Domain':<28} {'Passed':>10} {'Rate':>7}")
        print("-" * 70)

        totals = {model: [0, 0] for model in models}

        for domain in domains:
            total_problems = sum(1 for _ in (benchmark / domain).glob("*.lean"))
            row = [f"{domain:<28}"]
            for model in models:
                clean_passed = 0
                for p in (benchmark / domain).glob("*.lean"):
                    key = (plan, model, f"{domain}/{p.stem}")
                    if key in best and best[key][1] > 0:
                        clean_passed += 1

                rate = (clean_passed / total_problems * 100) if total_problems else 0
                row.append(f"{clean_passed:>10} {rate:>6.1f}%")
                totals[model][0] += clean_passed
                totals[model][1] += total_problems

            if len(models) >= 2:
                print(f"{row[0]} {row[1]}  {row[2]}")
            else:
                print(f"{row[0]} {row[1]}")

        print("-" * 70)
        total_row = [f"{'[TOTAL]':<28}"]
        for model in models:
            passed, total = totals[model]
            rate = (passed / total * 100) if total else 0
            total_row.append(f"{passed:>10} {rate:>6.1f}%")

        if len(models) >= 2:
            print(f"{total_row[0]} {total_row[1]}  {total_row[2]}")
        else:
            print(f"{total_row[0]} {total_row[1]}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
