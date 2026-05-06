#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""check_missing.py: 基于 LOG 扫描实验完成状态并输出缺失列表。"""

import argparse
import json
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parents[2]


def exp_key_from_cfg(cfg: dict) -> tuple[str, str, str]:
    plan = cfg.get("plan", "")
    model = str(cfg.get("model", "")).split("/")[-1]
    problem = Path(cfg.get("problem", cfg.get("local_problem", ""))).stem
    return (plan, model, problem)


def main() -> int:
    parser = argparse.ArgumentParser(description="检查缺失实验")
    parser.add_argument("--config", required=True, help="目标实验配置 JSON")
    parser.add_argument("--log-dir", default=str(PROJECT_ROOT / "LOG"))
    parser.add_argument("--ignore-running", action="store_true", help="无 summary 的目录也视为缺失")
    parser.add_argument("--output", default=str(PROJECT_ROOT / "experiments_missing.json"))
    args = parser.parse_args()

    config_file = Path(args.config).resolve()
    log_dir = Path(args.log_dir).resolve()
    output_file = Path(args.output).resolve()

    if not config_file.exists():
        raise FileNotFoundError(f"Config not found: {config_file}")
    if not log_dir.exists():
        raise FileNotFoundError(f"Log dir not found: {log_dir}")

    exps = json.loads(config_file.read_text(encoding="utf-8"))

    completed = set()
    running = set()

    for d in sorted(log_dir.iterdir()):
        if not d.is_dir() or d.name.startswith("_sbatch"):
            continue

        cfg_f = d / "config.json"
        sum_f = d / "summary.json"
        if not cfg_f.exists():
            continue

        try:
            cfg = json.loads(cfg_f.read_text(encoding="utf-8"))
        except Exception:
            continue

        key = exp_key_from_cfg(cfg)
        if sum_f.exists():
            completed.add(key)
        elif not args.ignore_running:
            running.add(key)

    print(f"Completed: {len(completed)}, In-progress: {len(running)}")

    missing = []
    for exp in exps:
        key = exp_key_from_cfg(exp)
        if key not in completed and key not in running:
            missing.append(exp)

    print(f"Not started: {len(missing)} / {len(exps)}")

    if missing:
        output_file.write_text(json.dumps(missing, ensure_ascii=False, indent=2), encoding="utf-8")
        print(f"Written missing list to: {output_file}")
    else:
        print("All done. No missing experiments.")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
