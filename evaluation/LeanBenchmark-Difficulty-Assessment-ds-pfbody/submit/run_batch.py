#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""run_batch.py: 顺序执行一个实验批次 JSON。"""

import argparse
import json
import subprocess
import sys
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_RUNNER = PROJECT_ROOT / "code" / "run_experiment.py"


def build_cmd(exp: dict, runner: Path) -> list[str]:
    cmd = [sys.executable, str(runner)]
    for key in ["plan", "problem", "base_url", "model", "lean_cwd"]:
        if key in exp:
            cmd += ["--" + key.replace("_", "-"), str(exp[key])]

    optional = {
        "pass_n": "--pass-n",
        "workers": "--workers",
        "backend": "--backend",
        "max_iter": "--max-iter",
        "max_turns": "--max-turns",
        "api_key": "--api-key",
    }
    for key, flag in optional.items():
        if exp.get(key) is not None:
            cmd += [flag, str(exp[key])]

    if exp.get("no_rag"):
        cmd.append("--no-rag")
    if exp.get("robust"):
        cmd.append("--robust")
    return cmd


def main() -> int:
    parser = argparse.ArgumentParser(description="顺序执行批量实验")
    parser.add_argument("config", help="批次实验配置 JSON")
    parser.add_argument(
        "--runner",
        default=str(DEFAULT_RUNNER),
        help="run_experiment.py 路径",
    )
    parser.add_argument(
        "--work-dir",
        default=str(PROJECT_ROOT),
        help="子进程执行目录（默认项目根目录）",
    )
    args = parser.parse_args()

    config_file = Path(args.config).resolve()
    runner = Path(args.runner).resolve()
    work_dir = Path(args.work_dir).resolve()

    if not config_file.exists():
        raise FileNotFoundError(f"Config not found: {config_file}")
    if not runner.exists():
        raise FileNotFoundError(f"Runner not found: {runner}")

    exps = json.loads(config_file.read_text(encoding="utf-8"))
    print(f"[Batch] {len(exps)} experiments from {config_file}")

    for i, exp in enumerate(exps, start=1):
        cmd = build_cmd(exp, runner)
        plan = exp.get("plan", "?")
        problem = Path(exp.get("problem", "unknown")).stem
        model = str(exp.get("model", "?")).split("/")[-1]

        print(f"\n[Batch {i}/{len(exps)}] {plan} / {problem} / {model}")
        r = subprocess.run(cmd, cwd=str(work_dir))
        if r.returncode != 0:
            print(f"[Batch] WARNING: rc={r.returncode} for {plan} / {problem}")

    print(f"\n[Batch] DONE all {len(exps)} experiments")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
