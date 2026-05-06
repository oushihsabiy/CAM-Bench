#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""submit_rerun_sorry.py: 提交重跑实验（每个实验一个 SLURM job）。"""

import argparse
import json
import os
import shlex
import subprocess
from datetime import datetime
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_BATCH_RUNNER = PROJECT_ROOT / "code_clean" / "submit" / "run_batch.py"
DEFAULT_EXP_RUNNER = PROJECT_ROOT / "code" / "run_experiment.py"
DEFAULT_CONFIG = PROJECT_ROOT / "experiments_rerun_sorry.json"

SLURM_TEMPLATE = """#!/bin/bash
#SBATCH --job-name={job_name}
#SBATCH --partition={partition}
#SBATCH --ntasks=1
#SBATCH --cpus-per-task={cpus}
#SBATCH --mem={mem}
#SBATCH --time={time_limit}
#SBATCH --output={work_dir}/slurm_logs/{job_name}_%j.log

set -euo pipefail

export https_proxy=\"http://login01:7890\"
export http_proxy=\"http://login01:7890\"
export HTTPS_PROXY=\"http://login01:7890\"
export HTTP_PROXY=\"http://login01:7890\"

source /public/software/apps/anaconda/etc/profile.d/conda.sh
conda activate lean-codex-cli

export PYTHONUNBUFFERED=1

cd {work_dir}
python {batch_runner} {batch_file} --runner {exp_runner} --work-dir {work_dir}
"""


def short_tags(exp: dict) -> tuple[str, str, str]:
    plan = str(exp.get("plan", ""))
    model = str(exp.get("model", ""))
    prob = Path(exp.get("problem", "unknown")).stem

    plan_tag = "p1" if "plan1" in plan else "p2" if "plan2" in plan else "px"
    if "Goedel" in model:
        model_tag = "g"
    elif "Kimina" in model:
        model_tag = "k"
    else:
        model_tag = "m"

    return plan_tag, model_tag, prob


def main() -> int:
    parser = argparse.ArgumentParser(description="提交 only-sorry 重跑实验")
    parser.add_argument("--config", default=str(DEFAULT_CONFIG), help="重跑实验配置 JSON")
    parser.add_argument("--work-dir", default=str(PROJECT_ROOT))
    parser.add_argument("--batch-runner", default=str(DEFAULT_BATCH_RUNNER))
    parser.add_argument("--exp-runner", default=str(DEFAULT_EXP_RUNNER))
    parser.add_argument("--partition", default="AMD")
    parser.add_argument("--cpus", type=int, default=8)
    parser.add_argument("--mem", default="16G")
    parser.add_argument("--time-limit", default="03:00:00")
    parser.add_argument("--slurm-bin", default="/opt/gridview/slurm/bin")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    work_dir = Path(args.work_dir).resolve()
    config_file = Path(args.config).resolve()
    batch_runner = Path(args.batch_runner).resolve()
    exp_runner = Path(args.exp_runner).resolve()
    slurm_bin = Path(args.slurm_bin).resolve()

    if not config_file.exists():
        raise FileNotFoundError(f"Config not found: {config_file}")
    if not batch_runner.exists():
        raise FileNotFoundError(f"Batch runner not found: {batch_runner}")
    if not exp_runner.exists():
        raise FileNotFoundError(f"Experiment runner not found: {exp_runner}")

    exps = json.loads(config_file.read_text(encoding="utf-8"))
    print(f"Total to rerun: {len(exps)}")
    if not exps:
        return 0

    slurm_logs = work_dir / "slurm_logs"
    slurm_logs.mkdir(parents=True, exist_ok=True)

    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    batch_dir = work_dir / "LOG" / f"_sbatch_{ts}_rerun_sorry"
    batch_dir.mkdir(parents=True, exist_ok=True)

    env = os.environ.copy()
    env["PATH"] = str(slurm_bin) + ":" + env.get("PATH", "")

    for idx, exp in enumerate(exps):
        batch_file = batch_dir / f"batch_rerun_sorry_{idx:03d}.json"
        batch_file.write_text(json.dumps([exp], ensure_ascii=False, indent=2), encoding="utf-8")

        plan_tag, model_tag, prob = short_tags(exp)
        job_name = f"re_{plan_tag}{model_tag}_{idx:03d}"

        script = SLURM_TEMPLATE.format(
            job_name=job_name,
            partition=args.partition,
            cpus=args.cpus,
            mem=args.mem,
            time_limit=args.time_limit,
            work_dir=str(work_dir),
            batch_runner=shlex.quote(str(batch_runner)),
            exp_runner=shlex.quote(str(exp_runner)),
            batch_file=shlex.quote(str(batch_file)),
        )
        script_path = batch_dir / f"{job_name}.sh"
        script_path.write_text(script, encoding="utf-8")

        if args.dry_run:
            print(f"[DryRun] {idx:03d} {plan_tag}/{model_tag} {prob}: {script_path}")
            continue

        r = subprocess.run(["sbatch", str(script_path)], capture_output=True, text=True, env=env)
        print(f"{idx:03d} {plan_tag}/{model_tag} {prob}: {r.stdout.strip()} {r.stderr.strip()}")

    print("Done.")
    print(f"Batch scripts in: {batch_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
