#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""submit_batches_socks.py: 通过 SOCKS 隧道提交批量实验。"""

import argparse
import json
import math
import os
import shlex
import subprocess
from datetime import datetime
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_BATCH_RUNNER = Path(__file__).resolve().parent / "run_batch.py"
DEFAULT_EXP_RUNNER = PROJECT_ROOT / "code" / "run_experiment.py"

SLURM_TEMPLATE = """#!/bin/bash
#SBATCH -J {job_name}
#SBATCH -p AMD
#SBATCH -N 1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=8
#SBATCH --mem=32G
#SBATCH -t {hours}:00:00
#SBATCH -D {work_dir}
#SBATCH -o {work_dir}/LOG/slurm_{job_name}_%j.out
#SBATCH -e {work_dir}/LOG/slurm_{job_name}_%j.err

set -euo pipefail

SOCKS_PORT=$((18100 + RANDOM % 800))
ssh -fN -D ${{SOCKS_PORT}} -o StrictHostKeyChecking=no -o ConnectTimeout=10 login01
export https_proxy=\"socks5h://127.0.0.1:${{SOCKS_PORT}}\"
export http_proxy=\"socks5h://127.0.0.1:${{SOCKS_PORT}}\"
export HTTPS_PROXY=\"socks5h://127.0.0.1:${{SOCKS_PORT}}\"
export HTTP_PROXY=\"socks5h://127.0.0.1:${{SOCKS_PORT}}\"
echo "[SOCKS] tunnel on port ${{SOCKS_PORT}}"

source /public/software/apps/anaconda/etc/profile.d/conda.sh
conda activate lean-codex-cli

export PYTHONUNBUFFERED=1

python {batch_runner} {batch_file} --runner {exp_runner} --work-dir {work_dir}
"""


def main() -> int:
    parser = argparse.ArgumentParser(description="批量提交（SOCKS 版）")
    parser.add_argument("--config", required=True)
    parser.add_argument("--n-jobs", type=int, required=True)
    parser.add_argument("--hours", type=int, default=10)
    parser.add_argument("--tag", default="batch")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--work-dir", default=str(PROJECT_ROOT))
    parser.add_argument("--batch-runner", default=str(DEFAULT_BATCH_RUNNER))
    parser.add_argument("--exp-runner", default=str(DEFAULT_EXP_RUNNER))
    parser.add_argument("--slurm-bin", default="/opt/gridview/slurm/bin")
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
    n = len(exps)
    chunk = math.ceil(n / args.n_jobs)
    print(f"[Submit-SOCKS] {n} experiments -> {args.n_jobs} jobs, ~{chunk} per job")

    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    batch_dir = work_dir / "LOG" / f"_sbatch_{ts}_{args.tag}"
    batch_dir.mkdir(parents=True, exist_ok=True)

    env = os.environ.copy()
    env["PATH"] = str(slurm_bin) + ":" + env.get("PATH", "")

    for i in range(args.n_jobs):
        chunk_exps = exps[i * chunk : (i + 1) * chunk]
        if not chunk_exps:
            continue

        batch_file = batch_dir / f"batch_{i:03d}.json"
        batch_file.write_text(json.dumps(chunk_exps, ensure_ascii=False, indent=2), encoding="utf-8")

        job_name = f"{args.tag}_{i:03d}"
        script = SLURM_TEMPLATE.format(
            job_name=job_name,
            hours=args.hours,
            work_dir=str(work_dir),
            batch_runner=shlex.quote(str(batch_runner)),
            exp_runner=shlex.quote(str(exp_runner)),
            batch_file=shlex.quote(str(batch_file)),
        )
        script_path = batch_dir / f"{job_name}.sh"
        script_path.write_text(script, encoding="utf-8")

        if args.dry_run:
            print(f"[DryRun] {job_name}: {len(chunk_exps)} exps")
            continue

        r = subprocess.run(["sbatch", str(script_path)], capture_output=True, text=True, env=env)
        if r.returncode != 0:
            print(f"[ERROR] {job_name}: {r.stderr.strip()}")
        else:
            job_id = r.stdout.strip().split()[-1]
            print(f"[SLURM] {job_name} ({len(chunk_exps)} exps) -> Job {job_id}")

    print(f"[Submit-SOCKS] Done. Batch files in {batch_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
