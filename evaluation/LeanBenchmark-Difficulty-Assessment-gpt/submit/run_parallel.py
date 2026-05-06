#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""run_parallel.py: 并行提交实验（SLURM 或本地并发）。"""

import argparse
import json
import os
import shlex
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_RUNNER = PROJECT_ROOT / "code" / "run_experiment.py"

SLURM_TEMPLATE = """#!/bin/bash
#SBATCH -J {job_name}
#SBATCH -p AMD
#SBATCH -N 1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=8
#SBATCH --mem=32G
#SBATCH -t 8:00:00
#SBATCH -D {work_dir}
#SBATCH -o {work_dir}/LOG/slurm_{job_name}_%j.out
#SBATCH -e {work_dir}/LOG/slurm_{job_name}_%j.err

set -euo pipefail

export https_proxy=\"http://login01:7890\"
export http_proxy=\"http://login01:7890\"
export HTTPS_PROXY=\"http://login01:7890\"
export HTTP_PROXY=\"http://login01:7890\"

source /public/software/apps/anaconda/etc/profile.d/conda.sh
conda activate lean-codex-cli

export PYTHONUNBUFFERED=1

python {runner} {args}
"""


def build_args_list(exp: dict) -> list[str]:
    args: list[str] = []
    for key in ["plan", "problem", "base_url", "model", "lean_cwd"]:
        if key in exp:
            args += ["--" + key.replace("_", "-"), str(exp[key])]

    optional = {
        "pass_n": "--pass-n",
        "workers": "--workers",
        "backend": "--backend",
        "max_iter": "--max-iter",
        "max_turns": "--max-turns",
        "nl_url": "--nl-url",
        "lean_url": "--lean-url",
        "api_key": "--api-key",
    }
    for key, flag in optional.items():
        if exp.get(key) is not None:
            args += [flag, str(exp[key])]

    if exp.get("no_rag"):
        args.append("--no-rag")
    if exp.get("robust"):
        args.append("--robust")
    return args


def to_shell_args(args: list[str]) -> str:
    return " ".join(shlex.quote(x) for x in args)


def submit_slurm(
    exp: dict,
    work_dir: Path,
    runner: Path,
    slurm_bin: Path,
    dry_run: bool = False,
) -> str:
    ts = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
    problem_id = Path(exp.get("problem", "unknown")).stem
    plan = exp.get("plan", "plan")
    job_name = f"{plan}_{problem_id}"[:32]

    work_dir.joinpath("LOG").mkdir(parents=True, exist_ok=True)
    script_path = work_dir / "LOG" / f"_sbatch_{ts}_{plan}_{problem_id}.sh"

    args_str = to_shell_args(build_args_list(exp))
    script = SLURM_TEMPLATE.format(
        job_name=job_name,
        work_dir=str(work_dir),
        runner=shlex.quote(str(runner)),
        args=args_str,
    )
    script_path.write_text(script, encoding="utf-8")

    if dry_run:
        print(f"[DryRun] Would submit: {script_path}")
        return "dry-run"

    env = os.environ.copy()
    env["PATH"] = str(slurm_bin) + ":" + env.get("PATH", "")
    r = subprocess.run(["sbatch", str(script_path)], capture_output=True, text=True, env=env)
    if r.returncode != 0:
        print(f"[ERROR] sbatch failed for {job_name}: {r.stderr.strip()}")
        return "error"

    job_id = r.stdout.strip().split()[-1]
    print(f"[SLURM] {job_name} -> Job {job_id}")
    return job_id


def run_local(exp: dict, work_dir: Path, runner: Path) -> dict:
    cmd = [sys.executable, str(runner)] + build_args_list(exp)
    print(f"[Local] Running: {' '.join(shlex.quote(x) for x in cmd)}")
    r = subprocess.run(cmd, cwd=str(work_dir), text=True)
    return {"exp": exp, "returncode": r.returncode}


def main() -> int:
    parser = argparse.ArgumentParser(description="并行提交多个实验")
    parser.add_argument("--config", required=True, help="实验配置 JSON")
    parser.add_argument("--mode", choices=["slurm", "local"], default="slurm")
    parser.add_argument("--workers", type=int, default=2, help="local 模式并发数")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--work-dir", default=str(PROJECT_ROOT), help="项目工作目录")
    parser.add_argument("--runner", default=str(DEFAULT_RUNNER), help="run_experiment.py 路径")
    parser.add_argument("--slurm-bin", default="/opt/gridview/slurm/bin", help="SLURM bin 目录")
    args = parser.parse_args()

    work_dir = Path(args.work_dir).resolve()
    runner = Path(args.runner).resolve()
    slurm_bin = Path(args.slurm_bin).resolve()
    config_file = Path(args.config).resolve()

    if not config_file.exists():
        raise FileNotFoundError(f"Config not found: {config_file}")
    if not runner.exists():
        raise FileNotFoundError(f"Runner not found: {runner}")

    config = json.loads(config_file.read_text(encoding="utf-8"))
    print(f"[Parallel] experiments={len(config)} mode={args.mode}")
    print(f"[Parallel] work_dir={work_dir}")
    print(f"[Parallel] runner={runner}")

    if args.mode == "slurm":
        for exp in config:
            submit_slurm(exp, work_dir, runner, slurm_bin, dry_run=args.dry_run)
        return 0

    with ThreadPoolExecutor(max_workers=args.workers) as executor:
        futs = [executor.submit(run_local, exp, work_dir, runner) for exp in config]
        for fut in as_completed(futs):
            result = fut.result()
            exp = result["exp"]
            rc = result["returncode"]
            status = "OK" if rc == 0 else f"FAIL(rc={rc})"
            print(f"[Local] {exp.get('plan', '?')} / {Path(exp.get('problem', '?')).stem} -> {status}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
