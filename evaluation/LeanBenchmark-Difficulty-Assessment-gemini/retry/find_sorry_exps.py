#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""find_sorry_exps.py: 查找 only-sorry 通过实验并生成重跑配置。"""

import argparse
import json
import re
from collections import Counter, defaultdict
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_MODEL_CONFIGS = {
    "Goedel-Prover-V2-32B": {
        "model": "/public_hw/home/ias_zwwen/lcy/Benchmark/Goedel-Prover-V2-32B",
        "base_url": "http://172.18.103.1:8000/v1",
        "workers": 2,
    },
    "Kimina-Prover-72B": {
        "model": "/public_hw/home/ias_zwwen/lcy/Benchmark/Kimina-Prover-72B",
        "base_url": "http://172.18.103.2:8000/v1",
        "workers": 2,
    },
}


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
    return not re.search(r"\bsorry\b", src) and not re.search(r"\baxiom\b", src)


def count_clean(exp_dir: Path, summary: dict) -> int:
    details = summary.get("details", [])
    clean = 0
    for detail in details:
        if not detail.get("passed", False):
            continue
        lf = exp_dir / f"pass_{detail['pass_idx']:03d}.lean"
        if lf.exists() and is_clean(lf):
            clean += 1
    return clean


def load_model_config(model_cfg_file: Path | None) -> dict:
    if model_cfg_file is None:
        return DEFAULT_MODEL_CONFIGS
    return json.loads(model_cfg_file.read_text(encoding="utf-8"))


def main() -> int:
    parser = argparse.ArgumentParser(description="生成 only-sorry 重跑实验列表")
    parser.add_argument("--log-dir", default=str(PROJECT_ROOT / "LOG"))
    parser.add_argument("--benchmark", default=str(PROJECT_ROOT / "Benchmark"))
    parser.add_argument("--plans", default="plan1_baseline,plan2_rag")
    parser.add_argument("--exclude-model-regex", default="(?i)(qwen|gpt)")
    parser.add_argument("--lean-cwd", default="/public/home/ias_zwwen/wzy/LeanAgent2603")
    parser.add_argument("--pass-n", type=int, default=32)
    parser.add_argument("--default-workers", type=int, default=2)
    parser.add_argument("--backend", default="loogle")
    parser.add_argument("--model-config", default=None, help="模型映射 JSON 文件")
    parser.add_argument("--output", default=str(PROJECT_ROOT / "experiments_rerun_sorry.json"))
    args = parser.parse_args()

    log_dir = Path(args.log_dir).resolve()
    benchmark = Path(args.benchmark).resolve()
    output = Path(args.output).resolve()
    plans = {p.strip() for p in args.plans.split(",") if p.strip()}
    exclude_pat = re.compile(args.exclude_model_regex)

    if not log_dir.exists():
        raise FileNotFoundError(f"Log dir not found: {log_dir}")
    if not benchmark.exists():
        raise FileNotFoundError(f"Benchmark dir not found: {benchmark}")

    model_cfg_file = Path(args.model_config).resolve() if args.model_config else None
    model_configs = load_model_config(model_cfg_file)

    bench_by_key: dict[str, Path] = {}
    for p in benchmark.rglob("*.lean"):
        key = f"{p.parent.name}/{p.stem}"
        bench_by_key[key] = p

    sorry_exps = defaultdict(list)  # (plan, model_short, prob_key) -> [(exp_dir, cfg)]

    for cfg_f in log_dir.rglob("config.json"):
        try:
            cfg = json.loads(cfg_f.read_text(encoding="utf-8"))
        except Exception:
            continue

        sum_f = cfg_f.parent / "summary.json"
        if not sum_f.exists():
            continue
        try:
            summary = json.loads(sum_f.read_text(encoding="utf-8"))
        except Exception:
            continue

        plan = cfg.get("plan", "")
        if plan not in plans:
            continue

        model_short = str(cfg.get("model", "")).split("/")[-1]
        if exclude_pat.search(model_short):
            continue

        if summary.get("passed_count", 0) == 0:
            continue

        clean = count_clean(cfg_f.parent, summary)
        if clean > 0:
            continue

        prob = cfg.get("problem", cfg.get("local_problem", ""))
        prob_key = get_prob_key(prob)
        sorry_exps[(plan, model_short, prob_key)].append((cfg_f.parent, cfg))

    print(f"Problems with only-sorry passes: {len(sorry_exps)}")
    by_model = Counter((plan, model) for plan, model, _ in sorry_exps)
    for (plan, model), cnt in sorted(by_model.items()):
        print(f"  {plan} / {model}: {cnt}")

    rerun = []
    missing_benchmark = 0

    for (plan, model_short, prob_key), exps in sorted(sorry_exps.items()):
        bench_file = bench_by_key.get(prob_key)
        if bench_file is None:
            missing_benchmark += 1
            continue

        first_cfg = exps[0][1]
        mcfg = model_configs.get(model_short, {})
        model = mcfg.get("model", first_cfg.get("model", ""))
        base_url = mcfg.get("base_url", first_cfg.get("base_url", ""))
        workers = int(mcfg.get("workers", first_cfg.get("workers", args.default_workers)))

        rerun.append(
            {
                "plan": plan,
                "problem": str(bench_file),
                "base_url": base_url,
                "model": model,
                "lean_cwd": args.lean_cwd,
                "pass_n": args.pass_n,
                "workers": workers,
                "backend": args.backend,
            }
        )

    output.write_text(json.dumps(rerun, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"Rerun list saved to {output} ({len(rerun)} experiments)")
    if missing_benchmark:
        print(f"Skipped {missing_benchmark} items because benchmark file was not found.")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
