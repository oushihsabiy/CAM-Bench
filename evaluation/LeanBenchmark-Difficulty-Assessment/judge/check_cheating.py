#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""check_cheating.py: 抽样检查通过样本是否含有可疑证明。"""

import argparse
import json
import random
import re
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parents[2]


def check_lean_file(lean_path: Path) -> list[str]:
    issues = []
    try:
        src = lean_path.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return ["[ERROR] cannot read file"]

    if re.search(r"\bsorry\b", src):
        issues.append("CHEAT: contains 'sorry'")

    if re.search(r"\bsorryAx\b", src):
        issues.append("CHEAT: uses 'sorryAx'")

    if re.search(r"\baxiom\b", src):
        axiom_lines = [l.strip() for l in src.splitlines() if "axiom" in l]
        issues.append(f"CHEAT: contains 'axiom': {axiom_lines[:2]}")

    if re.search(r"\bnative_decide\b", src):
        issues.append("WARN: uses 'native_decide'")

    proof_match = re.search(r":=\s*by\s*(.+?)(?:\n\n|$)", src, re.DOTALL)
    if proof_match:
        proof_body = proof_match.group(1).strip()
        if len(proof_body) < 10:
            issues.append(f"WARN: very short proof body: '{proof_body[:50]}'")

    non_empty = [l for l in src.splitlines() if l.strip() and not l.strip().startswith("--")]
    if len(non_empty) <= 5:
        issues.append(f"WARN: very few non-empty lines ({len(non_empty)})")

    return issues if issues else ["OK"]


def main() -> int:
    parser = argparse.ArgumentParser(description="抽样作弊检测")
    parser.add_argument("--log-dir", default=str(PROJECT_ROOT / "LOG"))
    parser.add_argument("--plan", default="plan1_baseline")
    parser.add_argument("--model-contains", default="Goedel")
    parser.add_argument("--sample-size", type=int, default=20)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--max-pass-files", type=int, default=3)
    args = parser.parse_args()

    log_dir = Path(args.log_dir).resolve()
    if not log_dir.exists():
        raise FileNotFoundError(f"Log dir not found: {log_dir}")

    passed_dirs = []
    for cfg_f in log_dir.rglob("config.json"):
        try:
            cfg = json.loads(cfg_f.read_text(encoding="utf-8"))
        except Exception:
            continue

        if cfg.get("plan") != args.plan:
            continue
        if args.model_contains not in cfg.get("model", ""):
            continue

        sum_f = cfg_f.parent / "summary.json"
        if not sum_f.exists():
            continue

        try:
            summary = json.loads(sum_f.read_text(encoding="utf-8"))
        except Exception:
            continue

        if int(summary.get("passed_count", 0)) > 0:
            passed_dirs.append((cfg_f.parent, cfg, summary))

    print(f"Total matched passed experiments: {len(passed_dirs)}")
    if not passed_dirs:
        return 0

    random.seed(args.seed)
    sample = random.sample(passed_dirs, min(args.sample_size, len(passed_dirs)))

    print(f"\nSampling {len(sample)} experiments for cheat detection...")
    print("=" * 80)

    cheat_count = 0
    warn_count = 0
    ok_count = 0

    for exp_dir, cfg, summary in sorted(sample, key=lambda x: str(x[0])):
        prob_path = Path(cfg.get("problem", cfg.get("local_problem", "")))
        prob = prob_path.stem
        domain = prob_path.parent.name
        passed = int(summary.get("passed_count", 0))
        pass_n = int(summary.get("pass_n", 32))

        pass_files = sorted(exp_dir.glob("pass_*.lean"))
        ok_files = []
        for lf in pass_files:
            rf = lf.with_name(lf.stem + "_result.txt")
            if rf.exists():
                rtxt = rf.read_text(encoding="utf-8", errors="ignore")
                if "returncode: 0" in rtxt or "SUCCESS" in rtxt.upper():
                    ok_files.append(lf)

        if not ok_files:
            ok_files = pass_files[: args.max_pass_files]

        print(f"\n[{exp_dir.name}]")
        print(f"  Problem: {domain}/{prob}, passed={passed}/{pass_n}")

        if not ok_files:
            print("  WARNING: no pass files found")
            continue

        exp_issues = []
        for lf in ok_files[: args.max_pass_files]:
            issues = check_lean_file(lf)
            for issue in issues:
                if issue != "OK":
                    exp_issues.append(f"{lf.name}: {issue}")

        if any("CHEAT" in issue for issue in exp_issues):
            print("  *** CHEAT DETECTED ***")
            for issue in exp_issues:
                print(f"    {issue}")
            cheat_count += 1
        elif exp_issues:
            print("  WARNINGS:")
            for issue in exp_issues:
                print(f"    {issue}")
            warn_count += 1
        else:
            print("  OK - no cheating detected")
            ok_count += 1

    print(f"\n{'=' * 80}")
    print(f"SUMMARY: {ok_count} OK, {warn_count} WARN, {cheat_count} CHEAT (out of {len(sample)} sampled)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
