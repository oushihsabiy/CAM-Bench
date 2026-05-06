#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
run_difficulty.py: 三阶段 Lean 题目难度评级 Pipeline 主入口。

用法：
  # 完整三阶段（需已有 eval_report.json 和 LOG 中的证明）
  python -m eval.run_difficulty \
    --config eval/task.json \
    --eval-report eval/eval_report.json \
    --log-dir LOG/ \
    --output eval/difficulty_report.json \
    --judge-model gpt-5.4 \
    --judge-base-url https://api-vip.codex-for.me/v1 \
    --judge-api-key <key>

  # 只跑先验阶段
  python -m eval.run_difficulty \
    --config eval/task.json \
    --stage prior \
    --judge-model gpt-5.4 \
    --judge-base-url https://api-vip.codex-for.me/v1

  # dry-run 预览
  python -m eval.run_difficulty --config eval/task.json --dry-run
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

# 支持 python -m eval.run_difficulty 和直接运行两种方式
if __name__ == "__main__" and __package__ is None:
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    __package__ = "eval"

from .difficulty_aggregator import aggregate
from .evaluator import ProblemMetrics, compute_raw_actual_score
from .llm_client import ModelConfig
from .posterior_scorer import PosteriorScore, score_posterior, _collect_proof_code
from .prior_scorer import PriorScore, score_prior
from .problem_loader import load_problem
from .reporter import print_difficulty_report, save_difficulty_excel, save_difficulty_report


PROJECT_ROOT = Path(__file__).resolve().parents[1]


# ---------------------------------------------------------------------------
# 从 eval_report.json 还原 ProblemMetrics（轻量版，不含 SolveResult）
# ---------------------------------------------------------------------------


def _canonical_problem_path(raw_path: str, lean_cwd: str | None = None) -> str:
    """将题目路径规范化为尽可能稳定的绝对路径字符串。"""
    p = Path(raw_path)
    if not p.is_absolute() and lean_cwd:
        p = Path(lean_cwd) / p
    return str(p.resolve(strict=False))

def _load_eval_report(report_path: Path) -> dict[str, ProblemMetrics]:
    """从已有 eval_report.json 还原 ProblemMetrics（仅聚合指标）。"""
    data = json.loads(report_path.read_text(encoding="utf-8"))
    result: dict[str, ProblemMetrics] = {}
    for p in data.get("problems", []):
        pm = ProblemMetrics(
            problem_path=p["problem"],
            total_blocks=p.get("total_blocks", 0),
        )
        pm.pass_rate = p.get("pass_rate", 0.0)
        pm.block_pass_rate = p.get("block_pass_rate", 0.0)
        pm.avg_turns_to_pass = p.get("avg_turns_to_pass", 0.0)
        pm.max_turns_to_pass = p.get("max_turns_to_pass", 0)
        pm.avg_time_sec = p.get("avg_time_sec", 0.0)
        pm.max_time_sec = p.get("max_time_sec", 0.0)
        pm.error_diversity = p.get("error_diversity", 0)
        pm.avg_proof_length = p.get("avg_proof_length", 0.0)
        pm.model_pass_rates = p.get("model_pass_rates", {})
        pm.model_gap = p.get("model_gap", 0.0)
        pm.difficulty_score = p.get("difficulty_score", 0.0)
        pm.difficulty_level = p.get("difficulty_level", "Unknown")
        # 同时保留原始键和规范化键，尽量兼容不同脚本输出的路径风格。
        result[pm.problem_path] = pm
        result[_canonical_problem_path(pm.problem_path)] = pm
    return result


# ---------------------------------------------------------------------------
# 解析 task.json 获取去重的题目列表
# ---------------------------------------------------------------------------

def _unique_problems(exps: list[dict], default_lean_cwd: str | None) -> list[str]:
    """从实验配置中提取去重的题目路径列表。"""
    seen: set[str] = set()
    problems: list[str] = []
    for exp in exps:
        lean_cwd = exp.get("lean_cwd", default_lean_cwd)
        ps = _canonical_problem_path(exp["problem"], lean_cwd)
        if ps not in seen:
            seen.add(ps)
            problems.append(ps)
    return problems


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(
        description="三阶段 Lean 题目难度评级 Pipeline",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("--config", required=True, help="实验配置 JSON（复用现有格式）")
    parser.add_argument("--eval-report", default=None, help="已有 eval_report.json（跳过实际求解）")
    parser.add_argument("--log-dir", default=str(PROJECT_ROOT / "LOG"), help="LOG 目录")
    parser.add_argument("--output", default=str(PROJECT_ROOT / "eval" / "difficulty_report.json"),
                        help="输出报告路径")
    parser.add_argument("--excel-output", default=None, help="Excel 输出路径（默认与 --output 同名 .xlsx）")
    parser.add_argument("--lean-cwd", default=None, help="Lean 工作目录")
    parser.add_argument("--max-turns", type=int, default=5, help="最大修复轮数（实际阶段用）")

    # LLM judge 配置
    parser.add_argument("--judge-model", default=None, help="LLM 评分模型名")
    parser.add_argument("--judge-base-url", default=None, help="LLM 评分 API base URL")
    parser.add_argument("--judge-api-key", default=None, help="LLM 评分 API key")
    parser.add_argument("--judge-temperature", type=float, default=0.3, help="LLM 评分温度")

    parser.add_argument("--stage", default="prior,actual,posterior",
                        help="运行哪些阶段（逗号分隔，默认 prior,actual,posterior）")
    parser.add_argument("--parallel", type=int, default=1, help="并发题目数")
    parser.add_argument("--dry-run", action="store_true", help="只打印计划")

    # 权重覆盖
    parser.add_argument("--stage-weights", default=None, help="三阶段权重 JSON 文件")
    args = parser.parse_args()

    stages = {s.strip() for s in args.stage.split(",")}
    config_file = Path(args.config).resolve()
    log_dir = Path(args.log_dir).resolve()
    output_file = Path(args.output).resolve()
    excel_output_file = (
        Path(args.excel_output).resolve() if args.excel_output else output_file.with_suffix(".xlsx")
    )

    if not config_file.exists():
        print(f"[Difficulty] ERROR: config not found: {config_file}", file=sys.stderr)
        return 1

    exps = json.loads(config_file.read_text(encoding="utf-8"))
    problems = _unique_problems(exps, args.lean_cwd)

    print(f"[Difficulty] Config: {config_file} ({len(problems)} unique problems)")
    print(f"[Difficulty] Stages: {', '.join(sorted(stages))}")
    print(f"[Difficulty] Log dir: {log_dir}")
    print(f"[Difficulty] Output: {output_file}")
    print(f"[Difficulty] Excel : {excel_output_file}")

    # --- 加载三阶段权重 ---
    stage_weights = None
    if args.stage_weights:
        sw_path = Path(args.stage_weights)
        if sw_path.exists():
            stage_weights = json.loads(sw_path.read_text(encoding="utf-8"))
            print(f"[Difficulty] Stage weights: {stage_weights}")

    # --- 构建 judge LLM 配置 ---
    judge_cfg: ModelConfig | None = None
    if args.judge_model and args.judge_base_url:
        judge_cfg = ModelConfig(
            model=args.judge_model,
            base_url=args.judge_base_url,
            api_key=args.judge_api_key or "EMPTY",
            temperature=args.judge_temperature,
            max_tokens=2048,
            stream=bool(getattr(args, "judge_stream", False)),
        )
    elif ("prior" in stages or "posterior" in stages):
        # 尝试从 task.json 第一个实验获取 LLM 配置
        if exps:
            first = exps[0]
            judge_cfg = ModelConfig(
                model=first["model"],
                base_url=first["base_url"],
                api_key=first.get("api_key", "EMPTY"),
                temperature=args.judge_temperature,
                max_tokens=2048,
                stream=bool(first.get("stream", False)),
            )
            print(f"[Difficulty] Using model from config: {judge_cfg.model}")

    if ("prior" in stages or "posterior" in stages) and judge_cfg is None:
        print("[Difficulty] ERROR: --judge-model and --judge-base-url required for prior/posterior stages",
              file=sys.stderr)
        return 1

    if args.dry_run:
        print(f"\n[Difficulty] DRY-RUN: would process {len(problems)} problems")
        for p in problems:
            print(f"  - {Path(p).stem}")
        return 0

    t0 = time.monotonic()

    # ================================================================
    # Phase A: 先验评分
    # ================================================================
    prior_scores: list[PriorScore] = []
    if "prior" in stages:
        print(f"\n[Difficulty] === Phase A: Prior Scoring ({len(problems)} problems) ===")
        for prob_path in problems:
            print(f"  [Prior] {Path(prob_path).stem} ...", end=" ", flush=True)
            try:
                problem = load_problem(prob_path)
            except FileNotFoundError:
                print(f"SKIP (file not found)")
                prior_scores.append(PriorScore(problem_path=prob_path))
                continue

            if problem.total_sorry_count == 0:
                print(f"SKIP (no sorry)")
                prior_scores.append(PriorScore(problem_path=prob_path))
                continue

            ps = score_prior(problem, judge_cfg)
            prior_scores.append(ps)
            print(f"raw={ps.raw_score:.3f} struct={ps.structural_complexity} "
                  f"concept={ps.concept_complexity} formal={ps.formalization_gap} "
                  f"type={ps.type_sophistication}")
    else:
        # 占位
        prior_scores = [PriorScore(problem_path=p) for p in problems]
        print("[Difficulty] Skipping prior stage")

    # ================================================================
    # Phase B: 实际证明难度
    # ================================================================
    actual_raw_scores: list[tuple[str, float, dict]] = []
    if "actual" in stages:
        print(f"\n[Difficulty] === Phase B: Actual Proof Difficulty ===")

        if args.eval_report:
            report_path = Path(args.eval_report).resolve()
            if not report_path.exists():
                print(f"[Difficulty] WARNING: eval_report not found: {report_path}, skipping actual stage")
                actual_raw_scores = [(p, 0.0, {}) for p in problems]
            else:
                print(f"  Loading eval report: {report_path}")
                pm_map = _load_eval_report(report_path)
                missing_count = 0
                for prob_path in problems:
                    pm = pm_map.get(prob_path)
                    if pm is None:
                        pm = pm_map.get(_canonical_problem_path(prob_path))
                    if pm is None:
                        print(f"  [Actual] {Path(prob_path).stem}: NOT FOUND in report")
                        actual_raw_scores.append((prob_path, 0.0, {}))
                        missing_count += 1
                    else:
                        raw, dims = compute_raw_actual_score(pm, max_turns=args.max_turns)
                        print(f"  [Actual] {Path(prob_path).stem}: raw={raw:.3f}")
                        actual_raw_scores.append((prob_path, raw, dims))

                if missing_count:
                    print(
                        f"  [Actual] WARNING: {missing_count}/{len(problems)} problems "
                        "missing in eval_report -> raw score fallback to 0."
                    )
        else:
            print("  [Actual] No --eval-report provided; using zero scores. "
                  "Run eval/run_eval.py first to generate eval_report.json.")
            actual_raw_scores = [(p, 0.0, {}) for p in problems]
    else:
        actual_raw_scores = [(p, 0.0, {}) for p in problems]
        print("[Difficulty] Skipping actual stage")

    # ================================================================
    # Phase C: 后验评分
    # ================================================================
    posterior_scores: list[PosteriorScore] = []
    if "posterior" in stages:
        print(f"\n[Difficulty] === Phase C: Posterior Scoring ===")

        for prob_path in problems:
            print(f"  [Post] {Path(prob_path).stem} ...", end=" ", flush=True)

            proof_code = _collect_proof_code(prob_path, log_dir)
            if proof_code is None:
                print("SKIP (no proof in LOG)")
                posterior_scores.append(PosteriorScore(problem_path=prob_path))
                continue

            ps = score_posterior(prob_path, proof_code, judge_cfg)
            posterior_scores.append(ps)
            print(f"raw={ps.raw_score:.3f} struct={ps.structure} sem={ps.semantic} "
                  f"lib={ps.library} type={ps.type_score} search={ps.search}")
    else:
        posterior_scores = [PosteriorScore(problem_path=p) for p in problems]
        print("[Difficulty] Skipping posterior stage")

    # ================================================================
    # Phase D: 聚合 + Rank-based Normalization
    # ================================================================
    print(f"\n[Difficulty] === Phase D: Aggregation ===")
    results = aggregate(
        prior_scores, actual_raw_scores, posterior_scores,
        stage_weights=stage_weights,
    )

    total_time = time.monotonic() - t0

    # ================================================================
    # Phase E: 输出
    # ================================================================
    print_difficulty_report(results)
    save_difficulty_report(results, output_file, stage_weights=stage_weights)
    save_difficulty_excel(results, excel_output_file, stage_weights=stage_weights)
    print(f"[Difficulty] Report saved to {output_file}")
    print(f"[Difficulty] Excel  saved to {excel_output_file}")
    print(f"[Difficulty] Total time: {total_time:.1f}s")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
