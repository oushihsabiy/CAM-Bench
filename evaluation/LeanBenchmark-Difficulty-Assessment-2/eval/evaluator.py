#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""evaluator.py: 多模型/多次运行聚合 → 难度系数计算。"""

from __future__ import annotations

import math
from dataclasses import dataclass, field

from .solver import SolveResult


# ---------------------------------------------------------------------------
# 难度权重默认值
# ---------------------------------------------------------------------------

DEFAULT_WEIGHTS = {
    "w_pass_rate": 0.35,      # 通过率越低越难
    "w_avg_turns": 0.25,      # 平均轮数越多越难
    "w_time": 0.10,           # 时间越长越难
    "w_error_diversity": 0.15, # 错误种类越多越难
    "w_model_gap": 0.15,      # 模型差异越大越难
}

DIFFICULTY_LEVELS = [
    (0.25, "Easy"),
    (0.50, "Medium"),
    (0.75, "Hard"),
    (1.01, "Very Hard"),
]


# ---------------------------------------------------------------------------
# 每道题的聚合结果
# ---------------------------------------------------------------------------

@dataclass
class ProblemMetrics:
    """单道题在所有模型/所有 pass 上的聚合指标。"""
    problem_path: str
    total_blocks: int

    # 原始数据
    results: list[SolveResult] = field(default_factory=list)

    # 聚合指标
    pass_rate: float = 0.0           # 所有尝试中 all_passed 的比例
    block_pass_rate: float = 0.0     # 按 block 级别的通过率
    avg_turns_to_pass: float = 0.0   # 成功块的平均首次通过轮次
    max_turns_to_pass: int = 0       # 成功块的最大首次通过轮次
    avg_time_sec: float = 0.0        # 平均解题时间
    max_time_sec: float = 0.0        # 最长解题时间
    total_prompt_tokens: int = 0     # 所有 run 的输入 token 总数
    total_completion_tokens: int = 0 # 所有 run 的输出 token 总数
    total_tokens: int = 0            # 所有 run 的总 token
    avg_tokens: float = 0.0          # 单次 run 平均 token
    max_tokens: int = 0              # 单次 run 最大 token
    error_diversity: int = 0         # 所有尝试中遇到的错误类型种类数
    avg_proof_length: float = 0.0    # 成功证明的平均代码行数
    model_pass_rates: dict[str, float] = field(default_factory=dict)  # 每个模型的通过率
    model_gap: float = 0.0           # 最大模型通过率差

    # 最终难度
    difficulty_score: float = 0.0
    difficulty_level: str = "Unknown"


def compute_metrics(
    problem_path: str,
    solve_results: list[SolveResult],
    *,
    max_turns: int = 5,
    weights: dict[str, float] | None = None,
) -> ProblemMetrics:
    """
    对同一道题的所有求解结果做聚合并计算难度系数。
    """
    w = {**DEFAULT_WEIGHTS, **(weights or {})}
    if not solve_results:
        return ProblemMetrics(problem_path=problem_path, total_blocks=0)

    total_blocks = solve_results[0].total_blocks
    pm = ProblemMetrics(
        problem_path=problem_path,
        total_blocks=total_blocks,
        results=solve_results,
    )

    # --- pass_rate（题目级别）---
    n_all_passed = sum(1 for r in solve_results if r.all_passed)
    pm.pass_rate = n_all_passed / len(solve_results)

    # --- block_pass_rate ---
    total_b = sum(r.total_blocks for r in solve_results)
    passed_b = sum(r.passed_blocks for r in solve_results)
    pm.block_pass_rate = passed_b / total_b if total_b > 0 else 0.0

    # --- avg / max turns ---
    first_turns = []
    for r in solve_results:
        for br in r.block_results:
            if br.passed and br.first_pass_turn > 0:
                first_turns.append(br.first_pass_turn)
    pm.avg_turns_to_pass = (sum(first_turns) / len(first_turns)) if first_turns else max_turns
    pm.max_turns_to_pass = max(first_turns) if first_turns else max_turns

    # --- time ---
    times = [r.total_elapsed_sec for r in solve_results]
    pm.avg_time_sec = sum(times) / len(times) if times else 0.0
    pm.max_time_sec = max(times) if times else 0.0

    # --- token usage ---
    token_totals = [r.total_tokens for r in solve_results]
    pm.total_prompt_tokens = sum(r.prompt_tokens for r in solve_results)
    pm.total_completion_tokens = sum(r.completion_tokens for r in solve_results)
    pm.total_tokens = sum(token_totals)
    pm.avg_tokens = (pm.total_tokens / len(token_totals)) if token_totals else 0.0
    pm.max_tokens = max(token_totals) if token_totals else 0

    # --- error_diversity ---
    all_types: set[str] = set()
    for r in solve_results:
        for br in r.block_results:
            for rec in br.timeline:
                all_types.update(rec.error_types)
    pm.error_diversity = len(all_types)

    # --- proof length ---
    proof_lens = []
    for r in solve_results:
        for br in r.block_results:
            if br.passed:
                proof_lens.append(len(br.final_code.splitlines()))
    pm.avg_proof_length = (sum(proof_lens) / len(proof_lens)) if proof_lens else 0.0

    # --- model gap ---
    from collections import defaultdict
    model_results: dict[str, list[bool]] = defaultdict(list)
    for r in solve_results:
        model_results[r.model].append(r.all_passed)
    for model, bools in model_results.items():
        pm.model_pass_rates[model] = sum(bools) / len(bools)
    rates = list(pm.model_pass_rates.values())
    pm.model_gap = (max(rates) - min(rates)) if len(rates) >= 2 else 0.0

    # --- difficulty score ---
    #  D = w1*(1 - pass_rate) + w2*(avg_turns / max_turns) + w3*time_norm + w4*err_div_norm + w5*model_gap
    turns_norm = pm.avg_turns_to_pass / max_turns if max_turns > 0 else 1.0
    # 时间归一化：用 sigmoid-like 映射，300s 为中位
    time_norm = 1 - math.exp(-pm.avg_time_sec / 300.0)
    err_div_norm = min(pm.error_diversity / 6.0, 1.0)  # 6种以上算满分

    pm.difficulty_score = (
        w["w_pass_rate"] * (1.0 - pm.pass_rate)
        + w["w_avg_turns"] * turns_norm
        + w["w_time"] * time_norm
        + w["w_error_diversity"] * err_div_norm
        + w["w_model_gap"] * pm.model_gap
    )
    pm.difficulty_score = max(0.0, min(1.0, pm.difficulty_score))

    for threshold, level in DIFFICULTY_LEVELS:
        if pm.difficulty_score < threshold:
            pm.difficulty_level = level
            break

    return pm


# ---------------------------------------------------------------------------
# Raw actual score（不截断版本，用于三阶段聚合）
# ---------------------------------------------------------------------------

def compute_raw_actual_score(
    pm: ProblemMetrics,
    *,
    max_turns: int = 5,
    weights: dict[str, float] | None = None,
) -> tuple[float, dict[str, float]]:
    """
    从已计算的 ProblemMetrics 提取实际证明难度 raw score（不做 clamp）。

    Returns
    -------
    (raw_score, dimensions_dict)
    """
    w = {**DEFAULT_WEIGHTS, **(weights or {})}

    turns_norm = pm.avg_turns_to_pass / max_turns if max_turns > 0 else 1.0
    time_norm = 1 - math.exp(-pm.avg_time_sec / 300.0)
    # 不截断：error_diversity / 6.0 可能 > 1.0
    err_div_norm = pm.error_diversity / 6.0

    raw = (
        w["w_pass_rate"] * (1.0 - pm.pass_rate)
        + w["w_avg_turns"] * turns_norm
        + w["w_time"] * time_norm
        + w["w_error_diversity"] * err_div_norm
        + w["w_model_gap"] * pm.model_gap
    )

    dims = {
        "pass_rate_inv": round(1.0 - pm.pass_rate, 4),
        "turns_norm": round(turns_norm, 4),
        "time_norm": round(time_norm, 4),
        "error_div_norm": round(err_div_norm, 4),
        "model_gap": round(pm.model_gap, 4),
    }
    return raw, dims
