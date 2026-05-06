#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""difficulty_aggregator.py: 三阶段聚合 + rank-based normalization → 最终难度。"""

from __future__ import annotations

from dataclasses import dataclass, field

from .prior_scorer import PriorScore
from .posterior_scorer import PosteriorScore


# ---------------------------------------------------------------------------
# 三阶段权重默认值
# ---------------------------------------------------------------------------

STAGE_WEIGHTS = {
    "prior": 0.20,
    "actual": 0.50,
    "posterior": 0.30,
}

DIFFICULTY_LEVELS = [
    (0.25, "Easy"),
    (0.50, "Medium"),
    (0.75, "Hard"),
    (1.01, "Very Hard"),
]


# ---------------------------------------------------------------------------
# 数据模型
# ---------------------------------------------------------------------------

@dataclass
class DifficultyResult:
    """一道题的最终三阶段难度结果。"""
    problem_path: str

    # 先验
    prior_raw: float = 0.0
    prior_norm: float = 0.0
    prior_dimensions: dict = field(default_factory=dict)

    # 实际
    actual_raw: float = 0.0
    actual_norm: float = 0.0
    actual_dimensions: dict = field(default_factory=dict)

    # 后验
    posterior_raw: float = 0.0
    posterior_norm: float = 0.0
    posterior_dimensions: dict = field(default_factory=dict)

    # 最终
    final_score: float = 0.0
    difficulty_level: str = "Unknown"


# ---------------------------------------------------------------------------
# Rank-based normalization
# ---------------------------------------------------------------------------

def rank_normalize(scores: list[float]) -> list[float]:
    """
    Rank-based percentile normalization → [0, 1]。

    使用 average rank 处理并列。
    单一题目退化为 0.5。
    """
    n = len(scores)
    if n == 0:
        return []
    if n == 1:
        return [0.5]

    # 计算 average rank（1-based）
    indexed = sorted(range(n), key=lambda i: scores[i])
    ranks = [0.0] * n

    i = 0
    while i < n:
        # 找出并列的范围
        j = i + 1
        while j < n and scores[indexed[j]] == scores[indexed[i]]:
            j += 1
        avg_rank = (i + j - 1) / 2.0 + 1.0  # 1-based average rank
        for k in range(i, j):
            ranks[indexed[k]] = avg_rank
        i = j

    # 归一化到 [0, 1]：(rank - 1) / (n - 1)
    return [(r - 1.0) / (n - 1) for r in ranks]


# ---------------------------------------------------------------------------
# 聚合
# ---------------------------------------------------------------------------

def aggregate(
    prior_scores: list[PriorScore],
    actual_raw_scores: list[tuple[str, float, dict]],
    posterior_scores: list[PosteriorScore],
    *,
    stage_weights: dict[str, float] | None = None,
) -> list[DifficultyResult]:
    """
    三阶段聚合 + rank-based normalization → 最终难度。

    Parameters
    ----------
    prior_scores : 先验评分列表
    actual_raw_scores : [(problem_path, raw_score, dimensions_dict), ...]
    posterior_scores : 后验评分列表
    stage_weights : 三阶段权重覆盖

    Returns
    -------
    按 final_score 降序排列的 DifficultyResult 列表
    """
    sw = {**STAGE_WEIGHTS, **(stage_weights or {})}

    # 建立 problem → index 映射（以 prior_scores 的顺序为基准）
    problems = [ps.problem_path for ps in prior_scores]
    prob_idx = {p: i for i, p in enumerate(problems)}
    n = len(problems)

    # --- 收集三个阶段的 raw score ---
    prior_raws = [ps.raw_score for ps in prior_scores]

    actual_map = {p: (s, d) for p, s, d in actual_raw_scores}
    actual_raws = [actual_map.get(p, (0.0, {}))[0] for p in problems]

    post_map = {ps.problem_path: ps for ps in posterior_scores}
    posterior_raws = [post_map[p].raw_score if p in post_map else 0.0 for p in problems]

    # --- Rank-based normalization ---
    prior_norms = rank_normalize(prior_raws)
    actual_norms = rank_normalize(actual_raws)
    posterior_norms = rank_normalize(posterior_raws)

    # --- 合成 ---
    results: list[DifficultyResult] = []
    for i, prob in enumerate(problems):
        dr = DifficultyResult(problem_path=prob)

        # 先验
        ps = prior_scores[i]
        dr.prior_raw = ps.raw_score
        dr.prior_norm = prior_norms[i]
        dr.prior_dimensions = {
            "hypothesis_count": ps.hypothesis_count,
            "sorry_block_count": ps.sorry_block_count,
            "statement_length": ps.statement_length,
            "structural_complexity": ps.structural_complexity,
            "concept_complexity": ps.concept_complexity,
            "formalization_gap": ps.formalization_gap,
            "type_sophistication": ps.type_sophistication,
        }

        # 实际
        a_score, a_dims = actual_map.get(prob, (0.0, {}))
        dr.actual_raw = a_score
        dr.actual_norm = actual_norms[i]
        dr.actual_dimensions = a_dims

        # 后验
        if prob in post_map:
            post = post_map[prob]
            dr.posterior_raw = post.raw_score
            dr.posterior_norm = posterior_norms[i]
            dr.posterior_dimensions = {
                "structure": post.structure,
                "semantic": post.semantic,
                "library": post.library,
                "type": post.type_score,
                "search": post.search,
            }
        else:
            dr.posterior_raw = 0.0
            dr.posterior_norm = posterior_norms[i]
            dr.posterior_dimensions = {}

        # 最终分数
        dr.final_score = (
            sw["prior"] * dr.prior_norm
            + sw["actual"] * dr.actual_norm
            + sw["posterior"] * dr.posterior_norm
        )

        # 难度等级
        for threshold, level in DIFFICULTY_LEVELS:
            if dr.final_score < threshold:
                dr.difficulty_level = level
                break

        results.append(dr)

    results.sort(key=lambda r: -r.final_score)
    return results
