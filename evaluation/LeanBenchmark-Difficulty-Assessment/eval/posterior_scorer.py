#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""posterior_scorer.py: 后验难度评分 — 基于完成证明的 LLM 分析。"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path

from .llm_client import ModelConfig, generate_with_usage


# ---------------------------------------------------------------------------
# 后验维度权重默认值
# ---------------------------------------------------------------------------

POSTERIOR_WEIGHTS = {
    "structure": 0.20,
    "semantic": 0.25,
    "library": 0.20,
    "type": 0.15,
    "search": 0.20,
}


# ---------------------------------------------------------------------------
# LLM 评分 Prompt
# ---------------------------------------------------------------------------

_POSTERIOR_SYSTEM_PROMPT = """\
You are an expert Lean 4 formal verification researcher.
Analyze the following COMPLETED Lean 4 proof and rate its complexity.

For each dimension, assign a score from 0 to 4:
0 = trivial / direct / no complexity
1 = low complexity
2 = moderate
3 = high
4 = very high complexity

Dimensions:

- structure (structural complexity):
  0 = single tactic (rfl, simp, exact)
  1 = short linear proof (2-5 tactics, no branching)
  2 = moderate (case splits, simple induction, a few intermediate have/let)
  3 = complex (nested induction, many have/let, significant branching)
  4 = very complex (deep nesting, auxiliary lemmas, intricate tactic orchestration)

- semantic (semantic/insight complexity):
  0 = direct definition unfolding or trivial rewriting
  1 = straightforward application of known results
  2 = requires moderate mathematical insight
  3 = requires non-obvious key idea or clever construction
  4 = requires deep mathematical insight or novel approach

- library (library retrieval complexity):
  0 = only basic automation (simp, ring, omega, norm_num)
  1 = common well-known Mathlib lemmas
  2 = specific Mathlib lemmas requiring moderate search
  3 = obscure or hard-to-find Mathlib results
  4 = combining multiple non-obvious Mathlib results creatively

- type (type and expression complexity):
  0 = simple types (ℕ, ℝ), no coercions
  1 = basic type classes, simple coercions
  2 = moderate (matrices, function spaces, basic dependent types)
  3 = complex interactions (Fin/Subtype, non-trivial coercions, universe issues)
  4 = very complex type reasoning (dependent elimination, universe polymorphism)

- search (proof search complexity):
  0 = deterministic, single obvious path
  1 = small search space, obvious tactic choice
  2 = moderate search, some trial-and-error
  3 = large search space, significant backtracking
  4 = very large search space, extensive exploration needed

IMPORTANT:
- Do NOT give an overall score
- Only score based on the definitions above
- Do NOT compare with other problems
- If the proof contains sorry or is incomplete, score based on the attempted portion and mark search=4

Return ONLY valid JSON (no markdown, no explanation outside JSON):
{"structure": <int>, "semantic": <int>, "library": <int>, "type": <int>, "search": <int>, "reasoning": "<1-2 sentences>"}
"""


# ---------------------------------------------------------------------------
# 数据模型
# ---------------------------------------------------------------------------

@dataclass
class PosteriorScore:
    """一道题的后验难度评分。"""
    problem_path: str

    # LLM 评分维度（0-4）
    structure: int = 0
    semantic: int = 0
    library: int = 0
    type_score: int = 0   # 'type' 是 Python 关键字，字段名用 type_score
    search: int = 0

    # LLM 推理说明
    reasoning: str = ""

    # token 使用统计
    prompt_tokens: int = 0
    completion_tokens: int = 0
    total_tokens: int = 0

    # 加权 raw score
    raw_score: float = 0.0


# ---------------------------------------------------------------------------
# LLM 评分
# ---------------------------------------------------------------------------

_LLM_DIMS = ("structure", "semantic", "library", "type", "search")
_DEFAULT_LLM_SCORE = {dim: 2 for dim in _LLM_DIMS}


def _parse_llm_json(text: str) -> dict:
    """从 LLM 回复中提取 JSON（容忍 markdown 代码块包裹）。"""
    m = re.search(r"```(?:json)?\s*\n?(.*?)```", text, re.DOTALL)
    candidate = m.group(1).strip() if m else text.strip()
    return json.loads(candidate)


def _collect_proof_code(
    problem_path: str,
    log_dir: Path,
) -> str | None:
    """
    从 LOG 目录中收集某道题的最佳完整证明代码。

    扫描 LOG 下所有包含该题的实验目录，优先选 all_passed=True 的，
    否则选 passed_count 最高的。返回拼接后的 .lean 文件内容。
    """
    prob_stem = Path(problem_path).stem
    best_dir: Path | None = None
    best_score = (-1, -1)  # (all_passed, passed_count)

    for d in sorted(log_dir.iterdir(), reverse=True):
        if not d.is_dir() or d.name.startswith("_"):
            continue
        if prob_stem not in d.name:
            continue

        sum_f = d / "summary.json"
        if not sum_f.exists():
            continue

        try:
            summary = json.loads(sum_f.read_text(encoding="utf-8"))
        except Exception:
            continue

        score = (int(summary.get("all_passed", False)), int(summary.get("passed_count", 0)))
        if score > best_score:
            best_score = score
            best_dir = d

    if best_dir is None:
        return None

    # 拼接该目录下所有 .lean 文件
    lean_files = sorted(best_dir.glob("block_*.lean"))
    if not lean_files:
        # 也许整个文件存为单个 .lean
        lean_files = sorted(best_dir.glob("*.lean"))
    if not lean_files:
        return None

    parts = [f.read_text(encoding="utf-8") for f in lean_files]
    return "\n\n".join(parts)


def score_posterior(
    problem_path: str,
    proof_code: str,
    cfg: ModelConfig,
    *,
    weights: dict[str, float] | None = None,
    retries: int = 1,
) -> PosteriorScore:
    """
    对一道题的完成证明做后验难度评分。

    Parameters
    ----------
    problem_path : 题目路径
    proof_code : 已填补证明的完整 Lean 代码
    cfg : LLM 配置
    weights : 维度权重覆盖
    retries : LLM 调用失败时的重试次数
    """
    w = {**POSTERIOR_WEIGHTS, **(weights or {})}
    ps = PosteriorScore(problem_path=problem_path)

    user_msg = (
        "Here is the completed Lean 4 proof code:\n\n"
        f"```lean\n{proof_code[:8000]}\n```\n\n"
        "Rate the complexity of this proof."
    )
    messages = [
        {"role": "system", "content": _POSTERIOR_SYSTEM_PROMPT},
        {"role": "user", "content": user_msg},
    ]

    scores: dict | None = None
    prompt_tokens = 0
    completion_tokens = 0
    total_tokens = 0
    for attempt in range(1 + retries):
        try:
            response, usage = generate_with_usage(messages, cfg, timeout=None)
            prompt_tokens = usage.prompt_tokens
            completion_tokens = usage.completion_tokens
            total_tokens = usage.total_tokens
            scores = _parse_llm_json(response)
            break
        except Exception as e:
            if attempt == retries:
                print(f"[PosteriorScorer] LLM failed for {Path(problem_path).stem}: {e}, using defaults")
                scores = dict(_DEFAULT_LLM_SCORE)

    if scores is None:
        scores = dict(_DEFAULT_LLM_SCORE)

    for dim in _LLM_DIMS:
        val = scores.get(dim, 2)
        val = max(0, min(4, int(val)))
        if dim == "type":
            ps.type_score = val
        else:
            setattr(ps, dim, val)

    ps.reasoning = scores.get("reasoning", "")
    ps.prompt_tokens = int(prompt_tokens)
    ps.completion_tokens = int(completion_tokens)
    ps.total_tokens = int(total_tokens)

    # --- raw score ---
    ps.raw_score = (
        w["structure"] * (ps.structure / 4.0)
        + w["semantic"] * (ps.semantic / 4.0)
        + w["library"] * (ps.library / 4.0)
        + w["type"] * (ps.type_score / 4.0)
        + w["search"] * (ps.search / 4.0)
    )

    return ps
