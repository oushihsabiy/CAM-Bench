#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""prior_scorer.py: 先验难度评分 — 基于 Lean 源码静态分析 + LLM 判定。"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from pathlib import Path

from .llm_client import ModelConfig, generate_with_usage
from .problem_loader import Problem, SorryBlock


# ---------------------------------------------------------------------------
# 先验维度权重默认值
# ---------------------------------------------------------------------------

PRIOR_WEIGHTS = {
    "hypothesis_count": 0.10,
    "sorry_block_count": 0.05,
    "statement_length": 0.05,
    "structural_complexity": 0.25,
    "concept_complexity": 0.25,
    "formalization_gap": 0.20,
    "type_sophistication": 0.10,
}


# ---------------------------------------------------------------------------
# LLM 评分 Prompt
# ---------------------------------------------------------------------------

_PRIOR_SYSTEM_PROMPT = """\
You are an expert Lean 4 formal verification researcher.
You are given a Lean 4 file where some theorems/lemmas contain `sorry` (proof placeholder).
Analyze the STATEMENTS ONLY (ignore sorry) and rate proof difficulty.

For each dimension, assign a score from 0 to 4:
0 = trivial / no complexity
1 = low complexity
2 = moderate
3 = high
4 = very high complexity

Dimensions:

- structural_complexity:
  0 = single-step proof likely (rfl, simp, exact)
  1 = short linear proof (2-3 tactics)
  2 = moderate (case splits, simple induction)
  3 = complex (nested induction, multiple intermediate lemmas)
  4 = very complex (deep recursion, heavy case analysis, auxiliary constructions)

- concept_complexity:
  0 = basic logic/arithmetic (Nat, Bool, simple propositions)
  1 = standard undergraduate math (groups, basic analysis)
  2 = moderate (linear algebra, topology basics, measure theory basics)
  3 = advanced (functional analysis, algebraic geometry, advanced probability)
  4 = research-level (complex interactions of multiple advanced domains)

- formalization_gap:
  0 = standard in Mathlib, direct formalization
  1 = minor adaptation from existing Mathlib patterns
  2 = moderate effort, some Lean-specific encoding tricks needed
  3 = significant challenge, non-obvious encoding
  4 = very hard to formalize, major gap between math and Lean

- type_sophistication:
  0 = simple concrete types (ℕ, ℝ, List)
  1 = basic abstract types (Group, Ring)
  2 = parameterized types with constraints
  3 = dependent types, Fin/Subtype interactions
  4 = complex type-level computation, universe polymorphism

IMPORTANT:
- Score ONLY based on the definitions above
- Do NOT give an overall score
- Do NOT compare with other problems
- Base judgment ONLY on theorem statements, not on proof content

Return ONLY valid JSON (no markdown, no explanation outside JSON):
{"structural_complexity": <int>, "concept_complexity": <int>, "formalization_gap": <int>, "type_sophistication": <int>, "reasoning": "<1-2 sentences>"}
"""


# ---------------------------------------------------------------------------
# 数据模型
# ---------------------------------------------------------------------------

@dataclass
class PriorScore:
    """一道题的先验难度评分。"""
    problem_path: str

    # 静态指标（raw count，归一化延迟到聚合阶段）
    hypothesis_count: int = 0
    sorry_block_count: int = 0
    statement_length: int = 0

    # LLM 指标（0-4）
    structural_complexity: int = 0
    concept_complexity: int = 0
    formalization_gap: int = 0
    type_sophistication: int = 0

    # LLM 推理说明
    reasoning: str = ""

    # token 使用统计
    prompt_tokens: int = 0
    completion_tokens: int = 0
    total_tokens: int = 0

    # 加权 raw score（静态指标用原始值加权，LLM 指标 /4 归一化后加权）
    raw_score: float = 0.0


# ---------------------------------------------------------------------------
# 静态分析
# ---------------------------------------------------------------------------

_HYPOTHESIS_RE = re.compile(r"\(h\w*\s*:", re.MULTILINE)
_STATEMENT_RE = re.compile(
    r"^(theorem|lemma)\s+\S+.*?:=\s*by",
    re.MULTILINE | re.DOTALL,
)


def _count_hypotheses(text: str) -> int:
    """统计定理声明中的假设数量（匹配 `(hxxx :` 模式）。"""
    return len(_HYPOTHESIS_RE.findall(text))


def _statement_lines(block_text: str) -> int:
    """估算 theorem/lemma 声明部分的行数（从开头到 `:= by` 或 `sorry`）。"""
    lines = block_text.splitlines()
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped.endswith(":= by") or stripped == "sorry" or stripped.startswith("sorry"):
            return i + 1
    return len(lines)


def _extract_static_features(problem: Problem) -> dict:
    """从 Problem 提取静态特征。"""
    max_hyp = 0
    max_stmt_len = 0
    for block in problem.blocks:
        max_hyp = max(max_hyp, _count_hypotheses(block.raw_text))
        max_stmt_len = max(max_stmt_len, _statement_lines(block.raw_text))

    return {
        "hypothesis_count": max_hyp,
        "sorry_block_count": len(problem.blocks),
        "statement_length": max_stmt_len,
    }


# ---------------------------------------------------------------------------
# LLM 评分
# ---------------------------------------------------------------------------

def _parse_llm_json(text: str) -> dict:
    """从 LLM 回复中提取 JSON（容忍 markdown 代码块包裹）。"""
    # 尝试提取代码块内的 JSON
    m = re.search(r"```(?:json)?\s*\n?(.*?)```", text, re.DOTALL)
    candidate = m.group(1).strip() if m else text.strip()
    return json.loads(candidate)


def _score_block_with_llm(
    block: SorryBlock,
    full_context: str,
    cfg: ModelConfig,
) -> tuple[dict, int, int, int]:
    """用 LLM 对单个 sorry block 做先验评分，返回 4 维分数字典。"""
    user_msg = (
        "Here is the Lean 4 file context (you may reference imports and definitions):\n\n"
        f"```lean\n{full_context[:6000]}\n```\n\n"
        "Now analyze this specific theorem/lemma block:\n\n"
        f"```lean\n{block.raw_text}\n```\n\n"
        "Rate the proof difficulty based on the statement only."
    )
    messages = [
        {"role": "system", "content": _PRIOR_SYSTEM_PROMPT},
        {"role": "user", "content": user_msg},
    ]
    response, usage = generate_with_usage(messages, cfg, timeout=None)
    return (
        _parse_llm_json(response),
        usage.prompt_tokens,
        usage.completion_tokens,
        usage.total_tokens,
    )


_LLM_DIMS = ("structural_complexity", "concept_complexity",
              "formalization_gap", "type_sophistication")
_DEFAULT_LLM_SCORE = {dim: 2 for dim in _LLM_DIMS}


def score_prior(
    problem: Problem,
    cfg: ModelConfig,
    *,
    weights: dict[str, float] | None = None,
    retries: int = 1,
) -> PriorScore:
    """
    对一道题做先验难度评分。

    对每个 sorry block 分别调 LLM，取所有 block 的 max 作为题目级分数。
    """
    w = {**PRIOR_WEIGHTS, **(weights or {})}
    ps = PriorScore(problem_path=str(problem.path))

    # --- 静态指标 ---
    static = _extract_static_features(problem)
    ps.hypothesis_count = static["hypothesis_count"]
    ps.sorry_block_count = static["sorry_block_count"]
    ps.statement_length = static["statement_length"]

    # --- LLM 指标（对每个 block 取 max）---
    best = dict(_DEFAULT_LLM_SCORE)
    reasoning_parts: list[str] = []

    for block in problem.blocks:
        scores = None
        block_pt = 0
        block_ct = 0
        block_tt = 0
        for attempt in range(1 + retries):
            try:
                scores, block_pt, block_ct, block_tt = _score_block_with_llm(block, problem.full_text, cfg)
                break
            except Exception as e:
                if attempt == retries:
                    print(f"[PriorScorer] LLM failed for {block.name}: {e}, using defaults")
                    scores = dict(_DEFAULT_LLM_SCORE)

        if scores is None:
            scores = dict(_DEFAULT_LLM_SCORE)

        ps.prompt_tokens += int(block_pt)
        ps.completion_tokens += int(block_ct)
        ps.total_tokens += int(block_tt)

        for dim in _LLM_DIMS:
            val = scores.get(dim, 2)
            val = max(0, min(4, int(val)))
            best[dim] = max(best[dim], val)

        if "reasoning" in scores:
            reasoning_parts.append(f"[{block.name}] {scores['reasoning']}")

    ps.structural_complexity = best["structural_complexity"]
    ps.concept_complexity = best["concept_complexity"]
    ps.formalization_gap = best["formalization_gap"]
    ps.type_sophistication = best["type_sophistication"]
    ps.reasoning = " | ".join(reasoning_parts) if reasoning_parts else ""

    # --- raw score ---
    # 静态指标直接用原始值参与加权（归一化在聚合阶段做 rank-based）
    # LLM 指标 /4 映射到 [0, 1]
    ps.raw_score = (
        w["hypothesis_count"] * ps.hypothesis_count
        + w["sorry_block_count"] * ps.sorry_block_count
        + w["statement_length"] * ps.statement_length
        + w["structural_complexity"] * (ps.structural_complexity / 4.0)
        + w["concept_complexity"] * (ps.concept_complexity / 4.0)
        + w["formalization_gap"] * (ps.formalization_gap / 4.0)
        + w["type_sophistication"] * (ps.type_sophistication / 4.0)
    )

    return ps
