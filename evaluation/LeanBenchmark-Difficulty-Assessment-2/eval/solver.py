#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""solver.py: 顺序前缀编译模式的 sorry 逐一修复 Pipeline。

核心算法：
1. 检测文件中所有 sorry（按源码顺序）。
2. 从第 1 个 sorry 开始：
   - 构建前缀文件（从文件开头到当前 sorry 所在块结尾）。
   - LLM 填充当前块中的 `/- FILL_PROOF_HERE -/` 占位符。
   - 用 `lake env lean` 编译前缀文件（不做错误过滤）。
   - 编译通过 = 成功；继续下一个 sorry。
3. 依次处理所有 sorry，每次前缀都包含已解决的历史内容。
4. 全部解决后做最终全文件重验证。
"""

from __future__ import annotations

import json
import re
import time
from dataclasses import dataclass, field
from pathlib import Path

from .lean_mcp_client import LeanMCPClient, LeanMCPContext, LeanMCPQueryResult
from .llm_client import ModelConfig, extract_lean_code, generate_with_usage
from .lean_verifier import VerifyResult, check_proof_integrity, verify_lean_string
from .problem_loader import Problem, SorryItem, _count_sorry, detect_sorry_items


# ---------------------------------------------------------------------------
# 数据模型
# ---------------------------------------------------------------------------

@dataclass
class AttemptRecord:
    """单轮尝试记录。"""
    turn: int
    passed: bool
    code_snippet: str           # 本轮 LLM 输出的代码（完整块）
    errors: str                 # Lean 前缀编译返回的错误摘要
    error_types: list[str]      # 错误类型集合
    elapsed_sec: float          # 本轮编译耗时
    prompt_tokens: int = 0
    completion_tokens: int = 0
    total_tokens: int = 0
    mcp_context_used: bool = False
    mcp_call_count: int = 0          # MCP 发起调用次数
    mcp_failure_count: int = 0       # MCP 工具失败次数
    mcp_failed_tools: list[str] = field(default_factory=list)  # 失败的工具名列表
    mcp_error_msg: str = ""          # 异常或空返回时的原因描述


@dataclass
class BlockResult:
    """单个 sorry 修复结果（每个 sorry token 对应一条记录）。"""
    block_name: str
    block_index: int
    sorry_index: int            # 在文件中的全局 sorry 顺序编号（0-based）
    sorry_count: int            # 固定为 1（每个 SorryItem 一个 BlockResult）
    passed: bool
    attempts: int               # 本 sorry 总尝试轮数
    first_pass_turn: int        # 首次通过的轮次（0 = 未成功）
    total_elapsed_sec: float    # 本 sorry 所有轮次总耗时
    final_code: str             # 最终块代码（成功时为通过版本，失败时为最后一轮）
    prompt_tokens: int = 0
    completion_tokens: int = 0
    total_tokens: int = 0
    termination_reason: str = "completed"   # completed / limit_exceeded / compile_stuck / llm_error / llm_error_budget_exceeded / auto_solved
    timeline: list[AttemptRecord] = field(default_factory=list)


@dataclass
class SolveResult:
    """一道题目的整体修复结果。"""
    problem_path: str
    model: str
    total_blocks: int           # = n_sorry_found
    passed_blocks: int
    all_passed: bool
    total_attempts: int
    total_elapsed_sec: float
    prompt_tokens: int = 0
    completion_tokens: int = 0
    total_tokens: int = 0
    block_results: list[BlockResult] = field(default_factory=list)
    final_verify_passed: bool | None = None
    final_verify_issues: list[str] = field(default_factory=list)
    n_sorry_found: int = 0                  # 文件中检测到的 sorry 总数
    termination_reason: str = "completed"   # completed / limit_exceeded / compile_stuck / llm_error / llm_error_budget_exceeded
    mcp_enabled: bool = False
    mcp_calls: int = 0
    mcp_failures: int = 0
    mcp_time_ms: int = 0


# ---------------------------------------------------------------------------
# 运行时计数器（跨所有 sorry 的文件级累计）
# ---------------------------------------------------------------------------

@dataclass
class RunningTotals:
    """文件级跨 sorry 累计运行计数器（用于限额检测和实时进度）。"""
    t0: float = field(default_factory=time.monotonic)
    turns: int = 0
    prompt_tokens: int = 0
    completion_tokens: int = 0
    total_tokens: int = 0
    mcp_calls: int = 0
    mcp_failures: int = 0
    mcp_time_ms: int = 0
    llm_error_budget_per_sorry: int = 10  # 0 = unlimited

    def elapsed(self) -> float:
        return time.monotonic() - self.t0

    def check_limits(
        self,
        max_tokens: int,
        problem_timeout: float,
    ) -> str | None:
        """
        检查全局限额。返回非空字符串表示触发了哪条限额，None 表示未触发。

        参数
        ----
        max_tokens      : 文件级 token 总预算（0 = 不限）
        problem_timeout : 文件级时间上限（秒，0 = 不限）
        """
        if max_tokens > 0 and self.total_tokens >= max_tokens:
            return f"limit_exceeded:max_tokens({self.total_tokens}>={max_tokens})"
        if problem_timeout > 0 and self.elapsed() >= problem_timeout:
            return f"limit_exceeded:problem_timeout({self.elapsed():.1f}s>={problem_timeout}s)"
        return None


# ---------------------------------------------------------------------------
# Prompt 模板
# ---------------------------------------------------------------------------

_SYSTEM_PROMPT = """\
You are a Lean 4 proof assistant. Your task is to fill in exactly ONE proof placeholder.

Rules:
- Output the COMPLETE theorem/lemma/def block.
- Replace ONLY the `/- FILL_PROOF_HERE -/` marker with a valid proof.
- Do NOT modify any `sorry` tokens already present in the block (those belong to later steps).
- Do NOT add `axiom` or `admit`.
- In the proof you write for `/- FILL_PROOF_HERE -/`, NEVER use `sorry`.
- Before using any lemma/theorem/definition name, verify it is resolvable in current context.
- Never guess or invent lemma names based on similarity.
- If a needed lemma is not resolvable from the search results, either switch to available lemmas or define a helper first (without sorry/axiom/admit).
- Do NOT add explanatory comments or natural language reasoning in Lean code.
- Wrap your code in a ```lean code block.
"""

_FIRST_TURN_USER = """\
Here is a Lean 4 block containing a proof placeholder `/- FILL_PROOF_HERE -/` \
and possibly other `sorry` tokens (which you must leave untouched).

```lean
{block_code}
```
{mcp_sections}

Replace ONLY the `/- FILL_PROOF_HERE -/` with a correct proof.
If the required lemma or definition is not found in the search results, define it yourself first before using it.
Use exact identifier names from searchable context; do not use similar-looking names that are not resolvable.
Do NOT use `sorry`, `axiom`, or `admit` in the proof you write.
"""

_RETRY_TURN_USER = """\
Your previous attempt produced compile errors. Here is the original template and your last attempt:

## Original Template (with placeholder)
```lean
{block_template}
```

## Your Previous Attempt
```lean
{prev_code}
```

## Compile Errors
{compile_errors}
{mcp_sections}

Fix ONLY the `/- FILL_PROOF_HERE -/` proof in the ORIGINAL TEMPLATE. Keep any other `sorry` tokens unchanged.
If the required lemma or definition is not found in the search results, define it yourself first before using it.
Before writing the final proof, ensure every new identifier you use is resolvable; otherwise revise the approach.
Do NOT use `sorry`, `axiom`, or `admit` in the proof you write.
Do NOT add comments, explanations, or text outside the Lean code block.
Output the complete corrected block in a ```lean code block.
"""

_RETRY_TURN_USER_WITH_HISTORY = """\
Previous attempts for THIS SAME proof placeholder produced compile errors. Use only the same-placeholder history below.

## Original Template (with placeholder)
```lean
{block_template}
```

## Previous Attempts For This Same Placeholder
{attempt_history}
{mcp_sections}

Fix ONLY the `/- FILL_PROOF_HERE -/` proof in the ORIGINAL TEMPLATE. Keep any other `sorry` tokens unchanged.
If the required lemma or definition is not found in the search results, define it yourself first before using it.
Before writing the final proof, ensure every new identifier you use is resolvable; otherwise revise the approach.
Do NOT use `sorry`, `axiom`, or `admit` in the proof you write.
Do NOT add comments, explanations, or text outside the Lean code block.
Output the complete corrected block in a ```lean code block.
"""


# ---------------------------------------------------------------------------
# 内部辅助
# ---------------------------------------------------------------------------

def _check_fill_integrity(new_block_text: str, n_expected_sorry: int) -> list[str]:
    """
    严格完整性检查：LLM 输出不允许出现任何 sorry。
    
    规则：
    - 任何非注释的 sorry 都是违规，即使是后续占位符也不允许
    - 不允许 axiom / admit
    
    这确保填补的证明片段是完整且有效的，不依赖后续的占位符。
    """
    issues: list[str] = []
    if _count_sorry(new_block_text) > 0:
        issues.append("contains_sorry")
    for line in new_block_text.splitlines():
        stripped = line.lstrip()
        if stripped.startswith("--"):
            continue
        code_part = line.split("--")[0]
        if re.search(r'\baxiom\b', code_part):
            issues.append("contains_axiom")
        if re.search(r'\badmit\b', code_part):
            issues.append("contains_admit")
    return sorted(set(issues))


def _render_same_sorry_attempt_history(timeline: list[AttemptRecord]) -> str:
    """渲染同一个 sorry 的历史尝试；不包含更早 sorry 的内容。"""
    chunks: list[str] = []
    for rec in timeline:
        if not rec.code_snippet.strip():
            continue
        errors = rec.errors.strip() or "(no errors captured)"
        chunks.append(
            "\n".join(
                [
                    f"### Turn {rec.turn}",
                    "```lean",
                    rec.code_snippet,
                    "```",
                    "Compile / Integrity Errors:",
                    errors,
                ]
            )
        )
    return "\n\n".join(chunks)


def _save_working_state(tmp_dir: Path, sorry_idx: int, working_text: str) -> None:
    """将 sorry_idx 处理完毕后的 working_text 快照写入文件，供断点续传使用。"""
    state_file = tmp_dir / f"working_state_after_sorry{sorry_idx}.lean"
    try:
        state_file.write_text(working_text, encoding="utf-8")
    except OSError:
        pass  # 写失败不影响主流程


def _load_resume_state(
    tmp_dir: Path,
    problem_full_text: str,
    n_sorry_found: int,
) -> "tuple[int, str, list[BlockResult]] | None":
    """
    尝试从 tmp_dir 加载上次中断的续跑状态。

    Returns
    -------
    (start_sorry_idx, working_text, block_results_so_far)
        若存在可用状态；否则返回 None（从头开始）。
    """
    progress_file = tmp_dir / "progress.json"
    if not progress_file.exists():
        return None

    try:
        progress = json.loads(progress_file.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return None

    sorry_attempted = int(progress.get("sorry_attempted", 0))
    if sorry_attempted == 0:
        return None

    saved_n = int(progress.get("n_sorry_found", 0))
    if saved_n != n_sorry_found:
        print(
            f"[Solver] Resume: n_sorry_found 不匹配 (saved={saved_n}, current={n_sorry_found})，"
            f"从头开始"
        )
        return None

    # 重建最小化的 BlockResult 列表（仅需 passed / attempts / termination_reason）
    results_data: list[dict] = progress.get("results", [])
    block_results: list[BlockResult] = []
    for rd in results_data:
        br = BlockResult(
            block_name=str(rd.get("block_name", "")),
            block_index=int(rd.get("sorry_index", 0)),
            sorry_index=int(rd.get("sorry_index", 0)),
            sorry_count=1,
            passed=bool(rd.get("passed", False)),
            attempts=int(rd.get("attempts", 0)),
            first_pass_turn=0,
            total_elapsed_sec=0.0,
            final_code="",
            termination_reason=str(rd.get("termination_reason", "completed")),
        )
        block_results.append(br)

    # 确定续跑起始索引（上次已处理了 sorry_attempted 个）
    start_idx = sorry_attempted

    # 加载对应的 working_text 快照
    if start_idx == 0:
        return start_idx, problem_full_text, block_results

    # 优先尝试精确匹配的快照文件，找不到则向前回退
    for k in range(start_idx - 1, -1, -1):
        sf = tmp_dir / f"working_state_after_sorry{k}.lean"
        if sf.exists():
            working_text = sf.read_text(encoding="utf-8")
            if k < start_idx - 1:
                # 回退到更早的快照
                start_idx = k + 1
                block_results = block_results[: k + 1]
                print(f"[Solver] Resume: 快照回退，从 sorry {start_idx} 续跑")
            return start_idx, working_text, block_results

    # 无任何快照文件：从头开始但保留已有 block_results（仅重算 working_text）
    print("[Solver] Resume: 未找到 working_state 快照，从头重建 working_text")
    return 0, problem_full_text, []


def _save_progress(
    tmp_dir: Path,
    sorry_idx: int,
    n_sorry: int,
    running: RunningTotals,
    block_results: list[BlockResult],
) -> None:
    """将当前进度写入 tmp_dir/progress.json，支持长时间运行时的实时监控。"""
    progress = {
        "sorry_attempted": sorry_idx + 1,
        "n_sorry_found": n_sorry,
        "elapsed_sec": round(running.elapsed(), 2),
        "total_turns": running.turns,
        "prompt_tokens": running.prompt_tokens,
        "completion_tokens": running.completion_tokens,
        "total_tokens": running.total_tokens,
        "mcp_calls": running.mcp_calls,
        "mcp_failures": running.mcp_failures,
        "mcp_time_ms": running.mcp_time_ms,
        "results": [
            {
                "sorry_index": br.sorry_index,
                "block_name": br.block_name,
                "passed": br.passed,
                "attempts": br.attempts,
                "termination_reason": br.termination_reason,
            }
            for br in block_results
        ],
    }
    try:
        (tmp_dir / "progress.json").write_text(
            json.dumps(progress, ensure_ascii=False, indent=2), encoding="utf-8"
        )
    except OSError:
        pass  # 进度文件写失败不影响主流程


def _load_failed_turn_resume(
    *,
    tmp_dir: Path,
    sorry_idx: int,
    max_turns: int,
    err_log_dir: Path,
    problem: Problem,
    model_id: str,
) -> tuple[int, str, str] | None:
    """
    尝试从已有失败轮次继续当前 sorry。

    Returns
    -------
    (next_turn, prev_code, last_compile_errors)
        next_turn 取最近一轮已记录失败日志的下一轮；
        prev_code / last_compile_errors 取“最近一轮不含 sorry 的失败代码和错误”。
        若找不到满足条件的基准，则返回 None。
    """
    turn_to_code_path: dict[int, Path] = {}
    for code_path in tmp_dir.glob(f"sorry{sorry_idx}_turn*.lean"):
        m = re.fullmatch(rf"sorry{sorry_idx}_turn(\d+)\.lean", code_path.name)
        if m is None:
            continue
        turn = int(m.group(1))
        turn_to_code_path[turn] = code_path

    if not turn_to_code_path:
        return None

    problem_id = _get_problem_id(problem)

    def _load_err_payload(turn: int) -> dict | None:
        err_path = err_log_dir / problem_id / model_id / f"sorry_{sorry_idx}" / f"turn_{turn}.json"
        if not err_path.exists():
            return None
        try:
            payload = json.loads(err_path.read_text(encoding="utf-8"))
            if isinstance(payload, dict):
                return payload
        except (OSError, json.JSONDecodeError):
            return None
        return None

    # 续跑轮次：基于最近一轮有失败日志的 turn，而不是单纯看代码文件。
    latest_logged_turn = 0
    latest_logged_payload: dict | None = None
    for turn in sorted(turn_to_code_path.keys(), reverse=True):
        payload = _load_err_payload(turn)
        if payload is not None:
            latest_logged_turn = turn
            latest_logged_payload = payload
            break

    if latest_logged_turn <= 0 or latest_logged_turn >= max_turns:
        return None

    if latest_logged_payload is not None and bool(latest_logged_payload.get("passed", False)):
        return None

    next_turn = latest_logged_turn + 1

    # 基准代码：从新到旧找最近一轮“不含 sorry”的失败代码。
    for turn in range(latest_logged_turn, 0, -1):
        code_path = turn_to_code_path.get(turn)
        if code_path is None:
            continue
        err_payload = _load_err_payload(turn)
        if err_payload is None:
            continue
        if bool(err_payload.get("passed", False)):
            continue

        last_compile_errors = str(err_payload.get("errors", "")).strip()
        if not last_compile_errors:
            continue

        try:
            prev_code = code_path.read_text(encoding="utf-8")
        except OSError:
            continue

        if _count_sorry(prev_code) > 0:
            continue

        return next_turn, prev_code, last_compile_errors

    return None


def _load_same_sorry_attempt_history(
    *,
    err_log_dir: Path,
    problem: Problem,
    model_id: str,
    sorry_idx: int,
    upto_turn: int,
) -> list[AttemptRecord]:
    """为续跑恢复同一个 sorry 的历史尝试；不读取更早 sorry。"""
    if upto_turn <= 0:
        return []

    problem_id = _get_problem_id(problem)
    sorry_dir = err_log_dir / problem_id / model_id / f"sorry_{sorry_idx}"
    if not sorry_dir.exists():
        return []

    timeline: list[AttemptRecord] = []
    for turn in range(1, upto_turn + 1):
        err_path = sorry_dir / f"turn_{turn}.json"
        if not err_path.exists():
            continue
        try:
            payload = json.loads(err_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if not isinstance(payload, dict):
            continue

        timeline.append(
            AttemptRecord(
                turn=int(payload.get("turn", turn)),
                passed=bool(payload.get("passed", False)),
                code_snippet=str(payload.get("code_snippet", "")),
                errors=str(payload.get("errors", "")),
                error_types=list(payload.get("error_types", [])),
                elapsed_sec=float(payload.get("elapsed_sec", 0.0) or 0.0),
                prompt_tokens=int(payload.get("prompt_tokens", 0) or 0),
                completion_tokens=int(payload.get("completion_tokens", 0) or 0),
                total_tokens=int(payload.get("total_tokens", 0) or 0),
                mcp_context_used=bool(payload.get("mcp_context_used", False)),
                mcp_call_count=int(payload.get("mcp_call_count", 0) or 0),
                mcp_failure_count=int(payload.get("mcp_failure_count", 0) or 0),
                mcp_failed_tools=list(payload.get("mcp_failed_tools", [])),
                mcp_error_msg=str(payload.get("mcp_error_msg", "")),
            )
        )

    return timeline


def _build_mcp_sections(ctx: LeanMCPContext | None) -> str:
    """将 MCP 上下文各字段渲染为 prompt 中带语义标签的独立小节。"""
    if ctx is None or not ctx.has_content():
        return ""
    parts: list[str] = []
    if ctx.goals:
        parts.append(f"## Lean Proof State\n{ctx.goals}")
    if ctx.search_results:
        sr_warning = (
            "> 💡 These are relevant Mathlib theorems from search. Prioritize using these when applicable.\n"
        )
        parts.append(f"## Relevant Theorems\n{sr_warning}\n{ctx.search_results}")
    if ctx.tactics:
        parts.append(f"## Suggested Tactics\n{ctx.tactics}")
    if ctx.diagnostics:
        parts.append(f"## Additional Diagnostics\n{ctx.diagnostics}")
    if ctx.raw and not (ctx.goals or ctx.search_results or ctx.tactics or ctx.diagnostics):
        parts.append(f"## MCP Output\n{ctx.raw}")
    if not parts:
        return ""
    return "\n" + "\n\n".join(parts)


# ---------------------------------------------------------------------------
# 日志记录
# ---------------------------------------------------------------------------

def _get_problem_id(problem: Problem) -> str:
    """从 Problem 提取标准化的 problem ID（去掉扩展名）。"""
    return Path(problem.path).stem


def _get_model_id(cfg_or_model: ModelConfig | str) -> str:
    """Return a filesystem-safe model identifier for shared log directories."""
    model = cfg_or_model.model if isinstance(cfg_or_model, ModelConfig) else str(cfg_or_model)
    model = str(model).strip() or "unknown_model"
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", model)


def _log_attempt_record(
    problem: Problem,
    model_id: str,
    sorry_index: int,
    rec: AttemptRecord,
    err_log_dir: Path,
) -> None:
    """将单轮尝试记录到 ERR_LOG 文件夹。
    
    目录结构：
    ERR_LOG/{problem_id}/{model_id}/sorry_{sorry_index}/turn_{turn}.json
    """
    problem_id = _get_problem_id(problem)
    sorry_dir = err_log_dir / problem_id / model_id / f"sorry_{sorry_index}"
    sorry_dir.mkdir(parents=True, exist_ok=True)
    
    log_file = sorry_dir / f"turn_{rec.turn}.json"
    
    # 准备日志内容
    log_data = {
        "turn": rec.turn,
        "model": model_id,
        "passed": rec.passed,
        "elapsed_sec": rec.elapsed_sec,
        "prompt_tokens": rec.prompt_tokens,
        "completion_tokens": rec.completion_tokens,
        "total_tokens": rec.total_tokens,
        "error_types": rec.error_types,
        "mcp_context_used": rec.mcp_context_used,
        "mcp_call_count": rec.mcp_call_count,
        "mcp_failure_count": rec.mcp_failure_count,
        "mcp_failed_tools": rec.mcp_failed_tools,
        "mcp_error_msg": rec.mcp_error_msg,
        "code_snippet": rec.code_snippet,
        "errors": rec.errors,
    }
    
    with open(log_file, "w", encoding="utf-8") as f:
        json.dump(log_data, f, indent=2, ensure_ascii=False)


def _log_mcp_record(
    problem: Problem,
    model_id: str,
    sorry_index: int,
    turn: int,
    mcp_ctx: LeanMCPContext,
    mcp_result: LeanMCPQueryResult,
    rendered_for_llm: str,
    mcp_log_dir: Path,
) -> None:
    """将 MCP 返回内容记录到 MCP_LOG 文件夹。
    
    目录结构：
    MCP_LOG/{problem_id}/{model_id}/sorry_{sorry_index}/turn_{turn}.json
    
    记录完整的 MCP 调用返回及最终传给 LLM 的渲染内容。
    """
    problem_id = _get_problem_id(problem)
    sorry_dir = mcp_log_dir / problem_id / model_id / f"sorry_{sorry_index}"
    sorry_dir.mkdir(parents=True, exist_ok=True)
    
    log_file = sorry_dir / f"turn_{turn}.json"
    
    # 准备 MCP 日志内容
    log_data = {
        "turn": turn,
        "model": model_id,
        "mcp_tools_called": mcp_result.used_tools,
        "mcp_tools_failed": mcp_result.failed_tools,
        "mcp_call_count": mcp_result.call_count,
        "mcp_failure_count": mcp_result.failure_count,
        "mcp_context": {
            "goals": mcp_ctx.goals,
            "diagnostics": mcp_ctx.diagnostics,
            "search_results": mcp_ctx.search_results,
            "tactics": mcp_ctx.tactics,
            "raw": mcp_ctx.raw,
        },
        "mcp_rendered_for_llm": rendered_for_llm,
    }
    
    with open(log_file, "w", encoding="utf-8") as f:
        json.dump(log_data, f, indent=2, ensure_ascii=False)


# ---------------------------------------------------------------------------
# 核心：单个 sorry 的多轮修复
# ---------------------------------------------------------------------------

def _solve_one_sorry(
    sorry_item: SorryItem,
    global_sorry_index: int,
    working_text: str,
    cfg: ModelConfig,
    *,
    lean_cwd: str | None,
    tmp_dir: Path,
    verify_timeout: float,
    running: RunningTotals,
    max_turns: int,
    max_tokens: int,
    problem_timeout: float,
    problem: Problem,
    err_log_dir: Path,
    mcp_log_dir: Path | None = None,
    lean_mcp_client: LeanMCPClient | None = None,
    same_sorry_history_in_prompt: bool = False,
) -> tuple[BlockResult, str]:
    """
    对 working_text 中的单个 sorry（由 sorry_item 指定）做多轮 LLM 修复。

    编译目标为**前缀文件**：
        prefix = working_text[:block_start] + new_block_text

    这确保每一步都只验证"从文件头到当前块末尾"的子集，
    且已修复的历史内容始终包含在前缀内。

    Returns
    -------
    (BlockResult, updated_working_text_if_passed)
    如果修复成功，返回更新后的 working_text；否则返回原始 working_text。
    """
    block_start = sorry_item.block_char_start
    block_end = sorry_item.block_char_end
    block_text = working_text[block_start:block_end]

    # 防御性诊断：块中若出现多个声明头，通常意味着上游边界识别异常。
    decl_heads = re.findall(
        r"(?m)^\s*(?:noncomputable\s+def|theorem|lemma|def)\s+\S+",
        block_text,
    )
    if len(decl_heads) > 1:
        print(
            f"[Solver] WARNING: suspicious block range for sorry {global_sorry_index}, "
            f"block='{sorry_item.block_name}', decl_heads={len(decl_heads)}"
        )

    # 构建块模板：仅替换本 sorry，其余 sorry 保持原样
    rel_offset = sorry_item.char_offset - block_start
    placeholder = "/- FILL_PROOF_HERE -/"
    block_template = (
        block_text[:rel_offset]
        + placeholder
        + block_text[rel_offset + len("sorry"):]
    )
    # 模板中剩余的 sorry 数（允许 LLM 保留；不允许超过）
    n_expected_sorry = _count_sorry(block_template)

    timeline: list[AttemptRecord] = []
    # prev_code: 上一轮发给模型的代码（LLM 错误时不更新）
    # last_compile_errors: 上一轮 Lean 编译错误（LLM 错误时不更新）
    prev_code = block_template
    last_compile_errors: str = ""
    # 追踪最后一个通过完整性检查的轮次，供失败时回溯
    last_integrity_passed_code = block_template
    last_integrity_passed_errors: str = ""
    start_turn = 1
    last_mcp_ctx: LeanMCPContext | None = None
    prefetch_mcp_called = False
    prefetch_mcp_context_used = False
    prefetch_mcp_call_count = 0
    prefetch_mcp_failure_count = 0
    prefetch_mcp_failed_tools: list[str] = []
    prefetch_mcp_error_msg = ""
    final_code = block_text      # 默认保留原始块（失败时用）
    passed = False
    first_pass_turn = 0
    total_elapsed = 0.0
    termination_reason = "compile_stuck"
    model_id = _get_model_id(cfg)

    # 本 sorry 的 token 计数（独立于全局 running）
    blk_prompt = blk_completion = blk_total = 0

    failed_turn_resume = _load_failed_turn_resume(
        tmp_dir=tmp_dir,
        sorry_idx=global_sorry_index,
        max_turns=max_turns,
        err_log_dir=err_log_dir,
        problem=problem,
        model_id=model_id,
    )
    if failed_turn_resume is not None:
        start_turn, prev_code, last_compile_errors = failed_turn_resume
        timeline = _load_same_sorry_attempt_history(
            err_log_dir=err_log_dir,
            problem=problem,
            model_id=model_id,
            sorry_idx=global_sorry_index,
            upto_turn=start_turn - 1,
        )
        # 恢复时同时更新"完整性通过基准"，这样后续失败时能回溯到这个点
        last_integrity_passed_code = prev_code
        last_integrity_passed_errors = last_compile_errors
        print(
            f"[Solver] Resume failed sorry {global_sorry_index}: "
            f"continuing from turn {start_turn - 1} -> {start_turn}"
        )

    # 首轮预取 MCP：让第一次生成也获得检索上下文，而不是失败后才注入。
    if lean_mcp_client is not None and start_turn == 1:
        prefetch_mcp_called = True
        prefetch_prefix = working_text[:block_start] + block_template
        t_mcp = time.monotonic()
        try:
            prefetch_result: LeanMCPQueryResult = lean_mcp_client.gather_failure_context(
                prefetch_prefix,
                problem_path=str(problem.path),
                block_name=sorry_item.block_name,
                line_no=sorry_item.line_no,
                col_no=sorry_item.col_no,
                error_summary=f"initial_attempt:{sorry_item.block_name}",
            )
            used_ms = int((time.monotonic() - t_mcp) * 1000)
            running.mcp_time_ms += used_ms
            running.mcp_calls += prefetch_result.call_count
            running.mcp_failures += prefetch_result.failure_count
            prefetch_mcp_call_count = prefetch_result.call_count
            prefetch_mcp_failure_count = prefetch_result.failure_count
            prefetch_mcp_failed_tools = list(prefetch_result.failed_tools)
            if prefetch_result.context.has_content():
                prefetch_mcp_context_used = True
                last_mcp_ctx = prefetch_result.context
                if mcp_log_dir is not None:
                    rendered_prefetch = _build_mcp_sections(prefetch_result.context)
                    try:
                        _log_mcp_record(
                            problem,
                            model_id,
                            global_sorry_index,
                            1,
                            prefetch_result.context,
                            prefetch_result,
                            rendered_prefetch,
                            mcp_log_dir,
                        )
                    except Exception:
                        pass
            else:
                prefetch_mcp_error_msg = (
                    f"mcp_called_but_empty: tools={prefetch_result.used_tools}, "
                    f"failed={prefetch_result.failed_tools}"
                )
            if prefetch_result.failed_tools:
                print(
                    f"[Solver] MCP WARNING - sorry {global_sorry_index}, prefetch: "
                    f"failed_tools={','.join(prefetch_result.failed_tools)}"
                )
        except Exception as e:
            used_ms = int((time.monotonic() - t_mcp) * 1000)
            running.mcp_time_ms += used_ms
            prefetch_mcp_error_msg = f"mcp_exception: {e}"
            print(
                f"[Solver] MCP ERROR - sorry {global_sorry_index}, prefetch: {e}"
            )

    llm_error_count = 0
    turn = start_turn
    while turn <= max_turns:
        # ---- 构建 prompt ----
        # 只有真正产出过 Lean 代码（非 llm_error）的轮次才算 retry；
        # 若上一轮是 llm_error（API 故障），重新发 first-turn 或上一次有效代码的 retry，
        # 不把 API 错误信息传给模型（模型无法从中获取有用信息）。
        messages = [{"role": "system", "content": _SYSTEM_PROMPT}]
        has_prior_code = prev_code != block_template or last_compile_errors
        if not has_prior_code:
            messages.append({
                "role": "user",
                "content": _FIRST_TURN_USER.format(
                    block_code=block_template,
                    mcp_sections=_build_mcp_sections(last_mcp_ctx),
                ),
            })
        else:
            attempt_history = _render_same_sorry_attempt_history(timeline)
            if same_sorry_history_in_prompt and attempt_history:
                print(
                    f"[Solver] Prompt mode - sorry {global_sorry_index}, turn {turn}: "
                    f"history (records={len(timeline)})"
                )
                messages.append({
                    "role": "user",
                    "content": _RETRY_TURN_USER_WITH_HISTORY.format(
                        block_template=block_template,
                        attempt_history=attempt_history,
                        mcp_sections=_build_mcp_sections(last_mcp_ctx),
                    ),
                })
            else:
                if same_sorry_history_in_prompt and turn > 1:
                    print(
                        f"[Solver] Prompt mode - sorry {global_sorry_index}, turn {turn}: "
                        "last-attempt (history empty)"
                    )
                messages.append({
                    "role": "user",
                    "content": _RETRY_TURN_USER.format(
                        block_template=block_template,
                        prev_code=prev_code,
                        compile_errors=last_compile_errors,
                        mcp_sections=_build_mcp_sections(last_mcp_ctx),
                    ),
                })

        # ---- 调用 LLM ----
        try:
            response, usage = generate_with_usage(messages, cfg, timeout=None)
            new_block_text = extract_lean_code(response)
        except Exception as e:
            import traceback
            llm_error_count += 1
            error_msg = f"LLM_ERROR: {e}"
            error_trace = traceback.format_exc()
            backoff_sec = min(2 ** (llm_error_count - 1), 16)
            llm_error_budget_display = (
                "unlimited"
                if running.llm_error_budget_per_sorry <= 0
                else str(running.llm_error_budget_per_sorry)
            )
            print(
                f"\n[Solver] LLM ERROR - sorry {global_sorry_index}, turn {turn}, "
                f"llm_error={llm_error_count}/{llm_error_budget_display}, "
                f"backoff={backoff_sec}s:"
            )
            print(error_trace)
            timeline.append(AttemptRecord(
                turn=turn, passed=False, code_snippet="",
                errors=error_msg, error_types=["llm_error"],
                elapsed_sec=0.0,
            ))
            # LLM 报错不计入 max_turns；按预算+退避重试。
            termination_reason = "llm_error"
            if (
                running.llm_error_budget_per_sorry > 0
                and llm_error_count >= running.llm_error_budget_per_sorry
            ):
                termination_reason = "llm_error_budget_exceeded"
                break
            limit = running.check_limits(max_tokens=max_tokens, problem_timeout=problem_timeout)
            if limit:
                termination_reason = "limit_exceeded"
                break
            time.sleep(backoff_sec)
            continue

        # 成功拿到一次 LLM 输出后，重置连续 LLM 错误计数
        llm_error_count = 0

        # ---- 更新 token 计数 ----
        running.turns += 1
        running.prompt_tokens += usage.prompt_tokens
        running.completion_tokens += usage.completion_tokens
        running.total_tokens += usage.total_tokens
        blk_prompt += usage.prompt_tokens
        blk_completion += usage.completion_tokens
        blk_total += usage.total_tokens

        # ---- 完整性检查（优先于编译，避免生成含 sorry 的临时文件）----
        integrity_issues = _check_fill_integrity(new_block_text, n_expected_sorry)

        # ---- 保存本轮生成的代码（无论是否通过完整性检查）----
        # 这样后续轮次可以看到此轮的代码和错误，继续改进而不是重新开始
        try:
            code_file = tmp_dir / f"sorry{global_sorry_index}_turn{turn}.lean"
            code_file.write_text(new_block_text, encoding="utf-8")
        except OSError:
            pass  # 代码文件写失败不影响主流程

        # ---- 构建前缀（无论是否编译，MCP 都需要用到）----
        # 无论完整性是否通过，都先构造前缀，供 MCP 分析和编译共用
        mcp_prefix = working_text[:block_start] + new_block_text

        # ---- 构建前缀文件并编译（仅当完整性通过时）----
        if not integrity_issues:
            # 完整性检查通过：进行编译验证
            prefix_for_compile = mcp_prefix
            vr: VerifyResult = verify_lean_string(
                prefix_for_compile, tmp_dir,
                filename=f"sorry{global_sorry_index}_turn{turn}.lean",
                lean_cwd=lean_cwd,
                timeout=verify_timeout,
            )
            total_elapsed += vr.elapsed_sec
        else:
            # 完整性检查失败（含 sorry）：不进行编译，直接返回失败结果
            issue_text = ", ".join(integrity_issues)
            vr = VerifyResult(
                passed=False,
                returncode=1,
                stderr=f"Integrity check failed: {issue_text}"
            )

        # ---- 可选 MCP 增强（编译失败或完整性失败时）----
        if turn == 1 and prefetch_mcp_called:
            mcp_context_used = prefetch_mcp_context_used
            mcp_call_count = prefetch_mcp_call_count
            mcp_failure_count = prefetch_mcp_failure_count
            mcp_failed_tools = list(prefetch_mcp_failed_tools)
            mcp_error_msg = prefetch_mcp_error_msg
        else:
            mcp_context_used = False
            mcp_call_count = 0
            mcp_failure_count = 0
            mcp_failed_tools = []
            mcp_error_msg = ""
        retry_errors = vr.error_summary
        if integrity_issues:
            issue_text = ", ".join(integrity_issues)
            retry_errors = (
                f"{retry_errors}\n\nIntegrity issues:\n- {issue_text}".strip()
            )
        should_call_mcp = (not vr.passed) or bool(integrity_issues)
        # turn1 已做过预取时，避免对同一上下文重复调用 MCP。
        if turn == 1 and prefetch_mcp_called:
            should_call_mcp = False
        if lean_mcp_client is not None and should_call_mcp:
            t_mcp = time.monotonic()
            try:
                mcp_result: LeanMCPQueryResult = lean_mcp_client.gather_failure_context(
                    mcp_prefix,   # 始终使用已定义的 mcp_prefix，不会 NameError
                    problem_path=str(problem.path),
                    block_name=sorry_item.block_name,
                    line_no=sorry_item.line_no,
                    col_no=sorry_item.col_no,
                    error_summary=retry_errors,
                )
                used_ms = int((time.monotonic() - t_mcp) * 1000)
                running.mcp_time_ms += used_ms
                running.mcp_calls += mcp_result.call_count
                running.mcp_failures += mcp_result.failure_count
                mcp_call_count += mcp_result.call_count
                mcp_failure_count += mcp_result.failure_count
                mcp_failed_tools = sorted(set(mcp_failed_tools + list(mcp_result.failed_tools)))
                ctx = mcp_result.context
                if ctx.has_content():
                    last_mcp_ctx = ctx
                    mcp_context_used = True
                    # 记录 MCP 内容到 MCP_LOG（若启用）
                    if mcp_log_dir is not None:
                        rendered_mcp = _build_mcp_sections(ctx)
                        try:
                            _log_mcp_record(
                                problem, model_id, global_sorry_index, turn,
                                ctx, mcp_result, rendered_mcp,
                                mcp_log_dir
                            )
                        except Exception:
                            pass  # MCP 日志写失败不影响主流程
                else:
                    # 调用成功但没有可用内容（搜索无结果 / 返回空）
                    mcp_error_msg = (
                        f"mcp_called_but_empty: tools={mcp_result.used_tools}, "
                        f"failed={mcp_result.failed_tools}"
                    )
                if mcp_result.failed_tools:
                    print(
                        f"[Solver] MCP WARNING - sorry {global_sorry_index}, turn {turn}: "
                        f"failed_tools={','.join(mcp_result.failed_tools)}"
                    )
            except Exception as e:
                used_ms = int((time.monotonic() - t_mcp) * 1000)
                running.mcp_time_ms += used_ms
                mcp_error_msg = f"mcp_exception: {e}"
                print(
                    f"[Solver] MCP ERROR - sorry {global_sorry_index}, turn {turn}: {e}"
                )

        # ---- 通过判定：前缀编译无错误 + 未引入禁止关键字 ----
        block_passed = vr.passed and not integrity_issues

        rec = AttemptRecord(
            turn=turn,
            passed=block_passed,
            code_snippet=new_block_text,
            errors=retry_errors,
            error_types=sorted(vr.error_types),
            elapsed_sec=vr.elapsed_sec,
            prompt_tokens=usage.prompt_tokens,
            completion_tokens=usage.completion_tokens,
            total_tokens=usage.total_tokens,
            mcp_context_used=mcp_context_used,
            mcp_call_count=mcp_call_count,
            mcp_failure_count=mcp_failure_count,
            mcp_failed_tools=mcp_failed_tools,
            mcp_error_msg=mcp_error_msg,
        )
        timeline.append(rec)
        
        # ---- 记录本轮尝试到 ERR_LOG ----
        _log_attempt_record(problem, model_id, global_sorry_index, rec, err_log_dir)
        
        # 更新下一轮 retry 上下文：区分完整性通过和失败
        # - 完整性通过：更新基准代码和错误（这个版本虽然可能编译失败，但至少代码完整）
        # - 完整性失败（含sorry）：回到上次完整性通过的版本，避免 LLM 被失败的中间尝试误导
        if not integrity_issues:
            # 通过完整性检查，这成为新的"基准"供后续回溯
            last_integrity_passed_code = new_block_text
            last_integrity_passed_errors = retry_errors
            prev_code = new_block_text
            last_compile_errors = retry_errors
        else:
            # 完整性失败，保持前次成功的版本作为下一轮参考
            prev_code = last_integrity_passed_code
            last_compile_errors = last_integrity_passed_errors

        # ---- 检查全局限额（token / time）----
        limit = running.check_limits(max_tokens=max_tokens, problem_timeout=problem_timeout)
        if limit:
            termination_reason = "limit_exceeded"
            final_code = new_block_text
            break

        if block_passed:
            passed = True
            first_pass_turn = turn
            final_code = new_block_text
            termination_reason = "completed"
            updated_working = (
                working_text[:block_start]
                + new_block_text
                + ("" if new_block_text.endswith("\n") or working_text[block_end:block_end+1] in ("", "\n") else "\n")
                + working_text[block_end:]
            )
            result = BlockResult(
                block_name=sorry_item.block_name,
                block_index=global_sorry_index,
                sorry_index=global_sorry_index,
                sorry_count=1,
                passed=True,
                attempts=len(timeline),
                first_pass_turn=first_pass_turn,
                total_elapsed_sec=total_elapsed,
                final_code=final_code,
                prompt_tokens=blk_prompt,
                completion_tokens=blk_completion,
                total_tokens=blk_total,
                termination_reason="completed",
                timeline=timeline,
            )
            return result, updated_working

        # 未通过：继续下一轮
        final_code = new_block_text
        turn += 1

    # 所有轮次耗尽（或 LLM 错误 / 限额触发）
    result = BlockResult(
        block_name=sorry_item.block_name,
        block_index=global_sorry_index,
        sorry_index=global_sorry_index,
        sorry_count=1,
        passed=False,
        attempts=len(timeline),
        first_pass_turn=0,
        total_elapsed_sec=total_elapsed,
        final_code=final_code,
        prompt_tokens=blk_prompt,
        completion_tokens=blk_completion,
        total_tokens=blk_total,
        termination_reason=termination_reason,
        timeline=timeline,
    )
    return result, working_text  # working_text 未变


# ---------------------------------------------------------------------------
# 主入口：solve_problem
# ---------------------------------------------------------------------------

def solve_problem(
    problem: Problem,
    cfg: ModelConfig,
    *,
    max_turns: int = 5,
    lean_cwd: str | None = None,
    tmp_dir: Path = Path("/tmp/lean_eval"),
    verify_timeout: float = 120,
    problem_timeout: float = 300,
    max_tokens: int = 0,
    lean_mcp_client: LeanMCPClient | None = None,
    resume: bool = True,
    same_sorry_history_in_prompt: bool = False,
    llm_error_budget_per_sorry: int = 10,
) -> SolveResult:
    """
    顺序前缀编译模式：逐一修复文件中每个 sorry。

    算法：
    - 检测所有 sorry（按源码顺序）。
    - 每次处理当前剩余的第一个 sorry，编译前缀（文件头→当前块末）。
    - 成功后更新 working_text，继续下一个 sorry。
    - 全部解决后做最终全文件重验证。

    限额（文件级）：
    - max_tokens      : 文件内全部 LLM 调用的 token 总用量上限（0 = 不限）
    - problem_timeout : 整道题总解题时间（秒，0 = 不限）
    - max_turns       : 每个 sorry 的最大修复轮次（per-sorry）
    - llm_error_budget_per_sorry : 每个 sorry 的连续 LLM 错误重试预算（0 = 不限）

    断点续传：
    - resume=True 时，若 tmp_dir 中存在 progress.json 和 working_state 快照，
      则从上次中断处继续；否则从头开始。
    - 每个 sorry 处理完毕后，将当前 working_text 快照写入
      tmp_dir/working_state_after_sorry{i}.lean 以便下次续跑。
    """
    tmp_dir = Path(tmp_dir)
    tmp_dir.mkdir(parents=True, exist_ok=True)

    llm_error_budget_per_sorry = max(0, int(llm_error_budget_per_sorry))
    running = RunningTotals(
        t0=time.monotonic(),
        llm_error_budget_per_sorry=llm_error_budget_per_sorry,
    )

    # 一次性检测全部 sorry，确定总数
    sorry_items_initial = detect_sorry_items(problem.full_text)
    n_sorry_found = len(sorry_items_initial)

    # ---- 断点续传：尝试加载上次中断状态 ----
    start_i = 0
    working_text = problem.full_text
    block_results: list[BlockResult] = []

    if resume:
        resume_state = _load_resume_state(tmp_dir, problem.full_text, n_sorry_found)
        if resume_state is not None:
            start_i, working_text, block_results = resume_state
            if start_i > 0:
                print(
                    f"[Solver] Resume: 从 sorry {start_i}/{n_sorry_found} 续跑"
                    f"（已完成 {len(block_results)} 个 sorry"
                    f"，其中 {sum(1 for br in block_results if br.passed)} 个通过）"
                )

    termination_reason = "completed"

    print(
        f"[Solver] {Path(problem.path).stem}: "
        f"{n_sorry_found} sorry found, max_turns={max_turns}, "
        f"max_tokens={'unlimited' if max_tokens == 0 else max_tokens}, "
        f"problem_timeout={'unlimited' if problem_timeout == 0 else f'{problem_timeout}s'}, "
        f"llm_error_budget_per_sorry="
        f"{'unlimited' if llm_error_budget_per_sorry == 0 else llm_error_budget_per_sorry}, "
        f"mcp={'on' if lean_mcp_client is not None else 'off'}, "
        f"same_sorry_history_prompt={'on' if same_sorry_history_in_prompt else 'off'}"
        + (f", resuming_from={start_i}" if start_i > 0 else "")
    )

    for i in range(start_i, n_sorry_found):
        # ---- 检查全局限额 ----
        limit = running.check_limits(max_tokens=max_tokens, problem_timeout=problem_timeout)
        if limit:
            print(f"[Solver] Global limit reached before sorry {i}: {limit}")
            termination_reason = "limit_exceeded"
            break

        # ---- 重新检测当前 working_text 中的 sorry ----
        # 每次重检是因为上一轮修复后偏移量已经改变
        remaining = detect_sorry_items(working_text)
        if not remaining:
            break  # 所有 sorry 已解决（LLM 可能一次填了多个）

        # 定位本轮目标 sorry：
        # passed_so_far 个 sorry 已从 working_text 消失，
        # 未通过的 sorry 仍留在 working_text 中。
        # → 本轮应处理 remaining 中第 (i - passed_so_far) 个
        passed_so_far = sum(1 for br in block_results if br.passed)
        target_idx = i - passed_so_far

        if target_idx >= len(remaining):
            # 剩余 sorry 已全部被顺带解决（前面轮次 LLM 多填了）
            break

        current_sorry = remaining[target_idx]
        print(
            f"[Solver] sorry {i + 1}/{n_sorry_found}: "
            f"block='{current_sorry.block_name}', "
            f"L{current_sorry.line_no}C{current_sorry.col_no}  "
            f"[elapsed={running.elapsed():.1f}s, "
            f"tokens={running.total_tokens}, turns={running.turns}]"
        )

        br, updated = _solve_one_sorry(
            current_sorry, i, working_text, cfg,
            lean_cwd=lean_cwd,
            tmp_dir=tmp_dir,
            verify_timeout=verify_timeout,
            running=running,
            max_turns=max_turns,
            max_tokens=max_tokens,
            problem_timeout=problem_timeout,
            problem=problem,
            err_log_dir=Path("ERR_LOG"),
            mcp_log_dir=Path("MCP_LOG"),
            lean_mcp_client=lean_mcp_client,
            same_sorry_history_in_prompt=same_sorry_history_in_prompt,
        )
        block_results.append(br)

        if br.passed:
            working_text = updated
            print(f"[Solver] sorry {i + 1} PASS (turn {br.first_pass_turn})")
        else:
            print(
                f"[Solver] sorry {i + 1} FAIL "
                f"({br.attempts} attempts, reason={br.termination_reason})"
            )

        # 若因限额终止，更新文件级 termination_reason 并立即退出
        if br.termination_reason == "limit_exceeded":
            termination_reason = "limit_exceeded"
            break
        if br.termination_reason == "llm_error":
            termination_reason = "llm_error"
            # LLM 错误不强制终止，继续尝试下一个 sorry
        if br.termination_reason == "llm_error_budget_exceeded":
            termination_reason = "llm_error_budget_exceeded"
            # 单个 sorry 的 LLM 错误预算耗尽，不强制终止整题

        # 保存实时进度 + working_text 快照（供断点续传）
        _save_progress(tmp_dir, i, n_sorry_found, running, block_results)
        _save_working_state(tmp_dir, i, working_text)

    # ---- 补充因 LLM 顺带解决产生的缺失记录 ----
    remaining_after = detect_sorry_items(working_text)
    if len(block_results) < n_sorry_found and not remaining_after:
        for extra_i in range(len(block_results), n_sorry_found):
            block_results.append(BlockResult(
                block_name="<auto_solved>",
                block_index=extra_i,
                sorry_index=extra_i,
                sorry_count=1,
                passed=True,
                attempts=0,
                first_pass_turn=0,
                total_elapsed_sec=0.0,
                final_code="",
                termination_reason="auto_solved",
            ))

    total_elapsed = running.elapsed()
    passed_count = sum(1 for br in block_results if br.passed)

    # ---- 全文件最终重验证 ----
    final_verify_passed: bool | None = None
    final_verify_issues: list[str] = []

    all_solved = (
        passed_count == n_sorry_found
        and n_sorry_found > 0
        and not detect_sorry_items(working_text)
    )
    if all_solved:
        print(f"[Solver] Final full-file recompilation for {Path(problem.path).stem} ...")
        final_vr = verify_lean_string(
            working_text, tmp_dir,
            filename="_final_verify.lean",
            lean_cwd=lean_cwd,
            timeout=verify_timeout,
        )
        final_integrity = check_proof_integrity(working_text)
        final_verify_passed = final_vr.passed and not final_integrity
        if not final_verify_passed:
            reason_parts: list[str] = []
            if not final_vr.passed:
                reason_parts.append(f"compile errors: {final_vr.error_summary[:2000]}")
            if final_integrity:
                reason_parts.append(f"integrity: {final_integrity}")
            final_verify_issues = reason_parts
            print(f"[Solver] FINAL VERIFY FAILED: {'; '.join(reason_parts)}")
            for br in block_results:
                br.passed = False
                br.first_pass_turn = 0
            passed_count = 0
            if termination_reason == "completed":
                termination_reason = "compile_stuck"
        else:
            print(f"[Solver] Final verify PASS.")
            termination_reason = "completed"

    return SolveResult(
        problem_path=str(problem.path),
        model=cfg.model.split("/")[-1],
        total_blocks=n_sorry_found,
        passed_blocks=passed_count,
        all_passed=(passed_count == n_sorry_found and n_sorry_found > 0),
        total_attempts=sum(br.attempts for br in block_results),
        total_elapsed_sec=total_elapsed,
        prompt_tokens=running.prompt_tokens,
        completion_tokens=running.completion_tokens,
        total_tokens=running.total_tokens,
        block_results=block_results,
        final_verify_passed=final_verify_passed,
        final_verify_issues=final_verify_issues,
        n_sorry_found=n_sorry_found,
        termination_reason=termination_reason,
        mcp_enabled=(lean_mcp_client is not None),
        mcp_calls=running.mcp_calls,
        mcp_failures=running.mcp_failures,
        mcp_time_ms=running.mcp_time_ms,
    )
