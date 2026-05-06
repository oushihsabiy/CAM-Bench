#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
run_eval.py: Lean 题目难度评测 Pipeline 主入口。

复用现有 experiments JSON 格式：
[
  {
    "problem": "/path/to/problem.lean",
    "model": "Goedel-Prover-V2-32B",
    "base_url": "http://172.18.103.1:8000/v1",
    "api_key": "EMPTY",           // 可选，默认 EMPTY
    "lean_cwd": "/path/to/lean",  // 可选
    "pass_n": 3,                  // 可选，每道题重复几轮（默认 1）
    "max_turns": 5,               // 可选，每个 sorry 块最大修复轮数
    "llm_error_budget_per_sorry": 11, // 可选，每个 sorry 连续 LLM 错误重试预算；0 = 不限
    "workers": 2                  // 可选（本脚本中用于并发题目数）
  },
  ...
]

用法：
  python -m eval.run_eval --config experiments.json
  python -m eval.run_eval --config experiments.json --parallel 4 --dry-run
"""

from __future__ import annotations

import argparse
import copy
import json
import os
import shlex
import sys
import time
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - py<3.11 fallback
    tomllib = None

# 支持 python -m eval.run_eval 和直接 python eval/run_eval.py 两种方式
if __name__ == "__main__" and __package__ is None:
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    __package__ = "eval"

from .evaluator import ProblemMetrics, compute_metrics
from .lean_mcp_client import LeanMCPClient, LeanMCPConfig
from .llm_client import ModelConfig
from .posterior_scorer import score_posterior
from .prior_scorer import score_prior
from .problem_loader import load_problem
from .reporter import (
    print_report,
    save_eval_excel,
    save_eval_markdown_report,
    save_eval_report,
    save_solve_result,
)
from .solver import SolveResult, problem_log_id_from_path, solve_problem


PROJECT_ROOT = Path(__file__).resolve().parents[1]


def _as_bool(v: object) -> bool:
    if isinstance(v, bool):
        return v
    if isinstance(v, (int, float)):
        return bool(v)
    if isinstance(v, str):
        return v.strip().lower() in {"1", "true", "yes", "on"}
    return False


def _load_optional_json_dict(path: Path) -> dict:
    if not path.exists():
        return {}
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"Expected JSON object in {path}")
    return data


def _load_experiments_and_options(path: Path) -> tuple[list[dict], bool]:
    """Load experiments and optional global switches from config JSON.

    Supported formats:
    - Legacy: top-level list of experiment dicts
    - Extended: {"experiments": [...], "difficulty_assessment": true/false}
    """
    data = json.loads(path.read_text(encoding="utf-8"))
    if isinstance(data, list):
        return data, False
    if isinstance(data, dict):
        exps = data.get("experiments", data.get("exps", []))
        if not isinstance(exps, list):
            raise ValueError("config.experiments must be a JSON array")
        difficulty_assessment = _as_bool(data.get("difficulty_assessment", False))
        return exps, difficulty_assessment
    raise ValueError("Config JSON must be a list or object with 'experiments'")


def _normalize_env_vars(v: object) -> dict[str, str]:
    if not isinstance(v, dict):
        return {}
    out: dict[str, str] = {}
    for k, val in v.items():
        key = str(k or "").strip()
        if not key:
            continue
        out[key] = str(val)
    return out


def _detect_codex_home(args: argparse.Namespace) -> Path | None:
    if getattr(args, "codex_home", None):
        p = Path(str(args.codex_home)).expanduser().resolve()
        return p if p.exists() else None

    env_codex_home = os.getenv("CODEX_HOME", "").strip()
    if env_codex_home:
        p = Path(env_codex_home).expanduser().resolve()
        return p if p.exists() else None

    inferred = (PROJECT_ROOT / ".codex_home").resolve()
    if inferred.exists():
        return inferred
    return None


def _load_mcp_from_codex_home(codex_home: Path | None) -> tuple[dict[str, object], str]:
    if codex_home is None:
        return {}, ""
    if tomllib is None:
        print("[Eval] WARNING: tomllib unavailable, skip .codex_home MCP config", file=sys.stderr)
        return {}, ""

    cfg_path = codex_home / "config.toml"
    if not cfg_path.exists():
        return {}, ""

    try:
        with cfg_path.open("rb") as f:
            data = tomllib.load(f)
    except Exception as err:
        print(f"[Eval] WARNING: failed to parse {cfg_path}: {err}", file=sys.stderr)
        return {}, ""

    if not isinstance(data, dict):
        return {}, str(cfg_path)
    mcp_servers = data.get("mcp_servers")
    if not isinstance(mcp_servers, dict):
        return {}, str(cfg_path)
    lean_lsp = mcp_servers.get("lean-lsp")
    if not isinstance(lean_lsp, dict):
        return {}, str(cfg_path)

    command = str(lean_lsp.get("command", "") or "").strip()
    args_list = lean_lsp.get("args", [])
    argv: list[str] = []
    if command:
        argv.append(command)
    if isinstance(args_list, list):
        argv.extend(str(a) for a in args_list if str(a).strip())
    command_line = " ".join(shlex.quote(x) for x in argv) if argv else ""

    env_cfg = _normalize_env_vars(lean_lsp.get("env", {}))

    out: dict[str, object] = {
        "lean_mcp_env_vars": env_cfg,
    }
    if command_line:
        # codex_home mcp_servers.* uses command+args (stdio semantics)
        out["lean_mcp_transport"] = "stdio"
        out["lean_mcp_command"] = command_line
    return out, str(cfg_path)


def _resolve_mcp_defaults(args: argparse.Namespace) -> dict[str, object]:
    codex_home = _detect_codex_home(args)
    codex_cfg, codex_cfg_path = _load_mcp_from_codex_home(codex_home)

    mcp_config_path = Path(args.lean_mcp_config).resolve() if args.lean_mcp_config else None
    file_cfg = _load_optional_json_dict(mcp_config_path) if mcp_config_path else {}
    merged_cfg = {**codex_cfg, **file_cfg}

    enabled = _as_bool(merged_cfg.get("lean_mcp_enabled", False))
    if args.lean_mcp_enabled is not None:
        enabled = args.lean_mcp_enabled

    transport = str(merged_cfg.get("lean_mcp_transport", "http"))
    if args.lean_mcp_transport is not None:
        transport = args.lean_mcp_transport
    # If user explicitly enables MCP from CLI but does not pick a transport,
    # default to python transport so calls go through mcp_helper.py.
    if args.lean_mcp_enabled is True and args.lean_mcp_transport is None:
        transport = "python"

    endpoint = str(merged_cfg.get("lean_mcp_endpoint", ""))
    if args.lean_mcp_endpoint is not None:
        endpoint = args.lean_mcp_endpoint

    command = str(merged_cfg.get("lean_mcp_command", ""))
    if args.lean_mcp_command is not None:
        command = args.lean_mcp_command

    timeout_sec = float(merged_cfg.get("lean_mcp_timeout", 5.0))
    if args.lean_mcp_timeout is not None:
        timeout_sec = args.lean_mcp_timeout

    tools = merged_cfg.get("lean_mcp_tools", {})
    if not isinstance(tools, (dict, list)):
        tools = {}
    strategy = str(merged_cfg.get("tool_selection_strategy", "single"))
    if args.lean_mcp_tool_selection_strategy is not None:
        strategy = args.lean_mcp_tool_selection_strategy
    tool_mode = str(merged_cfg.get("lean_mcp_tool_mode", "targeted"))
    pool_size = int(merged_cfg.get("lean_mcp_pool_size", 1) or 1)
    mcp_repo_path = str(merged_cfg.get("lean_mcp_repo_path", "") or "")
    env_vars = _normalize_env_vars(merged_cfg.get("lean_mcp_env_vars", {}))

    source_labels: list[str] = []
    if codex_cfg_path:
        source_labels.append(f"codex_home:{codex_cfg_path}")
    if mcp_config_path:
        source_labels.append(f"json:{mcp_config_path}")
    source = " -> ".join(source_labels) if source_labels else "built-in defaults"

    return {
        "path": str(mcp_config_path) if mcp_config_path else "",
        "codex_home": str(codex_home) if codex_home else "",
        "codex_path": codex_cfg_path,
        "source": source,
        "enabled": enabled,
        "transport": transport,
        "endpoint": endpoint,
        "command": command,
        "timeout_sec": timeout_sec,
        "tools": copy.deepcopy(tools),
        "tool_selection_strategy": strategy,
        "tool_mode": tool_mode,
        "pool_size": pool_size,
        "mcp_repo_path": mcp_repo_path,
        "env_vars": env_vars,
    }


# ---------------------------------------------------------------------------
# 从实验 JSON 条目构建 ModelConfig
# ---------------------------------------------------------------------------

def _build_model_cfg(exp: dict) -> ModelConfig:
    # `max_tokens_per_call`: per-LLM-call output token limit sent to the API.
    # `max_tokens` (legacy key) is now reinterpreted as the file-level total token
    # budget; use the explicit `max_tokens_per_call` key for the per-call limit.
    per_call = int(exp.get("max_tokens_per_call", 32768))
    return ModelConfig(
        model=exp["model"],
        base_url=exp["base_url"],
        api_key=exp.get("api_key", "EMPTY"),
        temperature=exp.get("temperature", 0.6),
        max_tokens=per_call,
        stream=bool(exp.get("stream", False)),
    )


def _build_judge_cfg(args: argparse.Namespace, exps: list[dict]) -> ModelConfig | None:
    """构建先验/后验评分使用的 LLM 配置。"""
    if args.judge_model and args.judge_base_url:
        return ModelConfig(
            model=args.judge_model,
            base_url=args.judge_base_url,
            api_key=args.judge_api_key or "EMPTY",
            temperature=args.judge_temperature,
            max_tokens=2048,
        )

    if exps:
        first = exps[0]
        return ModelConfig(
            model=first["model"],
            base_url=first["base_url"],
            api_key=first.get("api_key", "EMPTY"),
            temperature=args.judge_temperature,
            max_tokens=2048,
        )
    return None


def _build_best_proof_code(results: list[SolveResult]) -> str:
    """从多次运行中选出最佳一次，并拼接该次各 block 的最终代码。"""
    if not results:
        return ""

    best = max(
        results,
        key=lambda r: (
            int(r.all_passed),
            r.passed_blocks,
            -r.total_attempts,
            -r.total_elapsed_sec,
        ),
    )
    blocks = sorted(best.block_results, key=lambda b: b.block_index)
    parts = [b.final_code for b in blocks if b.final_code]
    return "\n\n".join(parts)


def _compute_prior_posterior_details(
    by_problem: dict[str, list[SolveResult]],
    judge_cfg: ModelConfig | None,
) -> dict[str, dict]:
    """计算每道题先验/后验维度评分，供 eval_report 和 Excel 输出。"""
    details: dict[str, dict] = {}
    if judge_cfg is None:
        return details

    for prob_path, results in by_problem.items():
        prior_payload = {
            "raw_score": 0.0,
            "prompt_tokens": 0,
            "completion_tokens": 0,
            "total_tokens": 0,
            "dimensions": {},
        }
        posterior_payload = {
            "raw_score": 0.0,
            "prompt_tokens": 0,
            "completion_tokens": 0,
            "total_tokens": 0,
            "dimensions": {},
        }

        try:
            problem = load_problem(prob_path)
            prior = score_prior(problem, judge_cfg)
            prior_payload = {
                "raw_score": prior.raw_score,
                "prompt_tokens": prior.prompt_tokens,
                "completion_tokens": prior.completion_tokens,
                "total_tokens": prior.total_tokens,
                "dimensions": {
                    "hypothesis_count": prior.hypothesis_count,
                    "sorry_block_count": prior.sorry_block_count,
                    "statement_length": prior.statement_length,
                    "structural_complexity": prior.structural_complexity,
                    "concept_complexity": prior.concept_complexity,
                    "formalization_gap": prior.formalization_gap,
                    "type_sophistication": prior.type_sophistication,
                },
            }
        except Exception as e:
            print(f"[Eval] WARNING: prior scoring failed for {Path(prob_path).stem}: {e}")

        try:
            proof_code = _build_best_proof_code(results)
            if proof_code:
                posterior = score_posterior(prob_path, proof_code, judge_cfg)
                posterior_payload = {
                    "raw_score": posterior.raw_score,
                    "prompt_tokens": posterior.prompt_tokens,
                    "completion_tokens": posterior.completion_tokens,
                    "total_tokens": posterior.total_tokens,
                    "dimensions": {
                        "structure": posterior.structure,
                        "semantic": posterior.semantic,
                        "library": posterior.library,
                        "type": posterior.type_score,
                        "search": posterior.search,
                    },
                }
        except Exception as e:
            print(f"[Eval] WARNING: posterior scoring failed for {Path(prob_path).stem}: {e}")

        details[prob_path] = {
            "prior": prior_payload,
            "posterior": posterior_payload,
        }

    return details


def _save_retest_llm_error_list(results: list[SolveResult]) -> Path:
    """Collect llm_error problems and save them to retest/retest.json."""
    retest_dir = PROJECT_ROOT / "retest"
    retest_file = retest_dir / "retest.json"
    retest_dir.mkdir(parents=True, exist_ok=True)

    llm_error_runs = [r for r in results if str(r.termination_reason) == "llm_error"]

    by_problem: dict[str, dict] = {}
    for r in llm_error_runs:
        p = Path(r.problem_path)
        key = str(p)
        row = by_problem.get(key)
        if row is None:
            row = {
                "problem": str(p),
                "problem_dir": str(p.parent),
                "folder": str(p.parent),   # alias: 所在文件夹
                "problem_no": p.stem,      # alias: 题号
                "llm_error_runs": 0,
                "models": set(),
            }
            by_problem[key] = row
        row["llm_error_runs"] += 1
        row["models"].add(str(r.model or "unknown"))

    problems = []
    for key in sorted(by_problem.keys()):
        row = by_problem[key]
        problems.append(
            {
                "problem": row["problem"],
                "problem_dir": row["problem_dir"],
                "folder": row["folder"],
                "problem_no": row["problem_no"],
                "llm_error_runs": int(row["llm_error_runs"]),
                "models": sorted(row["models"]),
            }
        )

    payload = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "total_llm_error_runs": len(llm_error_runs),
        "total_llm_error_problems": len(problems),
        "problems": problems,
    }
    retest_file.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
    return retest_file


# ---------------------------------------------------------------------------
# 单条实验执行
# ---------------------------------------------------------------------------

def _run_one(
    exp: dict,
    log_dir: Path,
    default_max_turns: int,
    default_lean_cwd: str | None,
    verify_timeout: float,
    problem_timeout: float,
    default_max_tokens: int,
    default_llm_error_budget_per_sorry: int,
    default_same_sorry_history_in_prompt: bool,
    default_lean_mcp_enabled: bool,
    default_lean_mcp_transport: str,
    default_lean_mcp_endpoint: str,
    default_lean_mcp_command: str,
    default_lean_mcp_timeout: float,
    default_lean_mcp_tools: object,
    default_tool_selection_strategy: str,
    default_lean_mcp_tool_mode: str,
    default_lean_mcp_pool_size: int,
    default_lean_mcp_repo_path: str,
    default_lean_mcp_env_vars: dict[str, str],
    dry_run: bool,
    resume: bool = True,
) -> SolveResult | None:
    # 解析 problem 路径：优先使用绝对路径；若为相对路径且提供了 lean_cwd，则基于 lean_cwd 解析
    raw_problem = exp["problem"]
    problem_path = Path(raw_problem)
    lean_cwd = exp.get("lean_cwd", default_lean_cwd)
    if not problem_path.is_absolute() and lean_cwd:
        problem_path = Path(lean_cwd) / problem_path
    model_cfg = _build_model_cfg(exp)
    max_turns = int(exp.get("max_turns", default_max_turns))
    verify_timeout = float(exp.get("verify_timeout", verify_timeout))
    problem_timeout = float(exp.get("problem_timeout", problem_timeout))
    # `max_tokens` = file-level total token budget (0 = unlimited)
    max_tokens_budget = int(exp.get("max_tokens", default_max_tokens))
    llm_error_budget_per_sorry = max(
        0,
        int(exp.get("llm_error_budget_per_sorry", default_llm_error_budget_per_sorry)),
    )
    same_sorry_history_in_prompt = _as_bool(
        exp.get("same_sorry_history_in_prompt", default_same_sorry_history_in_prompt)
    )
    mcp_cfg = LeanMCPConfig(
        enabled=_as_bool(exp.get("lean_mcp_enabled", default_lean_mcp_enabled)),
        transport=str(exp.get("lean_mcp_transport", default_lean_mcp_transport)),
        endpoint=str(exp.get("lean_mcp_endpoint", default_lean_mcp_endpoint)),
        command=str(exp.get("lean_mcp_command", default_lean_mcp_command)),
        timeout_sec=float(exp.get("lean_mcp_timeout", default_lean_mcp_timeout)),
        tools=copy.deepcopy(exp.get("lean_mcp_tools", default_lean_mcp_tools)),
        tool_selection_strategy=str(
            exp.get("tool_selection_strategy", default_tool_selection_strategy)
        ),
        tool_mode=str(exp.get("lean_mcp_tool_mode", default_lean_mcp_tool_mode)),
        pool_size=int(exp.get("lean_mcp_pool_size", default_lean_mcp_pool_size) or 1),
        mcp_repo_path=str(exp.get("lean_mcp_repo_path", default_lean_mcp_repo_path) or ""),
        env_vars=_normalize_env_vars(exp.get("lean_mcp_env_vars", default_lean_mcp_env_vars)),
    )
    mcp_client = LeanMCPClient(mcp_cfg) if mcp_cfg.enabled else None
    model_short = model_cfg.model.split("/")[-1]
    print(f"[Eval] Loading {problem_path} for {model_short} ...")
    try:
        problem = load_problem(problem_path)
    except FileNotFoundError:
        print(f"[Eval] SKIP: problem file not found: {problem_path}")
        return None

    if problem.total_sorry_count == 0:
        print(f"[Eval] SKIP: no sorry in {problem_path}")
        return None

    print(
        f"[Eval] {Path(problem_path).stem}: "
        f"{len(problem.blocks)} sorry-blocks, "
        f"{problem.total_sorry_count} total sorry, "
        f"max_turns={max_turns}, model={model_short}, mcp={'on' if mcp_client else 'off'}, "
        f"same_sorry_history_prompt={'on' if same_sorry_history_in_prompt else 'off'}, "
        f"mcp_transport={mcp_cfg.transport if mcp_client else 'n/a'}, "
        f"mcp_strategy={mcp_cfg.tool_selection_strategy if mcp_client else 'n/a'}"
    )

    if dry_run:
        print(f"[Eval] DRY-RUN: would solve {problem_path}")
        return None

    problem_log_id = problem_log_id_from_path(problem_path)
    tmp_dir = log_dir / "_tmp" / f"{problem_log_id}_{model_short}"
    result = solve_problem(
        problem, model_cfg,
        max_turns=max_turns,
        lean_cwd=lean_cwd,
        tmp_dir=tmp_dir,
        verify_timeout=verify_timeout,
        problem_timeout=problem_timeout,
        max_tokens=max_tokens_budget,
        llm_error_budget_per_sorry=llm_error_budget_per_sorry,
        lean_mcp_client=mcp_client,
        resume=resume,
        same_sorry_history_in_prompt=same_sorry_history_in_prompt,
    )

    # 保存到 LOG
    out_dir = save_solve_result(result, log_dir, tag="eval")
    status = "PASS" if result.all_passed else f"PARTIAL({result.passed_blocks}/{result.total_blocks})"
    print(
        f"[Eval] {Path(problem_path).stem}/{model_short}: "
        f"{status}, sorry={result.n_sorry_found}, "
        f"attempts={result.total_attempts}, tokens={result.total_tokens}, "
        f"time={result.total_elapsed_sec:.1f}s, reason={result.termination_reason}, "
        f"mcp_calls={result.mcp_calls}, mcp_failures={result.mcp_failures} "
        f"-> {out_dir.name}"
    )
    return result


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(
        description="Lean 题目难度评测 Pipeline",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("--config", required=True, help="实验配置 JSON（复用现有格式）")
    parser.add_argument("--log-dir", default=str(PROJECT_ROOT / "LOG"), help="日志输出目录")
    parser.add_argument("--output", default=str(PROJECT_ROOT / "eval_report.json"), help="汇总报告路径")
    parser.add_argument("--excel-output", default=None, help="Excel 输出路径（默认与 --output 同名 .xlsx）")
    parser.add_argument("--markdown-output", default=None, help="Markdown 输出路径（默认与 --output 同名 .md）")
    parser.add_argument("--max-turns", type=int, default=5, help="每个 sorry 最大修复轮数")
    parser.add_argument("--max-tokens", type=int, default=0, help="文件级 token 总预算（0 = 不限，对应 task.json max_tokens 字段）")
    parser.add_argument(
        "--llm-error-budget-per-sorry",
        type=int,
        default=11,
        help="每个 sorry 连续 LLM API 错误重试预算；0 = 不限，一直重试直到成功或触发全局限额",
    )
    parser.add_argument(
        "--same-sorry-history-in-prompt",
        action="store_true",
        help="在 retry prompt 中附带当前 sorry 之前各轮尝试与错误；不包含更早 sorry",
    )
    parser.add_argument("--lean-cwd", default=None, help="lean 工作目录（含 lakefile.lean）")
    parser.add_argument("--verify-timeout", type=float, default=0, help="lean 编译超时(秒，<=0 表示不限)")
    parser.add_argument("--problem-timeout", type=float, default=300, help="单题总解题时间上限(秒)，默认 300")
    parser.add_argument("--lean-mcp-config", default=str(PROJECT_ROOT / "eval" / "mcp_config.json"), help="Lean MCP 默认配置 JSON")
    parser.add_argument("--codex-home", default=None, help=".codex_home 目录路径（默认自动探测）")
    parser.add_argument("--lean-mcp-enabled", action="store_true", default=None, help="启用 Lean MCP 失败重试上下文增强")
    parser.add_argument("--lean-mcp-transport", default=None, choices=["http", "stdio", "python"], help="Lean MCP 传输方式")
    parser.add_argument("--lean-mcp-endpoint", default=None, help="Lean MCP HTTP endpoint")
    parser.add_argument("--lean-mcp-command", default=None, help="Lean MCP stdio 命令（transport=stdio 时使用）")
    parser.add_argument("--lean-mcp-timeout", type=float, default=None, help="Lean MCP 单次调用超时(秒)")
    parser.add_argument("--lean-mcp-tool-selection-strategy", default=None, choices=["single", "fallback", "sequential", "all", "error_based"], help="Lean MCP 多工具选择策略")
    parser.add_argument("--parallel", type=int, default=1, help="并发题目数")
    parser.add_argument("--dry-run", action="store_true", help="只打印计划，不实际执行")
    parser.add_argument("--skip-existing", action="store_true", help="跳过 LOG 中已有结果的实验")
    parser.add_argument(
        "--no-resume",
        action="store_true",
        help="禁用断点续传；即使 _tmp 中有已有进度也从头开始",
    )
    parser.add_argument("--judge-model", default=None, help="先验/后验评分模型名")
    parser.add_argument("--judge-base-url", default=None, help="先验/后验评分 API base URL")
    parser.add_argument("--judge-api-key", default=None, help="先验/后验评分 API key")
    parser.add_argument("--judge-temperature", type=float, default=0.3, help="先验/后验评分温度")
    parser.add_argument(
        "--difficulty-assessment",
        dest="difficulty_assessment",
        action="store_true",
        help="启用难度评测（prior/posterior 评分）；默认关闭",
    )
    parser.add_argument(
        "--no-difficulty-assessment",
        dest="difficulty_assessment",
        action="store_false",
        help="禁用难度评测（prior/posterior 评分）",
    )
    parser.set_defaults(difficulty_assessment=None)
    args = parser.parse_args()

    config_file = Path(args.config).resolve()
    log_dir = Path(args.log_dir).resolve()
    output_file = Path(args.output).resolve()
    excel_output_file = (
        Path(args.excel_output).resolve() if args.excel_output else output_file.with_suffix(".xlsx")
    )
    markdown_output_file = (
        Path(args.markdown_output).resolve() if args.markdown_output else output_file.with_suffix(".md")
    )

    if not config_file.exists():
        print(f"[Eval] ERROR: config not found: {config_file}", file=sys.stderr)
        return 1

    exps, cfg_difficulty_assessment = _load_experiments_and_options(config_file)
    enable_difficulty_assessment = (
        cfg_difficulty_assessment
        if args.difficulty_assessment is None
        else bool(args.difficulty_assessment)
    )
    log_dir.mkdir(parents=True, exist_ok=True)
    mcp_defaults = _resolve_mcp_defaults(args)

    print(f"[Eval] Config: {config_file} ({len(exps)} experiments)")
    print(f"[Eval] Log dir: {log_dir}")
    verify_timeout_display = "unlimited" if args.verify_timeout <= 0 else f"{args.verify_timeout}s"
    problem_timeout_display = "unlimited" if args.problem_timeout <= 0 else f"{args.problem_timeout}s"
    print(
        f"[Eval] Max turns: {args.max_turns}, "
        f"max tokens budget: {'unlimited' if args.max_tokens == 0 else args.max_tokens}, "
        f"llm error budget per sorry: "
        f"{'unlimited' if args.llm_error_budget_per_sorry == 0 else args.llm_error_budget_per_sorry}, "
        f"verify timeout: {verify_timeout_display}, problem timeout: {problem_timeout_display}"
    )
    print(
        f"[Eval] Lean MCP: {'enabled' if mcp_defaults['enabled'] else 'disabled'} "
        f"(transport={mcp_defaults['transport']}, timeout={mcp_defaults['timeout_sec']}s, "
        f"strategy={mcp_defaults['tool_selection_strategy']}, config={mcp_defaults['path'] or 'none'})"
    )
    print(f"[Eval] Lean MCP config source: {mcp_defaults.get('source', 'unknown')}")
    if mcp_defaults.get("codex_home"):
        print(f"[Eval] Codex home: {mcp_defaults.get('codex_home')}")
    if mcp_defaults["enabled"]:
        if isinstance(mcp_defaults["tools"], dict):
            print(f"[Eval] Lean MCP tools: {', '.join(mcp_defaults['tools'].keys())}")
        elif isinstance(mcp_defaults["tools"], list):
            print(f"[Eval] Lean MCP tools: {', '.join(str(x) for x in mcp_defaults['tools'])}")
        print(
            f"[Eval] Lean MCP mode: tool_mode={mcp_defaults.get('tool_mode', 'targeted')}, "
            f"pool_size={mcp_defaults.get('pool_size', 1)}, "
            f"repo_path={mcp_defaults.get('mcp_repo_path', '') or 'auto'}"
        )
        if mcp_defaults.get("env_vars"):
            env_keys = sorted(str(k) for k in (mcp_defaults.get("env_vars") or {}).keys())
            print(f"[Eval] Lean MCP env vars from config: {', '.join(env_keys)}")
    print(f"[Eval] Parallel: {args.parallel}")
    print(
        f"[Eval] Difficulty assessment: "
        f"{'enabled' if enable_difficulty_assessment else 'disabled'}"
    )

    judge_cfg = None
    if enable_difficulty_assessment:
        judge_cfg = _build_judge_cfg(args, exps)
        if judge_cfg is not None:
            print(f"[Eval] Prior/Posterior judge model: {judge_cfg.model}")
        else:
            print("[Eval] WARNING: no judge config found; prior/posterior details will be zeros")

    # ---- 展开 pass_n（同一实验重复 N 次）----
    expanded: list[dict] = []
    for exp in exps:
        pass_n = int(exp.get("pass_n", 1))
        for _ in range(pass_n):
            expanded.append(exp)

    print(f"[Eval] Expanded to {len(expanded)} runs (with pass_n repeats)")

    # ---- 执行 ----
    all_results: list[SolveResult] = []
    t0 = time.monotonic()

    if args.parallel <= 1:
        for exp in expanded:
            r = _run_one(
                exp,
                log_dir,
                args.max_turns,
                args.lean_cwd,
                args.verify_timeout,
                args.problem_timeout,
                args.max_tokens,
                args.llm_error_budget_per_sorry,
                args.same_sorry_history_in_prompt,
                bool(mcp_defaults["enabled"]),
                str(mcp_defaults["transport"]),
                str(mcp_defaults["endpoint"]),
                str(mcp_defaults["command"]),
                float(mcp_defaults["timeout_sec"]),
                copy.deepcopy(mcp_defaults["tools"]),
                str(mcp_defaults["tool_selection_strategy"]),
                str(mcp_defaults.get("tool_mode", "targeted")),
                int(mcp_defaults.get("pool_size", 1) or 1),
                str(mcp_defaults.get("mcp_repo_path", "") or ""),
                copy.deepcopy(_normalize_env_vars(mcp_defaults.get("env_vars", {}))),
                args.dry_run,
                not args.no_resume,
            )
            if r is not None:
                all_results.append(r)
    else:
        with ThreadPoolExecutor(max_workers=args.parallel) as pool:
            futs = [
                pool.submit(
                    _run_one,
                    exp,
                    log_dir,
                    args.max_turns,
                    args.lean_cwd,
                    args.verify_timeout,
                    args.problem_timeout,
                    args.max_tokens,
                    args.llm_error_budget_per_sorry,
                    args.same_sorry_history_in_prompt,
                    bool(mcp_defaults["enabled"]),
                    str(mcp_defaults["transport"]),
                    str(mcp_defaults["endpoint"]),
                    str(mcp_defaults["command"]),
                    float(mcp_defaults["timeout_sec"]),
                    copy.deepcopy(mcp_defaults["tools"]),
                    str(mcp_defaults["tool_selection_strategy"]),
                    str(mcp_defaults.get("tool_mode", "targeted")),
                    int(mcp_defaults.get("pool_size", 1) or 1),
                    str(mcp_defaults.get("mcp_repo_path", "") or ""),
                    copy.deepcopy(_normalize_env_vars(mcp_defaults.get("env_vars", {}))),
                    args.dry_run,
                    not args.no_resume,
                )
                for exp in expanded
            ]
            for fut in as_completed(futs):
                try:
                    r = fut.result()
                    if r is not None:
                        all_results.append(r)
                except Exception as e:
                    print(f"[Eval] ERROR in worker: {e}")

    total_time = time.monotonic() - t0
    print(f"\n[Eval] Completed {len(all_results)} runs in {total_time:.1f}s")

    if args.dry_run or not all_results:
        return 0

    # ---- 按 problem 聚合 ----
    by_problem: dict[str, list[SolveResult]] = defaultdict(list)
    for r in all_results:
        by_problem[r.problem_path].append(r)

    metrics: list[ProblemMetrics] = []
    for prob_path, results in by_problem.items():
        pm = compute_metrics(prob_path, results, max_turns=args.max_turns)
        metrics.append(pm)

    prior_posterior_by_problem: dict[str, dict] = {}
    if enable_difficulty_assessment:
        print("[Eval] Computing prior/posterior per-dimension details ...")
        prior_posterior_by_problem = _compute_prior_posterior_details(by_problem, judge_cfg)
    else:
        print("[Eval] Skip prior/posterior scoring (difficulty assessment disabled).")

    # ---- 输出 ----
    print_report(metrics)
    save_eval_report(metrics, output_file, prior_posterior_by_problem=prior_posterior_by_problem)
    save_eval_excel(metrics, excel_output_file, prior_posterior_by_problem=prior_posterior_by_problem)
    save_eval_markdown_report(
        metrics,
        markdown_output_file,
        prior_posterior_by_problem=prior_posterior_by_problem,
    )
    retest_file = _save_retest_llm_error_list(all_results)
    print(f"[Eval] Report saved to {output_file}")
    print(f"[Eval] Excel  saved to {excel_output_file}")
    print(f"[Eval] Markdown saved to {markdown_output_file}")
    print(f"[Eval] Retest list saved to {retest_file}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
