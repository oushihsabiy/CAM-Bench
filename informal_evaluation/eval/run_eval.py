#!/usr/bin/env python3
"""Run informal natural-language proof generation tasks.

Typical usage:
  python -m eval.generate_task.generate --config eval/generate_task/config.json
  python -m eval.run_eval --config eval/task.json --parallel 4
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import sys
import time
from concurrent.futures import Future, ThreadPoolExecutor, as_completed
from datetime import datetime
from pathlib import Path
from typing import Any

if __name__ == "__main__" and __package__ is None:
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    __package__ = "eval"

from .llm_client import ModelConfig, generate_with_usage
from .problem_loader import safe_slug, task_key
from .reporter import build_run_report, utc_now, write_json, write_report_csv
from .task_manager import completed_keys_from_output, prune_task_file, task_completion_key


PROJECT_ROOT = Path(__file__).resolve().parents[1]
WORKSPACE_ROOT = PROJECT_ROOT.parent


SYSTEM_PROMPT = """You are an expert graduate-level mathematics proof writer.

Write a rigorous natural-language proof for the given problem. Use clear mathematical reasoning,
define introduced notation, and do not rely on unstated computational verification.

Return only the proof. Do not mention that you are an AI model. Do not include code fences unless
the proof itself requires displayed mathematics.
"""

USER_PROMPT_TEMPLATE = """Problem metadata:
- source: {source}
- source_idx: {source_idx}
- problem_type: {problem_type}

Problem:
{problem}

Write a complete natural-language proof."""


DEFAULT_RETRY_INITIAL_DELAY = 5.0
DEFAULT_RETRY_MAX_DELAY = 60.0
DEFAULT_RETRY_BACKOFF = 2.0


def _as_bool(value: object, default: bool = False) -> bool:
    if value is None:
        return default
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return bool(value)
    if isinstance(value, str):
        return value.strip().lower() in {"1", "true", "yes", "on"}
    return default


def _optional_positive_int(value: object) -> int | None:
    if value is None or value == "":
        return None
    try:
        parsed = int(value)
    except (TypeError, ValueError):
        return None
    return parsed if parsed > 0 else None


def _retry_delay(task: dict[str, Any], retry_number: int) -> float:
    initial = float(task.get("llm_retry_initial_delay", DEFAULT_RETRY_INITIAL_DELAY))
    max_delay = float(task.get("llm_retry_max_delay", DEFAULT_RETRY_MAX_DELAY))
    backoff = float(task.get("llm_retry_backoff", DEFAULT_RETRY_BACKOFF))
    if initial <= 0 or max_delay <= 0:
        return 0.0
    return min(initial * (max(backoff, 1.0) ** max(retry_number - 1, 0)), max_delay)


def load_task_config(path: str | Path) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    if isinstance(data, list):
        return [t for t in data if isinstance(t, dict)], {}
    if isinstance(data, dict):
        raw = data.get("tasks", data.get("experiments"))
        if isinstance(raw, list):
            return [t for t in raw if isinstance(t, dict)], data
    raise ValueError(f"config must be task.json list or object with tasks/experiments: {path}")


def parse_model_filter(values: list[str] | None) -> set[str]:
    """Parse repeated/comma-separated model filters from CLI values."""
    selected: set[str] = set()
    for value in values or []:
        for part in str(value).split(","):
            name = part.strip()
            if name:
                selected.add(name)
    return selected


def filter_tasks_by_model(tasks: list[dict[str, Any]], selected_models: set[str]) -> list[dict[str, Any]]:
    """Keep only tasks whose model exactly matches one of selected_models."""
    if not selected_models:
        return tasks
    return [task for task in tasks if str(task.get("model", "")) in selected_models]


def _model_cfg(task: dict[str, Any]) -> ModelConfig:
    return ModelConfig(
        model=str(task["model"]),
        base_url=str(task["base_url"]),
        api_key=str(task.get("api_key", "EMPTY")),
        temperature=float(task.get("temperature", 0.6)),
        max_tokens=int(task.get("max_tokens_per_call", 4096)),
        stream=bool(task.get("stream", False)),
    )


def _problem_type(task: dict[str, Any]) -> str:
    block = task.get("block")
    if isinstance(block, dict):
        value = block.get("题目类型", block.get("problem_type", ""))
        if isinstance(value, list):
            return ", ".join(str(x) for x in value)
        return str(value or "")
    return ""


def build_messages(task: dict[str, Any]) -> list[dict[str, str]]:
    """Build model messages without leaking reference proof fields."""
    user = USER_PROMPT_TEMPLATE.format(
        source=str(task.get("source", "") or ""),
        source_idx=str(task.get("source_idx", "") or ""),
        problem_type=_problem_type(task),
        problem=str(task.get("problem", "") or ""),
    )
    return [
        {"role": "system", "content": SYSTEM_PROMPT},
        {"role": "user", "content": user},
    ]


def _short_hash_text(value: object) -> str:
    return hashlib.sha1(str(value).encode("utf-8")).hexdigest()[:10]


def _chapter_output_slug(task: dict[str, Any]) -> str:
    raw_path = str(task.get("chapter_path", "") or "")
    if raw_path:
        try:
            chapter_path = Path(raw_path).expanduser().resolve()
        except Exception:
            chapter_path = Path(raw_path)
        rel_path: Path | None = None
        for root in (WORKSPACE_ROOT / "benchmark", WORKSPACE_ROOT, Path.cwd()):
            try:
                rel_path = chapter_path.relative_to(root.resolve())
                break
            except (OSError, ValueError):
                continue
        if rel_path is None:
            rel_path = chapter_path
        if rel_path.name == "informal.json":
            rel_path = rel_path.parent
        elif rel_path.suffix:
            rel_path = rel_path.with_suffix("")
        parts = [safe_slug(part, fallback="part") for part in rel_path.parts if part not in {"", "."}]
        base = "__".join(parts) or safe_slug(task.get("chapter_stem"), fallback="chapter")
        return f"{base}__{_short_hash_text(chapter_path)}"
    return safe_slug(task.get("chapter_stem"), fallback="chapter")


def _task_output_dir(task: dict[str, Any], run_dir: Path) -> Path:
    chapter = _chapter_output_slug(task)
    problem = safe_slug(task.get("problem_slug") or task.get("problem_id"), fallback="problem")
    model = safe_slug(str(task.get("model", "model")).split("/")[-1], fallback="model")
    return run_dir / chapter / problem / model


def _initial_problem_payload(task: dict[str, Any]) -> dict[str, Any]:
    block = task.get("block")
    if isinstance(block, dict):
        return copy.deepcopy(block)
    return {
        "problem": task.get("problem", ""),
        "source": task.get("source", ""),
        "source_idx": task.get("source_idx", ""),
    }


def _write_task_summary(
    *,
    task: dict[str, Any],
    out_dir: Path,
    attempts: list[dict[str, Any]],
    started_at: str,
    finished_at: str,
) -> dict[str, Any]:
    success_count = sum(1 for a in attempts if a.get("status") == "success")
    summary = {
        "chapter_path": task.get("chapter_path", ""),
        "chapter_stem": task.get("chapter_stem", ""),
        "problem_id": task.get("problem_id", ""),
        "problem_slug": task.get("problem_slug", ""),
        "source_idx": task.get("source_idx", ""),
        "source": task.get("source", ""),
        "model": task.get("model", ""),
        "pass_n": int(task.get("pass_n", 1)),
        "successful_attempts": success_count,
        "total_attempts": len(attempts),
        "generated_at_n": success_count > 0,
        "correctness_status": "ungraded",
        "started_at": started_at,
        "finished_at": finished_at,
        "attempts": attempts,
        "output_dir": str(out_dir),
    }
    write_json(out_dir / "attempts.json", attempts)
    write_json(out_dir / "summary.json", summary)
    return summary


def run_one_task(task: dict[str, Any], run_dir: Path, *, dry_run: bool = False) -> dict[str, Any]:
    pass_n = int(task.get("pass_n", 1))
    timeout = float(task.get("problem_timeout", 300))
    max_attempts_per_pass = _optional_positive_int(task.get("llm_retry_max_attempts"))
    cfg = _model_cfg(task)
    out_dir = _task_output_dir(task, run_dir)

    started_at = utc_now()
    attempts: list[dict[str, Any]] = []
    if dry_run:
        return {
            "chapter_path": task.get("chapter_path", ""),
            "chapter_stem": task.get("chapter_stem", ""),
            "problem_id": task.get("problem_id", ""),
            "model": task.get("model", ""),
            "pass_n": pass_n,
            "generated_at_n": False,
            "correctness_status": "ungraded",
            "attempts": [],
            "output_dir": str(out_dir),
        }

    out_dir.mkdir(parents=True, exist_ok=True)
    problem_json = out_dir / "problem.json"
    if not problem_json.exists():
        write_json(problem_json, _initial_problem_payload(task))

    for pass_index in range(1, pass_n + 1):
        proof_file = out_dir / f"proof_pass_{pass_index:03d}.md"
        retry_index = 0
        while True:
            retry_index += 1
            t0 = time.monotonic()
            attempt: dict[str, Any] = {
                "pass_index": pass_index,
                "retry_index": retry_index,
                "model": cfg.model,
                "status": "error",
                "proof_file": str(proof_file),
                "prompt_tokens": 0,
                "completion_tokens": 0,
                "total_tokens": 0,
                "elapsed_sec": 0.0,
                "error": "",
            }
            try:
                text, usage = generate_with_usage(build_messages(task), cfg, timeout=timeout if timeout > 0 else None)
                proof = text.strip()
                if proof:
                    proof_file.write_text(proof + "\n", encoding="utf-8")
                    attempt["status"] = "success"
                else:
                    attempt["status"] = "empty"
                    attempt["error"] = "empty proof"
                attempt["prompt_tokens"] = usage.prompt_tokens
                attempt["completion_tokens"] = usage.completion_tokens
                attempt["total_tokens"] = usage.total_tokens
            except Exception as err:
                attempt["status"] = "error"
                attempt["error"] = f"{type(err).__name__}: {err}"
            finally:
                attempt["elapsed_sec"] = round(time.monotonic() - t0, 3)
                attempts.append(attempt)
                write_json(out_dir / "attempts.json", attempts)

            if attempt["status"] == "success":
                break
            if max_attempts_per_pass is not None and retry_index >= max_attempts_per_pass:
                break
            delay = _retry_delay(task, retry_index)
            if delay > 0:
                time.sleep(delay)

    finished_at = utc_now()
    return _write_task_summary(
        task=task,
        out_dir=out_dir,
        attempts=attempts,
        started_at=started_at,
        finished_at=finished_at,
    )


def _resolve_run_dir(args: argparse.Namespace, tasks: list[dict[str, Any]], meta: dict[str, Any]) -> tuple[Path, Path]:
    output_root = args.output_root or meta.get("output_root")
    if not output_root and tasks:
        output_root = tasks[0].get("output_root")
    root = Path(output_root or PROJECT_ROOT / "results").expanduser().resolve()
    run_id = args.run_id or datetime.now().strftime("%Y%m%d_%H%M%S")
    return root, root / run_id


def _maybe_prune(
    *,
    task_path: Path,
    output_root: Path,
    remove_completed: bool,
    extra_keys: set[str] | None = None,
) -> tuple[int, int, int]:
    if not remove_completed:
        return (0, 0, 0)
    keys = completed_keys_from_output(output_root)
    if extra_keys:
        keys.update(extra_keys)
    return prune_task_file(task_path, keys, backup=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", required=True, help="Path to informal task.json")
    parser.add_argument("--output-root", default=None, help="Override output_root")
    parser.add_argument("--run-id", default=None, help="Run id under output_root")
    parser.add_argument("--report", default=None, help="report.json path")
    parser.add_argument("--csv", default=None, help="report.csv path")
    parser.add_argument("--parallel", type=int, default=1, help="Number of concurrent tasks")
    parser.add_argument(
        "--model",
        action="append",
        default=[],
        help=(
            "Run only tasks for this exact model name. Repeatable; comma-separated values are also accepted."
        ),
    )
    parser.add_argument(
        "--models",
        action="append",
        default=[],
        help="Alias of --model; accepts comma-separated exact model names.",
    )
    parser.add_argument("--dry-run", action="store_true", help="Print planned work without calling models")
    parser.add_argument(
        "--no-remove-completed-from-task",
        action="store_true",
        help="Do not remove generated tasks from task.json",
    )
    args = parser.parse_args()

    task_path = Path(args.config).resolve()
    all_tasks, meta = load_task_config(task_path)
    selected_models = parse_model_filter([*args.model, *args.models])
    tasks = filter_tasks_by_model(all_tasks, selected_models)
    output_root, run_dir = _resolve_run_dir(args, tasks, meta)
    report_path = Path(args.report).resolve() if args.report else run_dir / "report.json"
    csv_path = Path(args.csv).resolve() if args.csv else run_dir / "report.csv"
    default_remove = _as_bool(meta.get("remove_completed_from_task"), True)
    if tasks:
        default_remove = _as_bool(tasks[0].get("remove_completed_from_task"), default_remove)
    remove_completed = default_remove and not args.no_remove_completed_from_task and not args.dry_run

    print(f"[InformalEval] Config: {task_path} ({len(all_tasks)} tasks)")
    if selected_models:
        missing = selected_models - {str(t.get("model", "")) for t in all_tasks}
        print(
            f"[InformalEval] Model filter: {', '.join(sorted(selected_models))} "
            f"({len(tasks)} matching tasks)"
        )
        if missing:
            print(f"[InformalEval] WARNING: no tasks matched model(s): {', '.join(sorted(missing))}")
    print(f"[InformalEval] Output root: {output_root}")
    print(f"[InformalEval] Run dir: {run_dir}")
    print(f"[InformalEval] Parallel: {args.parallel}")
    print(f"[InformalEval] Remove completed from task: {'on' if remove_completed else 'off'}")

    if not tasks:
        report = build_run_report([])
        if not args.dry_run:
            write_json(report_path, report)
            write_report_csv(csv_path, [])
        return 0

    results: list[dict[str, Any]] = []
    completed_keys: set[str] = set()
    t0 = time.monotonic()

    try:
        if args.parallel <= 1:
            for task in tasks:
                result = run_one_task(task, run_dir, dry_run=args.dry_run)
                results.append(result)
                if result.get("generated_at_n"):
                    completed_keys.add(task_key(result.get("chapter_path"), result.get("problem_id"), result.get("model")))
                    before, removed, after = _maybe_prune(
                        task_path=task_path,
                        output_root=output_root,
                        remove_completed=remove_completed,
                        extra_keys=completed_keys,
                    )
                    if removed:
                        print(f"[InformalEval] Pruned task.json: {before}->{after} (-{removed})")
        else:
            pool = ThreadPoolExecutor(max_workers=args.parallel)
            futures: dict[Future[dict[str, Any]], dict[str, Any]] = {}
            try:
                for task in tasks:
                    futures[pool.submit(run_one_task, task, run_dir, dry_run=args.dry_run)] = task
                for fut in as_completed(futures):
                    task = futures[fut]
                    try:
                        result = fut.result()
                    except Exception as err:
                        print(f"[InformalEval] ERROR in worker: {err}", file=sys.stderr)
                        continue
                    results.append(result)
                    if result.get("generated_at_n"):
                        completed_keys.add(task_completion_key(task))
                        before, removed, after = _maybe_prune(
                            task_path=task_path,
                            output_root=output_root,
                            remove_completed=remove_completed,
                            extra_keys=completed_keys,
                        )
                        if removed:
                            print(f"[InformalEval] Pruned task.json: {before}->{after} (-{removed})")
            except KeyboardInterrupt:
                pool.shutdown(wait=False, cancel_futures=True)
                raise
            else:
                pool.shutdown(wait=True)
    except KeyboardInterrupt:
        print("\n[InformalEval] Interrupted by Ctrl+C; pruning completed generated tasks ...")
        before, removed, after = _maybe_prune(
            task_path=task_path,
            output_root=output_root,
            remove_completed=remove_completed,
            extra_keys=completed_keys,
        )
        if remove_completed:
            print(f"[InformalEval] Pruned task.json: {before}->{after} (-{removed})")
        if results and not args.dry_run:
            report = build_run_report(results)
            write_json(report_path, report)
            write_report_csv(csv_path, results)
            print(f"[InformalEval] Partial report saved to {report_path}")
        return 130

    elapsed = time.monotonic() - t0
    report = build_run_report(results)
    report["duration_seconds"] = round(elapsed, 3)

    if not args.dry_run:
        write_json(report_path, report)
        write_report_csv(csv_path, results)
        before, removed, after = _maybe_prune(
            task_path=task_path,
            output_root=output_root,
            remove_completed=remove_completed,
            extra_keys=completed_keys,
        )
        if remove_completed and removed:
            print(f"[InformalEval] Final prune task.json: {before}->{after} (-{removed})")

    print(
        f"[InformalEval] Completed {len(results)} tasks in {elapsed:.1f}s; "
        f"generated_at_n={report['completed_tasks']}/{report['total_tasks']}"
    )
    if not args.dry_run:
        print(f"[InformalEval] Report saved to {report_path}")
        print(f"[InformalEval] CSV saved to {csv_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
