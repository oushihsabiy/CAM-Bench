#!/usr/bin/env python3
"""Summarize pass@k accuracy from exported result directories.

The result tree is expected to look like:

    result/<model>/pass@32/<book>/<chapter>/<problem>/summary.json

For k values smaller than the exported pass limit, this script derives pass@k
from each problem's block_details: a problem passes at k iff every block passed
and each block's first_pass_turn, or attempts as a fallback, is <= k.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any


DEFAULT_KS = (1, 2, 4, 8, 16)
PASS_DIR_RE = re.compile(r"^pass@(\d+)$")


@dataclass(frozen=True)
class ProblemResult:
    model: str
    source_pass_k: int
    summary_path: Path
    passed: bool
    pass_turn: int | None
    total_tokens: int
    prompt_tokens: int
    completion_tokens: int
    status: str
    strict_pass: bool


def load_json(path: Path) -> Any | None:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return None


def parse_pass_dir(path: Path) -> int | None:
    match = PASS_DIR_RE.fullmatch(path.name)
    if match is None:
        return None
    return int(match.group(1))


def available_pass_dirs(model_dir: Path) -> dict[int, Path]:
    out: dict[int, Path] = {}
    for child in model_dir.iterdir() if model_dir.exists() else []:
        if not child.is_dir():
            continue
        k = parse_pass_dir(child)
        if k is not None:
            out[k] = child
    return out


def block_pass_turn(block: dict[str, Any]) -> int | None:
    """Return the turn at which a block passed, or None when unknown/failed."""
    if block.get("passed") is not True:
        return None
    first_pass_turn = block.get("first_pass_turn")
    if isinstance(first_pass_turn, int) and first_pass_turn > 0:
        return first_pass_turn
    attempts = block.get("attempts")
    if isinstance(attempts, int) and attempts > 0:
        return attempts
    return None


def load_strict_pass(summary_path: Path, data: dict[str, Any]) -> bool:
    """Return the exported strict-pass flag for a problem.

    Local block success is not enough for accuracy: some exported results have
    block_details with passed=true while the final strict validation did not
    pass. Prefer source_info.json because it is the export manifest's authority
    for whether the final file is actually correct.
    """
    source_info = load_json(summary_path.with_name("source_info.json"))
    if isinstance(source_info, dict) and isinstance(source_info.get("strict_pass"), bool):
        return bool(source_info["strict_pass"])
    if isinstance(data.get("correct"), bool):
        return bool(data["correct"])
    if isinstance(data.get("final_verify_passed"), bool):
        return bool(data["final_verify_passed"])
    return bool(data.get("all_passed") is True)


def summarize_problem(model: str, source_pass_k: int, summary_path: Path) -> ProblemResult | None:
    data = load_json(summary_path)
    if not isinstance(data, dict):
        return None

    blocks = data.get("block_details")
    strict_pass = load_strict_pass(summary_path, data)
    total_tokens = int(data.get("total_tokens") or 0)
    prompt_tokens = int(data.get("prompt_tokens") or 0)
    completion_tokens = int(data.get("completion_tokens") or 0)

    if not strict_pass:
        return ProblemResult(
            model=model,
            source_pass_k=source_pass_k,
            summary_path=summary_path,
            passed=False,
            pass_turn=None,
            total_tokens=total_tokens,
            prompt_tokens=prompt_tokens,
            completion_tokens=completion_tokens,
            status="strict_failed",
            strict_pass=False,
        )

    if not isinstance(blocks, list) or not blocks:
        return ProblemResult(
            model=model,
            source_pass_k=source_pass_k,
            summary_path=summary_path,
            passed=False,
            pass_turn=None,
            total_tokens=total_tokens,
            prompt_tokens=prompt_tokens,
            completion_tokens=completion_tokens,
            status="no_block_details",
            strict_pass=strict_pass,
        )

    turns: list[int] = []
    for block in blocks:
        if not isinstance(block, dict):
            return ProblemResult(
                model=model,
                source_pass_k=source_pass_k,
                summary_path=summary_path,
                passed=False,
                pass_turn=None,
                total_tokens=total_tokens,
                prompt_tokens=prompt_tokens,
                completion_tokens=completion_tokens,
                status="bad_block_details",
                strict_pass=strict_pass,
            )
        turn = block_pass_turn(block)
        if turn is None:
            return ProblemResult(
                model=model,
                source_pass_k=source_pass_k,
                summary_path=summary_path,
                passed=False,
                pass_turn=None,
                total_tokens=total_tokens,
                prompt_tokens=prompt_tokens,
                completion_tokens=completion_tokens,
                status=str(block.get("termination_reason") or data.get("termination_reason") or "failed"),
                strict_pass=strict_pass,
            )
        turns.append(turn)

    return ProblemResult(
        model=model,
        source_pass_k=source_pass_k,
        summary_path=summary_path,
        passed=True,
        pass_turn=max(turns),
        total_tokens=total_tokens,
        prompt_tokens=prompt_tokens,
        completion_tokens=completion_tokens,
        status="passed",
        strict_pass=strict_pass,
    )


def choose_source_dir(pass_dirs: dict[int, Path], requested_ks: list[int]) -> tuple[int, Path] | None:
    if not pass_dirs:
        return None
    need = max(requested_ks)
    eligible = {k: p for k, p in pass_dirs.items() if k >= need}
    if eligible:
        k = max(eligible)
        return k, eligible[k]
    k = max(pass_dirs)
    return k, pass_dirs[k]


def collect_model_results(model_dir: Path, requested_ks: list[int]) -> list[ProblemResult]:
    source = choose_source_dir(available_pass_dirs(model_dir), requested_ks)
    if source is None:
        return []
    source_k, source_dir = source
    results: list[ProblemResult] = []
    for summary_path in sorted(source_dir.glob("**/summary.json")):
        result = summarize_problem(model_dir.name, source_k, summary_path)
        if result is not None:
            results.append(result)
    return results


def summarize_by_k(results: list[ProblemResult], requested_ks: list[int]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    total = len(results)
    total_tokens = sum(r.total_tokens for r in results)
    prompt_tokens = sum(r.prompt_tokens for r in results)
    completion_tokens = sum(r.completion_tokens for r in results)
    for k in requested_ks:
        passed = sum(1 for r in results if r.passed and r.pass_turn is not None and r.pass_turn <= k)
        rows.append(
            {
                "k": k,
                "problems": total,
                "passed": passed,
                "failed": total - passed,
                "accuracy": (passed / total) if total else None,
                "total_tokens": total_tokens,
                "prompt_tokens": prompt_tokens,
                "completion_tokens": completion_tokens,
                "avg_tokens_per_problem": (total_tokens / total) if total else None,
            }
        )
    return rows


def format_percent(value: float | None) -> str:
    if value is None:
        return "n/a"
    return f"{value:.2%}"


def print_table(summary: dict[str, Any]) -> None:
    headers = [
        "model",
        "source",
        "k",
        "problems",
        "passed",
        "accuracy",
        "avg_tokens/problem",
        "total_tokens",
    ]
    print("\t".join(headers))
    for model, payload in summary["models"].items():
        source = f"pass@{payload['source_pass_k']}" if payload["source_pass_k"] is not None else "n/a"
        for row in payload["pass_at"]:
            print(
                "\t".join(
                    [
                        model,
                        source,
                        str(row["k"]),
                        str(row["problems"]),
                        str(row["passed"]),
                        format_percent(row["accuracy"]),
                        f"{row['avg_tokens_per_problem']:.2f}" if row["avg_tokens_per_problem"] is not None else "n/a",
                        str(row["total_tokens"]),
                    ]
                )
            )


def write_csv(path: Path, summary: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=[
                "model",
                "source_pass_k",
                "k",
                "problems",
                "passed",
                "failed",
                "accuracy",
                "total_tokens",
                "prompt_tokens",
                "completion_tokens",
                "avg_tokens_per_problem",
            ],
        )
        writer.writeheader()
        for model, payload in summary["models"].items():
            for row in payload["pass_at"]:
                writer.writerow({"model": model, "source_pass_k": payload["source_pass_k"], **row})


def parse_ks(raw: str) -> list[int]:
    ks = sorted({int(part.strip()) for part in raw.split(",") if part.strip()})
    if not ks or any(k <= 0 for k in ks):
        raise argparse.ArgumentTypeError("--ks must contain positive integers")
    return ks


def main() -> int:
    parser = argparse.ArgumentParser(description="Compute pass@k accuracy from result/<model>/pass@N exports.")
    parser.add_argument("--result-root", default="result", help="Path to result root directory.")
    parser.add_argument("--ks", type=parse_ks, default=list(DEFAULT_KS), help="Comma-separated k values, e.g. 1,2,4,8,16.")
    parser.add_argument("--models", default=None, help="Comma-separated model directory names. Default: all models.")
    parser.add_argument("--json-output", default=None, help="Optional path to write JSON summary.")
    parser.add_argument("--csv-output", default=None, help="Optional path to write CSV summary.")
    args = parser.parse_args()

    result_root = Path(args.result_root)
    if args.models:
        model_names = [m.strip() for m in args.models.split(",") if m.strip()]
        model_dirs = [result_root / name for name in model_names]
    else:
        model_dirs = sorted(path for path in result_root.iterdir() if path.is_dir())

    summary: dict[str, Any] = {
        "result_root": str(result_root),
        "ks": args.ks,
        "rule": "A problem passes at k iff every block passed and max(first_pass_turn or attempts) <= k.",
        "models": {},
    }

    for model_dir in model_dirs:
        results = collect_model_results(model_dir, args.ks)
        source_pass_k = results[0].source_pass_k if results else None
        status_counts: dict[str, int] = {}
        for result in results:
            status_counts[result.status] = status_counts.get(result.status, 0) + 1
        summary["models"][model_dir.name] = {
            "source_pass_k": source_pass_k,
            "source_problem_count": len(results),
            "status_counts": status_counts,
            "strict_pass_count": sum(1 for result in results if result.strict_pass),
            "pass_at": summarize_by_k(results, args.ks),
        }

    print_table(summary)

    if args.json_output:
        output = Path(args.json_output)
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    if args.csv_output:
        write_csv(Path(args.csv_output), summary)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
