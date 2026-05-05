#!/usr/bin/env python3
"""Review informal proof files against sibling informal.json problem statements.

Usage:
  python3 review/reviewer.py --config review/config.json
  python3 review/reviewer.py --config review/config.json --parallel 4
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any


SYSTEM_PROMPT = """You are a careful mathematical proof reviewer.

Your task is to decide whether the submitted proof correctly proves the problem statement.
Check every logical step, assumptions, definitions, edge cases, and whether the proof proves the
exact requested statement. Do not be lenient about gaps.

Return exactly two file blocks using this format, with no code fences and no extra text:
<<<review.json>>>
{
  "verdict": "correct" | "incorrect" | "unclear",
  "is_correct": true | false | null
}
<<<review.md>>>
# Review

## 主要问题

- 中文列出主要问题；如果没有问题则写“- 无”

## 判断理由

中文解释判断理由
<<<end>>>

The review.md block is plain Markdown. It may contain normal mathematical notation and raw
LaTeX backslashes. Only the review.json block must be valid JSON.
"""

USER_PROMPT_TEMPLATE = """Problem:
{problem}

Submitted proof:
{proof}

Review whether the submitted proof correctly proves the problem."""


VALID_VERDICTS = {"correct", "incorrect", "unclear"}
REVIEW_JSON_MARKER = "<<<review.json>>>"
REVIEW_MD_MARKER = "<<<review.md>>>"
END_MARKER = "<<<end>>>"


def load_config(path: str | Path) -> dict[str, Any]:
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError("config.json must contain a JSON object")
    return data


def resolve_api_key(value: object) -> str:
    key = str(value or "").strip()
    if key.startswith("ENV:"):
        env_name = key[4:].strip()
        if not env_name:
            raise ValueError("api_key uses ENV: but no environment variable name was provided")
        env_value = os.environ.get(env_name, "").strip()
        if not env_value:
            raise ValueError(f"environment variable {env_name!r} is not set")
        return env_value
    return key


def extract_problem(payload: Any, source: Path) -> str:
    if isinstance(payload, dict):
        problem = payload.get("problem")
        if isinstance(problem, str) and problem.strip():
            return problem.strip()
    if isinstance(payload, list):
        problems = [
            item.get("problem", "").strip()
            for item in payload
            if isinstance(item, dict) and isinstance(item.get("problem"), str) and item.get("problem", "").strip()
        ]
        if len(problems) == 1:
            return problems[0]
        if len(problems) > 1:
            return "\n\n".join(f"Problem {idx + 1}:\n{text}" for idx, text in enumerate(problems))
    raise ValueError(f"could not find a non-empty 'problem' field in {source}")


def _configured_models(config: dict[str, Any]) -> set[str]:
    raw_models = config.get("review_models")
    if not raw_models:
        return set()
    if not isinstance(raw_models, list):
        raise ValueError("review_models must be a list when provided")
    return {str(model).strip() for model in raw_models if str(model).strip()}


def find_review_targets(root: Path, config: dict[str, Any] | None = None) -> list[dict[str, Any]]:
    if not root.exists():
        raise FileNotFoundError(f"target_root does not exist: {root}")
    if not root.is_dir():
        raise NotADirectoryError(f"target_root is not a directory: {root}")
    config = config or {}
    proof_filename = str(config.get("proof_filename", "informal_proof.md"))
    review_filename = str(config.get("review_filename", "review.json"))
    review_md_filename = str(config.get("review_md_filename", "review.md"))
    selected_models = _configured_models(config)

    targets: list[dict[str, Any]] = []
    for informal_path in root.rglob("informal.json"):
        directory = informal_path.parent
        proof_root = directory / "proof"
        if proof_root.is_dir():
            for proof_path in sorted(proof_root.glob(f"*/{proof_filename}")):
                model = proof_path.parent.name
                if selected_models and model not in selected_models:
                    continue
                targets.append(
                    {
                        "problem_dir": directory,
                        "model": model,
                        "informal_path": informal_path,
                        "proof_path": proof_path,
                        "review_path": proof_path.parent / review_filename,
                        "review_md_path": proof_path.parent / review_md_filename,
                    }
                )
            continue

        # Backward compatibility for the old flat layout:
        #   problem_dir/[informal.json, proof.md, review.json]
        if (directory / "proof.md").is_file():
            model = "proof.md"
            if selected_models and model not in selected_models:
                continue
            targets.append(
                {
                    "problem_dir": directory,
                    "model": model,
                    "informal_path": informal_path,
                    "proof_path": directory / "proof.md",
                    "review_path": directory / review_filename,
                    "review_md_path": directory / review_md_filename,
                }
            )
    return sorted(targets, key=lambda item: (str(item["problem_dir"]), str(item["model"])))


def parse_usage(obj: dict[str, Any] | None) -> dict[str, int]:
    if not obj:
        return {"prompt_tokens": 0, "completion_tokens": 0, "total_tokens": 0}
    prompt_tokens = int(obj.get("prompt_tokens", 0) or 0)
    completion_tokens = int(obj.get("completion_tokens", 0) or 0)
    total_tokens = int(obj.get("total_tokens", 0) or 0) or prompt_tokens + completion_tokens
    return {
        "prompt_tokens": prompt_tokens,
        "completion_tokens": completion_tokens,
        "total_tokens": total_tokens,
    }


def parse_review_files(text: str) -> tuple[dict[str, Any], str]:
    content = text.strip()
    json_marker_index = content.find(REVIEW_JSON_MARKER)
    md_marker_index = content.find(REVIEW_MD_MARKER)
    if json_marker_index < 0 or md_marker_index < 0 or md_marker_index <= json_marker_index:
        raise ValueError(f"review response must contain {REVIEW_JSON_MARKER} before {REVIEW_MD_MARKER}")

    json_block = content[json_marker_index + len(REVIEW_JSON_MARKER) : md_marker_index].strip()
    json_start = json_block.find("{")
    json_end = json_block.rfind("}")
    if json_start < 0 or json_end <= json_start:
        raise ValueError("review.json block must contain a JSON object")
    review_json = json.loads(json_block[json_start : json_end + 1])
    if not isinstance(review_json, dict):
        raise ValueError("review.json block must contain a JSON object")

    verdict = str(review_json.get("verdict", "")).strip().lower()
    if verdict not in VALID_VERDICTS:
        raise ValueError('review.json must contain verdict: correct, incorrect, or unclear')

    is_correct = review_json.get("is_correct")
    if is_correct not in {True, False, None}:
        raise ValueError("review.json field is_correct must be true, false, or null")

    md_start = md_marker_index + len(REVIEW_MD_MARKER)
    end_marker_index = content.find(END_MARKER, md_start)
    if end_marker_index < 0:
        review_md = content[md_start:].strip()
    else:
        review_md = content[md_start:end_marker_index].strip()
    if not review_md:
        raise ValueError("review.md block must be non-empty")

    return {
        "verdict": verdict,
        "is_correct": is_correct,
    }, review_md.strip() + "\n"


def call_chat_completion(messages: list[dict[str, str]], config: dict[str, Any]) -> tuple[str, dict[str, int]]:
    base_url = str(config["base_url"]).rstrip("/")
    url = f"{base_url}/chat/completions"
    payload = {
        "model": str(config["model"]),
        "messages": messages,
        "temperature": float(config.get("temperature", 0)),
        "max_tokens": int(config.get("max_tokens", 2000)),
        "stream": bool(config.get("stream", False)),
    }
    data = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    headers = {
        "Content-Type": "application/json",
        "Authorization": f"Bearer {resolve_api_key(config.get('api_key', ''))}",
        "User-Agent": "proof-reviewer/1.0",
    }
    request = urllib.request.Request(url, data=data, headers=headers, method="POST")

    try:
        with urllib.request.urlopen(request, timeout=float(config.get("request_timeout", 300))) as response:
            raw = response.read().decode("utf-8")
    except urllib.error.HTTPError as err:
        body = err.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"LLM API error {err.code}: {body[:500]}") from err
    except urllib.error.URLError as err:
        raise RuntimeError(f"LLM API connection error: {err.reason}") from err

    parts: list[str] = []
    usage = {"prompt_tokens": 0, "completion_tokens": 0, "total_tokens": 0}
    for line in raw.splitlines():
        if not line.startswith("data: ") or line.strip() == "data: [DONE]":
            continue
        try:
            chunk = json.loads(line[6:])
        except json.JSONDecodeError:
            continue
        choices = chunk.get("choices") or [{}]
        delta = choices[0].get("delta", {}) if isinstance(choices[0], dict) else {}
        piece = delta.get("content", "")
        if piece:
            parts.append(str(piece))
        chunk_usage = parse_usage(chunk.get("usage"))
        if chunk_usage["total_tokens"]:
            usage = chunk_usage
    if parts:
        return "".join(parts).strip(), usage

    try:
        body = json.loads(raw)
    except json.JSONDecodeError as err:
        raise RuntimeError(f"LLM returned non-JSON response: {raw[:500]}") from err
    choices = body.get("choices") or []
    if not choices:
        raise RuntimeError(f"LLM returned no choices. Raw response: {raw[:500]}")
    content = str(choices[0].get("message", {}).get("content", "")).strip()
    if not content:
        raise RuntimeError(f"LLM returned empty content. Raw response: {raw[:500]}")
    return content, parse_usage(body.get("usage"))


def retry_delay(config: dict[str, Any], retry_index: int) -> float:
    initial = float(config.get("retry_initial_delay", 5))
    max_delay = float(config.get("retry_max_delay", 60))
    backoff = max(float(config.get("retry_backoff", 2)), 1.0)
    if initial <= 0 or max_delay <= 0:
        return 0.0
    return min(initial * (backoff ** max(retry_index - 1, 0)), max_delay)


def review_one(target: dict[str, Any], config: dict[str, Any]) -> dict[str, Any]:
    directory = Path(target["problem_dir"])
    model = str(target["model"])
    informal_path = Path(target["informal_path"])
    proof_path = Path(target["proof_path"])
    review_path = Path(target["review_path"])
    review_md_path = Path(target["review_md_path"])
    payload = json.loads(informal_path.read_text(encoding="utf-8"))
    problem = extract_problem(payload, informal_path)
    proof = proof_path.read_text(encoding="utf-8").strip()
    if not proof:
        raise ValueError(f"proof file is empty: {proof_path}")

    messages = [
        {"role": "system", "content": SYSTEM_PROMPT},
        {"role": "user", "content": USER_PROMPT_TEMPLATE.format(problem=problem, proof=proof)},
    ]
    retry_index = 0
    while True:
        retry_index += 1
        try:
            review, usage = call_chat_completion(messages, config)
            review_json, review_md = parse_review_files(review)
            review_path.write_text(json.dumps(review_json, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
            review_md_path.write_text(review_md, encoding="utf-8")
            return {
                "directory": str(directory),
                "model": model,
                "status": "success",
                "retry_count": retry_index,
                "proof_path": str(proof_path),
                "review_path": str(review_path),
                "review_md_path": str(review_md_path),
                "verdict": review_json["verdict"],
                "is_correct": review_json["is_correct"],
                "usage": usage,
            }
        except Exception as err:
            print(f"[Review] ERROR {directory} retry={retry_index}: {type(err).__name__}: {err}", flush=True)
            max_attempts = config.get("retry_max_attempts")
            if max_attempts is not None and retry_index >= int(max_attempts):
                return {
                    "directory": str(directory),
                    "model": model,
                    "status": "error",
                    "retry_count": retry_index,
                    "proof_path": str(proof_path),
                    "review_path": str(review_path),
                    "review_md_path": str(review_md_path),
                    "error": f"{type(err).__name__}: {err}",
                }
            delay = retry_delay(config, retry_index)
            if delay > 0:
                time.sleep(delay)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", default=Path(__file__).with_name("config.json"), help="Path to config.json")
    parser.add_argument(
        "--parallel",
        type=int,
        default=None,
        help="Number of proof targets to review concurrently. Defaults to config.parallel or 1.",
    )
    args = parser.parse_args()

    config_path = Path(args.config).expanduser().resolve()
    config = load_config(config_path)
    parallel = args.parallel if args.parallel is not None else int(config.get("parallel", 1))
    if parallel < 1:
        raise ValueError("--parallel must be at least 1")

    target_root = Path(str(config["target_root"])).expanduser()
    if not target_root.is_absolute():
        target_root = target_root.resolve()
    else:
        target_root = target_root.resolve()

    targets = find_review_targets(target_root, config)
    overwrite = bool(config.get("overwrite", False))
    print(f"[Review] Target root: {target_root}")
    print(f"[Review] Found {len(targets)} proof target(s)")
    print(f"[Review] Parallel workers: {parallel}")

    results: list[dict[str, Any] | None] = [None] * len(targets)
    pending: list[tuple[int, dict[str, Any]]] = []
    for index, target in enumerate(targets, start=1):
        directory = Path(target["problem_dir"])
        model = str(target["model"])
        proof_path = Path(target["proof_path"])
        review_path = Path(target["review_path"])
        review_md_path = Path(target["review_md_path"])
        if review_md_path.exists() and not overwrite:
            print(f"[Review] SKIP {index}/{len(targets)} {directory} [{model}] (review.md exists)")
            results[index - 1] = {
                "directory": str(directory),
                "model": model,
                "status": "skipped",
                "proof_path": str(proof_path),
                "review_path": str(review_path),
                "review_md_path": str(review_md_path),
            }
            continue
        pending.append((index, target))

    def run_target(index: int, target: dict[str, Any]) -> dict[str, Any]:
        directory = Path(target["problem_dir"])
        model = str(target["model"])
        proof_path = Path(target["proof_path"])
        review_path = Path(target["review_path"])
        review_md_path = Path(target["review_md_path"])
        print(f"[Review] RUN {index}/{len(targets)} {directory} [{model}]", flush=True)
        try:
            return review_one(target, config)
        except Exception as err:
            print(f"[Review] ERROR {directory} [{model}]: {type(err).__name__}: {err}", flush=True)
            return {
                "directory": str(directory),
                "model": model,
                "status": "error",
                "proof_path": str(proof_path),
                "review_path": str(review_path),
                "review_md_path": str(review_md_path),
                "error": f"{type(err).__name__}: {err}",
            }

    if parallel == 1 or len(pending) <= 1:
        for index, target in pending:
            results[index - 1] = run_target(index, target)
    else:
        with concurrent.futures.ThreadPoolExecutor(max_workers=parallel) as executor:
            future_to_index = {
                executor.submit(run_target, index, target): index
                for index, target in pending
            }
            for future in concurrent.futures.as_completed(future_to_index):
                index = future_to_index[future]
                results[index - 1] = future.result()

    final_results = [item for item in results if item is not None]
    success_count = sum(1 for item in final_results if item.get("status") == "success")
    skipped_count = sum(1 for item in final_results if item.get("status") == "skipped")
    error_count = sum(1 for item in final_results if item.get("status") == "error")
    summary_path = target_root / "review_summary.json"
    summary_path.write_text(json.dumps(final_results, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"[Review] Done: success={success_count}, skipped={skipped_count}, error={error_count}")
    print(f"[Review] Summary: {summary_path}")
    return 1 if error_count else 0


if __name__ == "__main__":
    raise SystemExit(main())
