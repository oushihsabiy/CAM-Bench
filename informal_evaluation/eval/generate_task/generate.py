#!/usr/bin/env python3
"""Generate informal_evaluation/eval/task.json from chapter JSON files."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

if __name__ == "__main__" and __package__ is None:
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    __package__ = "eval.generate_task"

from ..problem_loader import load_chapter


PROJECT_ROOT = Path(__file__).resolve().parents[2]
RETRY_CONFIG_KEYS = [
    "llm_retry_initial_delay",
    "llm_retry_max_delay",
    "llm_retry_backoff",
    "llm_retry_max_attempts",
]


def load_config(path: str | Path) -> dict[str, Any]:
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError("config.json must contain a JSON object")
    return data


def _resolve_models(config: dict[str, Any]) -> list[dict[str, Any]]:
    base_url = config.get("base_url")
    api_key = config.get("api_key", "EMPTY")
    temperature = config.get("temperature", 0.6)
    stream = config.get("stream", False)
    max_tokens_per_call = config.get("max_tokens_per_call", 4096)
    raw_models = config.get("models")

    models: list[dict[str, Any]] = []
    if isinstance(raw_models, list) and raw_models:
        for idx, item in enumerate(raw_models):
            if isinstance(item, str):
                name = item.strip()
                if not name:
                    raise ValueError(f"models[{idx}] is empty")
                models.append(
                    {
                        "model": name,
                        "base_url": base_url,
                        "api_key": api_key,
                        "temperature": temperature,
                        "stream": stream,
                        "max_tokens_per_call": max_tokens_per_call,
                    }
                )
            elif isinstance(item, dict):
                name = str(item.get("model", "")).strip()
                if not name:
                    raise ValueError(f"models[{idx}].model is required")
                models.append(
                    {
                        "model": name,
                        "base_url": item.get("base_url", base_url),
                        "api_key": item.get("api_key", api_key),
                        "temperature": item.get("temperature", temperature),
                        "stream": item.get("stream", stream),
                        "max_tokens_per_call": item.get("max_tokens_per_call", max_tokens_per_call),
                        **{key: item[key] for key in RETRY_CONFIG_KEYS if key in item},
                    }
                )
            else:
                raise ValueError(f"models[{idx}] must be string or object")
    else:
        name = str(config.get("model", "")).strip()
        if not name:
            raise ValueError("Either 'model' or non-empty 'models' is required")
        models.append(
            {
                "model": name,
                "base_url": base_url,
                "api_key": api_key,
                "temperature": temperature,
                "stream": stream,
                "max_tokens_per_call": max_tokens_per_call,
            }
        )

    for model in models:
        if not model.get("base_url"):
            raise ValueError(f"base_url is required for model {model['model']}")
        if model.get("api_key") is None:
            model["api_key"] = "EMPTY"
    return models


def _resolve_input_files(config: dict[str, Any]) -> list[Path]:
    files: list[Path] = []
    searched: list[str] = []

    pattern = str(config.get("input_glob", "*.json"))
    for value in config.get("input_dirs", []) or []:
        root = Path(value).expanduser().resolve()
        if not root.exists():
            raise FileNotFoundError(f"input directory not found: {root}")
        if not root.is_dir():
            raise NotADirectoryError(f"input_dirs entry is not a directory: {root}")
        searched.append(f"{root}/**/{pattern}")
        files.extend(sorted(p.resolve() for p in root.rglob(pattern) if p.is_file()))

    for value in config.get("input_files", []) or []:
        files.append(Path(value).expanduser().resolve())

    input_dir = config.get("input_dir")
    if input_dir:
        root = Path(str(input_dir)).expanduser().resolve()
        searched.append(f"{root}/**/{pattern}")
        files.extend(sorted(p.resolve() for p in root.rglob(pattern) if p.is_file()))

    if not files:
        if searched:
            raise ValueError(
                "No input JSON files matched configured directories: "
                + ", ".join(searched)
            )
        raise ValueError("config must provide input_dirs, input_files, or input_dir")

    seen: set[Path] = set()
    out: list[Path] = []
    for path in files:
        if path in seen:
            continue
        if not path.exists():
            raise FileNotFoundError(f"input JSON not found: {path}")
        seen.add(path)
        out.append(path)
    return out


def generate_tasks(config: dict[str, Any]) -> list[dict[str, Any]]:
    models = _resolve_models(config)
    input_files = _resolve_input_files(config)
    tasks: list[dict[str, Any]] = []

    for chapter_path in input_files:
        for block in load_chapter(chapter_path):
            for model_cfg in models:
                task = {
                    "chapter_path": block.chapter_path,
                    "chapter_stem": block.chapter_stem,
                    "block_ordinal": block.ordinal,
                    "problem_id": block.problem_id,
                    "problem_slug": block.problem_slug,
                    "source_idx": block.source_idx,
                    "source": block.source,
                    "problem": block.problem_text,
                    "block": block.original,
                    "model": model_cfg["model"],
                    "base_url": model_cfg["base_url"],
                    "api_key": model_cfg.get("api_key", "EMPTY"),
                    "temperature": model_cfg.get("temperature", config.get("temperature", 0.6)),
                    "stream": bool(model_cfg.get("stream", config.get("stream", False))),
                    "max_tokens_per_call": int(
                        model_cfg.get("max_tokens_per_call", config.get("max_tokens_per_call", 4096))
                    ),
                    "pass_n": int(config.get("pass_n", 1)),
                    "workers": int(config.get("workers", 1)),
                    "problem_timeout": float(config.get("problem_timeout", 300)),
                    "output_root": str(
                        Path(config.get("output_root", PROJECT_ROOT / "results"))
                        .expanduser()
                        .resolve()
                    ),
                    "remove_completed_from_task": bool(
                        config.get("remove_completed_from_task", True)
                    ),
                }
                for key in RETRY_CONFIG_KEYS:
                    if key in model_cfg:
                        task[key] = model_cfg[key]
                    elif key in config:
                        task[key] = config[key]
                tasks.append(task)
    return tasks


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--config",
        default=str(Path(__file__).resolve().parent / "config.json"),
        help="Path to generator config JSON",
    )
    parser.add_argument(
        "--output",
        default=str(PROJECT_ROOT / "eval" / "task.json"),
        help="Output task.json path",
    )
    args = parser.parse_args()

    config = load_config(args.config)
    tasks = generate_tasks(config)
    output = Path(args.output).resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(tasks, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    print(f"Generated {len(tasks)} tasks")
    print(f"Output written to: {output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
