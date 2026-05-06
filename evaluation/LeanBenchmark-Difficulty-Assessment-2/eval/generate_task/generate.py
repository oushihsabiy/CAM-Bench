#!/usr/bin/env python3
"""
Generate task.json from config.json and Lean project files.

This script:
1. Reads configuration from config.json.
    - Legacy mode: single-model fields (`model`, `base_url`, `api_key`).
    - Multi-model mode: `models` array.
2. Scans a subdirectory under `lean_cwd` for all .lean files. The subdirectory
    can be configured with the `lean_subdir` key in config.json (default: "Leanproject").
3. Generates task.json with each (.lean file, model) pair as one experiment entry.
"""

import json
import os
import sys
import argparse


def _resolve_models(config: dict) -> list[dict]:
    """Resolve model configs from config.

    Supported shapes:
    1) Legacy single-model:
       {
         "model": "gpt-5.4",
         "base_url": "https://...",
         "api_key": "..."
       }
    2) Multi-model list:
       {
         "models": [
           "gpt-5.4",
           {"model": "deepseek-r1", "base_url": "https://...", "api_key": "..."}
         ]
       }

    Notes:
    - String entries inherit top-level base_url/api_key/temperature/stream/max_tokens_per_call.
    - Dict entries can override any inherited field.
    """
    base_url = config.get("base_url")
    api_key = config.get("api_key")
    temperature = config.get("temperature", 0.6)
    stream = config.get("stream", False)
    max_tokens_per_call = config.get("max_tokens_per_call")

    raw_models = config.get("models")
    resolved: list[dict] = []

    if isinstance(raw_models, list) and raw_models:
        for idx, item in enumerate(raw_models):
            if isinstance(item, str):
                name = item.strip()
                if not name:
                    raise ValueError(f"models[{idx}] is an empty string")
                resolved.append(
                    {
                        "model": name,
                        "base_url": base_url,
                        "api_key": api_key,
                        "temperature": temperature,
                        "stream": stream,
                        "max_tokens_per_call": max_tokens_per_call,
                    }
                )
                continue

            if isinstance(item, dict):
                name = str(item.get("model", "")).strip()
                if not name:
                    raise ValueError(f"models[{idx}].model is required")
                resolved.append(
                    {
                        "model": name,
                        "base_url": item.get("base_url", base_url),
                        "api_key": item.get("api_key", api_key),
                        "temperature": item.get("temperature", temperature),
                        "stream": item.get("stream", stream),
                        "max_tokens_per_call": item.get("max_tokens_per_call", max_tokens_per_call),
                    }
                )
                continue

            raise ValueError(f"models[{idx}] must be string or object")
    else:
        # Backward-compatible single model mode.
        single_model = str(config.get("model", "")).strip()
        if not single_model:
            raise ValueError("Either 'model' or non-empty 'models' must be specified in config.json")
        resolved.append(
            {
                "model": single_model,
                "base_url": base_url,
                "api_key": api_key,
                "temperature": temperature,
                "stream": stream,
                "max_tokens_per_call": max_tokens_per_call,
            }
        )

    # Basic validation.
    for i, m in enumerate(resolved):
        if not m.get("base_url"):
            raise ValueError(f"base_url is required for model '{m['model']}' (entry {i})")
        if m.get("api_key") is None:
            # Keep compatibility with existing scripts that default to EMPTY.
            m["api_key"] = "EMPTY"

    return resolved


def load_config(config_path: str) -> dict:
    """Load configuration from config.json."""
    if not os.path.exists(config_path):
        raise FileNotFoundError(f"Config file not found: {config_path}")
    
    with open(config_path, 'r', encoding='utf-8') as f:
        return json.load(f)


def _resolve_scan_dirs(
    lean_cwd: str,
    lean_project_dir: str,
    include_dirs: list[str] | None = None,
) -> list[str]:
    """Resolve scan directories from include_dirs.

    Priority for each non-absolute include dir:
    1) relative to lean_project_dir
    2) relative to lean_cwd
    """
    if not include_dirs:
        return [lean_project_dir]

    scan_dirs: list[str] = []
    for d in include_dirs:
        if not d:
            continue
        d = str(d).strip()
        if not d:
            continue

        candidates: list[str] = []
        if os.path.isabs(d):
            candidates.append(d)
        else:
            candidates.append(os.path.join(lean_project_dir, d))
            candidates.append(os.path.join(lean_cwd, d))

        found = None
        for c in candidates:
            if os.path.isdir(c):
                found = os.path.abspath(c)
                break

        if found is None:
            raise FileNotFoundError(
                f"Include directory not found: {d} "
                f"(tried: {', '.join(candidates)})"
            )
        scan_dirs.append(found)

    # de-duplicate while preserving order
    seen = set()
    uniq: list[str] = []
    for p in scan_dirs:
        if p in seen:
            continue
        seen.add(p)
        uniq.append(p)
    return uniq


def find_lean_files(
    lean_cwd: str,
    lean_subdir: str = "Leanproject",
    include_dirs: list[str] | None = None,
) -> list:
    """
    Find all .lean files in the specified subdirectory under lean_cwd.

    `lean_subdir` is a directory name (relative to `lean_cwd`). Returns a list
    of relative paths from `lean_cwd` to .lean files.
    """
    lean_project_dir = os.path.join(lean_cwd, lean_subdir)

    if not os.path.exists(lean_project_dir):
        raise FileNotFoundError(f"Leanproject directory not found: {lean_project_dir}")

    scan_dirs = _resolve_scan_dirs(lean_cwd, lean_project_dir, include_dirs)

    lean_files = []
    seen_files = set()
    for scan_dir in scan_dirs:
        for root, dirs, files in os.walk(scan_dir):
            for file in sorted(files):
                # Skip Basic.lean intentionally
                if file.endswith('.lean') and file != "Basic.lean" and not file.startswith("mcp_prefix_"):
                    # Get relative path from lean_cwd
                    full_path = os.path.join(root, file)
                    rel_path = os.path.relpath(full_path, lean_cwd)
                    if rel_path in seen_files:
                        continue
                    seen_files.add(rel_path)
                    lean_files.append(rel_path)

    return sorted(lean_files)


def generate_task_json(config: dict, lean_files: list) -> list:
    """
    Generate task.json content.
    
    Returns a list of task dictionaries.
    """
    tasks = []
    models = _resolve_models(config)

    for lean_file in lean_files:
        for model_cfg in models:
            task = {
                "problem": lean_file,
                "model": model_cfg.get("model"),
                "base_url": model_cfg.get("base_url"),
                "api_key": model_cfg.get("api_key"),
                "lean_cwd": config.get("lean_cwd"),
                "pass_n": config.get("pass_n", 3),
                "max_turns": config.get("max_turns", 5),
                "max_tokens": config.get("max_tokens", 1000000),
                "llm_error_budget_per_sorry": config.get("llm_error_budget_per_sorry", 10),
                "workers": config.get("workers", 1),
                "problem_timeout": config.get("problem_timeout", 300),
                "stream": model_cfg.get("stream", config.get("stream", False)),
                "temperature": model_cfg.get("temperature", config.get("temperature", 0.6)),
            }
            max_tokens_per_call = model_cfg.get("max_tokens_per_call")
            if max_tokens_per_call is not None:
                task["max_tokens_per_call"] = int(max_tokens_per_call)
            tasks.append(task)

    return tasks


def main():
    """Main function to generate task.json."""
    script_dir = os.path.dirname(os.path.abspath(__file__))
    eval_dir = os.path.dirname(script_dir)

    parser = argparse.ArgumentParser(
        description="Generate eval/task.json from config.json and Lean files.",
    )
    parser.add_argument(
        "--config",
        default=os.path.join(script_dir, "config.json"),
        help="Path to config.json",
    )
    parser.add_argument(
        "--output",
        default=os.path.join(eval_dir, "task.json"),
        help="Output task.json path",
    )
    parser.add_argument(
        "--include-dir",
        action="append",
        default=[],
        help=(
            "Restrict scanning to a folder (repeatable). "
            "Relative paths are resolved against lean_subdir first, then lean_cwd."
        ),
    )
    args = parser.parse_args()

    config_path = args.config
    output_path = args.output
    
    print(f"Loading config from: {config_path}")
    config = load_config(config_path)
    
    lean_cwd = config.get("lean_cwd")
    if not lean_cwd:
        raise ValueError("lean_cwd not specified in config.json")
    
    lean_subdir = config.get("lean_subdir", "Leanproject")
    include_dirs = args.include_dir or None
    print(f"Using lean_cwd: {lean_cwd}")
    print(f"Scanning for Lean files in: {os.path.join(lean_cwd, lean_subdir)}")
    if include_dirs:
        print("Restricting scan to --include-dir:")
        for d in include_dirs:
            print(f"  - {d}")

    lean_files = find_lean_files(lean_cwd, lean_subdir, include_dirs)
    print(f"Found {len(lean_files)} Lean files:")
    for f in lean_files:
        print(f"  - {f}")
    
    tasks = generate_task_json(config, lean_files)
    model_names = sorted({str(t.get("model", "")) for t in tasks})
    
    # Write task.json
    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(tasks, f, indent=2, ensure_ascii=False)
    
    print(f"\nGenerated task.json with {len(tasks)} tasks")
    print(f"Models in task.json: {', '.join(model_names)}")
    print(f"Output written to: {output_path}")
    
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
