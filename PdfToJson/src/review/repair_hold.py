#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""Repair hold JSON rows (except missing_dependency) one-by-one with LLM."""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Any, Dict, List

_THIS_DIR = Path(__file__).resolve().parent
if str(_THIS_DIR) not in sys.path:
    sys.path.append(str(_THIS_DIR))

from repair import (  # noqa: E402
    _build_prompt,
    _build_repaired_row,
    _chat_completion_text,
    _clear_proxy_env,
    _extract_first_json_object,
    _iter_json_files,
    _load_list,
    _reindex_rows,
    _write_progressive,
    find_config_json,
    load_config,
)
from openai import OpenAI  # noqa: E402
from token_usage import log_estimated_usage  # noqa: E402


def _load_prompt(prompt_path: str = "") -> str:
    if str(prompt_path or "").strip():
        p = Path(str(prompt_path)).expanduser().resolve()
    else:
        p = Path(__file__).resolve().parents[1] / "prompts" / "repair_hold.md"
    if not p.exists():
        raise FileNotFoundError(f"Repair-hold prompt not found: {p}")
    return p.read_text(encoding="utf-8").strip()


def _derive_out_path(in_file: Path, in_root: Path, out_root: Path) -> Path:
    rel = in_file.resolve().relative_to(in_root.resolve())
    stem = rel.stem if rel.stem.endswith("-re3") else (rel.stem + "-re3")
    rel2 = rel.with_name(stem + rel.suffix)
    return out_root / rel2


def _is_missing_dependency_hold(row: Dict[str, Any]) -> bool:
    c = str(row.get("hold_category") or "").strip().lower()
    if c == "missing_dependency":
        return True
    hr = str(row.get("hold_reason_type") or "").strip().lower()
    if hr == "missing_dependency":
        return True
    issues = row.get("value_true_issues")
    if isinstance(issues, dict):
        v = issues.get("missing_dependency")
        if isinstance(v, dict):
            vv = str(v.get("value") or "").strip().lower()
            if vv in {"true", "1", "yes", "y"}:
                return True
    issue_type = row.get("issue_type")
    if isinstance(issue_type, dict):
        v = issue_type.get("missing_dependency")
        if isinstance(v, dict):
            vv = str(v.get("value") or "").strip().lower()
            if vv in {"true", "1", "yes", "y"}:
                return True
    reason = str(row.get("reason") or "").strip().lower()
    if "missing dependency" in reason or "missing_dependency" in reason:
        return True
    return False


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description="Repair hold rows with LLM (excluding missing_dependency).")
    ap.add_argument("in_path", type=str, nargs="?", default="output_review/hold/book", help="Input file or root")
    ap.add_argument("out_root", type=str, nargs="?", default="output_review/hold/rewrite", help="Output root")
    ap.add_argument("--input-root", type=str, default="", help="Input root for relative path mapping")
    ap.add_argument("--model", type=str, default="", help="LLM model override")
    ap.add_argument("--max-tokens", type=int, default=1200, help="Max output tokens per row")
    ap.add_argument("--llm-retries", type=int, default=2, help="Max retries per row")
    ap.add_argument("--max-items", type=int, default=0, help="Max rows to send to LLM (0 = all)")
    ap.add_argument("--disable-llm", action="store_true", help="Do not call LLM")
    ap.add_argument("--force", action="store_true", help="Rebuild output file from scratch")
    ap.add_argument(
        "--prompt-path",
        type=str,
        default="",
        help="Repair-hold prompt path override (default: src/prompts/repair_hold.md)",
    )
    return ap.parse_args()


def main() -> None:
    args = parse_args()
    in_path = Path(args.in_path).expanduser().resolve()
    out_root = Path(args.out_root).expanduser().resolve()
    if not in_path.exists():
        raise FileNotFoundError(f"Input path not found: {in_path}")

    cfg: Dict[str, Any] = {}
    try:
        cfg = load_config()
    except Exception:
        cfg = {}
    api_key = str(cfg.get("api_key") or os.getenv("OPENAI_API_KEY") or "").strip()
    base_url = str(cfg.get("base_url") or "").strip()
    model = str(args.model or cfg.get("model") or "gpt-5-mini").strip()

    _clear_proxy_env()
    log_estimated_usage(
        endpoint="chat.completions",
        model=model,
        prompt_text="",
        output_text="",
        call_type="repair_hold",
        base_url=base_url,
        source="src/review/repair_hold.py",
        config_path=find_config_json(),
        extra={"script": "src/review/repair_hold.py", "reason": "run_start"},
    )

    use_llm = (not bool(args.disable_llm)) and bool(api_key)
    client = None
    if use_llm:
        if base_url:
            client = OpenAI(api_key=api_key, base_url=base_url, timeout=180)
        else:
            client = OpenAI(api_key=api_key, timeout=180)
    else:
        why = "disable-llm flag" if bool(args.disable_llm) else "missing api_key"
        print(f"[repair-hold] llm disabled: {why}", flush=True)

    template = _load_prompt(str(args.prompt_path or ""))
    files = list(_iter_json_files(in_path))
    if not files:
        print(f"[repair-hold] No JSON files found under {in_path}", flush=True)
        return

    if args.input_root:
        input_root = Path(args.input_root).expanduser().resolve()
    else:
        input_root = in_path if in_path.is_dir() else in_path.parent

    llm_budget = max(0, int(args.max_items))
    for in_file in files:
        rows_all = _load_list(in_file)
        rows: List[Dict[str, Any]] = [r for r in rows_all if not _is_missing_dependency_hold(r)]
        n_dep_skipped = len(rows_all) - len(rows)
        out_path = _derive_out_path(in_file, input_root, out_root)

        print(f"\n[repair-hold] File: {in_file.name}", flush=True)
        print(f"[repair-hold]   total rows={len(rows_all)}  repairable={len(rows)}  missing_dependency(skip)={n_dep_skipped}", flush=True)

        if len(rows) == 0:
            _write_progressive(out_path, [])
            print(f"[repair-hold][skip-empty] -> {out_path.name} (0 rows)", flush=True)
            continue

        done_rows: List[Dict[str, Any]] = []
        if out_path.exists() and not bool(args.force):
            try:
                prev = _load_list(out_path)
            except Exception:
                prev = []
            if len(prev) >= len(rows):
                print(f"[repair-hold][skip] already done ({len(rows)}/{len(rows)})", flush=True)
                continue
            done_rows = prev
            print(f"[repair-hold]   resuming from row {len(done_rows)+1}", flush=True)
        elif bool(args.force):
            _write_progressive(out_path, [])
            print(f"[repair-hold]   force mode: rebuilding from scratch", flush=True)

        start_idx = len(done_rows)
        llm_used = 0
        for i, row in enumerate(rows[start_idx:], start=start_idx + 1):
            source_idx = str(row.get("source_idx") or f"row{i}").strip()
            model_obj = None
            can_use_llm = use_llm and (llm_budget == 0 or llm_used < llm_budget)
            if can_use_llm:
                llm_used += 1
                prompt = _build_prompt(template, row)
                for _ in range(max(1, int(args.llm_retries))):
                    try:
                        raw = _chat_completion_text(
                            client,  # type: ignore[arg-type]
                            model=model,
                            prompt=prompt,
                            max_tokens=int(args.max_tokens),
                            source_idx=source_idx,
                        )
                        obj = _extract_first_json_object(raw)
                        if isinstance(obj, dict):
                            model_obj = obj
                            break
                    except Exception:
                        pass

            repaired = _build_repaired_row(row, model_obj)
            done_rows.append(repaired)
            done_rows = _reindex_rows(done_rows)
            _write_progressive(out_path, done_rows)
            tag = "llm" if (can_use_llm and model_obj) else ("llm-fail" if can_use_llm else "copy")
            print(f"[repair-hold][{i}/{len(rows)}][{tag}] {source_idx}", flush=True)

        print(f"[repair-hold] Done: {in_file.name} -> {out_path.name}  (llm_calls={llm_used})", flush=True)


if __name__ == "__main__":
    main()
