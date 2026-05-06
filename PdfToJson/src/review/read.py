#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""Read naturalized JSON files and review records one by one."""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional

from openai import OpenAI

_SRC_ROOT = Path(__file__).resolve().parents[1]
if str(_SRC_ROOT) not in sys.path:
    sys.path.append(str(_SRC_ROOT))
_THIS_DIR = Path(__file__).resolve().parent
if str(_THIS_DIR) not in sys.path:
    sys.path.append(str(_THIS_DIR))

from review import load_config, load_review_prompt, review_one
from token_usage import extract_base_url, log_estimated_usage


def _clear_proxy_env() -> None:
    for k in ("http_proxy", "https_proxy", "HTTP_PROXY", "HTTPS_PROXY", "ALL_PROXY", "all_proxy"):
        os.environ.pop(k, None)


def _iter_input_json_files(in_path: Path) -> Iterable[Path]:
    if in_path.is_file() and in_path.suffix.lower() == ".json":
        yield in_path
        return
    if in_path.is_dir():
        for p in sorted(in_path.rglob("*.json")):
            if p.is_file():
                yield p


def _safe_list_load(path: Path) -> List[Dict[str, Any]]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, list):
        raise ValueError(f"Input file must be a JSON list: {path}")
    return [x for x in obj if isinstance(x, dict)]


def _derive_out_path(in_file: Path, in_root: Path, out_root: Path) -> Path:
    rel = in_file.relative_to(in_root)
    return out_root / rel


def _write_progressive(out_path: Path, reports: List[Dict[str, Any]]) -> None:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(reports, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _status_of(report: Dict[str, Any]) -> str:
    return str(report.get("overall_status") or "").strip() or "unknown"


def _source_idx_of(record: Dict[str, Any], fallback_i: int) -> str:
    return str(record.get("source_idx") or f"row{fallback_i}").strip()


def _load_existing_reports(path: Path) -> List[Dict[str, Any]]:
    if not path.exists():
        return []
    try:
        obj = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return []
    if not isinstance(obj, list):
        return []
    out: List[Dict[str, Any]] = []
    for it in obj:
        if isinstance(it, dict):
            out.append(it)
    return out


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description="Review naturalized JSON files block-by-block.")
    ap.add_argument(
        "in_path",
        type=str,
        nargs="?",
        default="output_json_naturalized",
        help="Input JSON file or root directory (default: output_json_naturalized)",
    )
    ap.add_argument(
        "out_root",
        type=str,
        nargs="?",
        default="output_review/reviewlog",
        help="Output review root directory (default: output_review/reviewlog)",
    )
    ap.add_argument(
        "--input-root",
        type=str,
        default="",
        help="Optional input root for preserving relative output path",
    )
    ap.add_argument("--model", type=str, default="", help="LLM model override")
    ap.add_argument("--max-tokens", type=int, default=1200, help="Max output tokens per record")
    ap.add_argument("--max-items", type=int, default=0, help="Max records per file sent to LLM (0 = all)")
    ap.add_argument("--llm-retries", type=int, default=2, help="Max retries per record")
    ap.add_argument("--disable-llm", action="store_true", help="Do not call LLM")
    ap.add_argument("--force", action="store_true", help="Rebuild output even if review file already complete")
    ap.add_argument(
        "--prompt-path",
        type=str,
        default="",
        help="Review prompt path override (default: src/prompts/review.md)",
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

    source_base_url = base_url
    use_llm = (not bool(args.disable_llm)) and bool(api_key)
    client: Optional[OpenAI] = None
    if use_llm:
        if base_url:
            client = OpenAI(api_key=api_key, base_url=base_url, timeout=180)
        else:
            client = OpenAI(api_key=api_key, timeout=180)
        source_base_url = extract_base_url(client) or base_url

    log_estimated_usage(
        endpoint="chat.completions",
        model=model,
        prompt_text="",
        output_text="",
        call_type="review",
        base_url=source_base_url,
        source="src/review/read.py",
        config_path=None,
        extra={"script": "src/review/read.py", "reason": "run_start"},
    )

    template = load_review_prompt(str(args.prompt_path or ""))

    if args.input_root:
        in_root = Path(args.input_root).expanduser().resolve()
    else:
        in_root = in_path if in_path.is_dir() else in_path.parent
    files = list(_iter_input_json_files(in_path))
    if not files:
        print(f"No JSON files found under {in_path}")
        return

    llm_budget = max(0, int(args.max_items))
    for in_file in files:
        rows = _safe_list_load(in_file)
        out_path = _derive_out_path(in_file, in_root, out_root)
        print(f"\n[review] File: {in_file.name} -> {out_path}", flush=True)
        if len(rows) == 0:
            _write_progressive(out_path, [])
            print(f"[review][skip-empty] {in_file} -> {out_path} (0/0)", flush=True)
            continue
        reports = _load_existing_reports(out_path)
        if len(reports) >= len(rows) and not bool(args.force):
            print(f"[review][skip] {in_file} -> {out_path} ({len(rows)}/{len(rows)})", flush=True)
            continue
        if bool(args.force):
            reports = []
            _write_progressive(out_path, reports)

        llm_used = 0

        start_idx = len(reports)
        for i, row in enumerate(rows[start_idx:], start=start_idx + 1):
            can_use_llm = use_llm and (llm_budget == 0 or llm_used < llm_budget)
            if can_use_llm:
                llm_used += 1
            report = review_one(
                row,
                client=client if can_use_llm else None,
                model=model,
                max_tokens=int(args.max_tokens),
                prompt_template=template,
                llm_retries=int(args.llm_retries),
            )
            reports.append(report)
            _write_progressive(out_path, reports)
            source_idx = _source_idx_of(row, i)
            status = _status_of(report)
            print(
                f"[review][{i}/{len(rows)}] source_idx: {source_idx:<20} overall_status: {status}  reviewlog_written={len(reports)}",
                flush=True,
            )


if __name__ == "__main__":
    main()
