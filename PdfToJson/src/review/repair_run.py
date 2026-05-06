#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""Standalone revise-repair pipeline: repair -> review -> summary."""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, Iterable, List, Tuple


PROJECT_ROOT = Path(__file__).resolve().parents[2]


def _clear_proxy_env(env: Dict[str, str]) -> Dict[str, str]:
    out = dict(env)
    for k in ("http_proxy", "https_proxy", "HTTP_PROXY", "HTTPS_PROXY", "ALL_PROXY", "all_proxy"):
        out.pop(k, None)
    return out


def _iter_json_files(root: Path) -> Iterable[Path]:
    for p in sorted(root.rglob("*.json")):
        if p.is_file():
            yield p


def _load_settings() -> Dict[str, Any]:
    p = PROJECT_ROOT / "settings.json"
    if not p.exists():
        return {}
    try:
        obj = json.loads(p.read_text(encoding="utf-8"))
    except Exception:
        return {}
    return obj if isinstance(obj, dict) else {}


def _run(cmd: List[str]) -> None:
    env = _clear_proxy_env(os.environ)
    print("\n$ " + " ".join(cmd), flush=True)
    proc = subprocess.run(cmd, stdout=sys.stdout, stderr=sys.stderr, env=env)
    if proc.returncode != 0:
        raise SystemExit(proc.returncode)


def _load_list_len(path: Path) -> int:
    if not path.exists():
        return -1
    try:
        obj = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return -1
    if not isinstance(obj, list):
        return -1
    return len(obj)


def _summary_revise_path(rel: Path, summary_out_root: Path) -> Path:
    stem = rel.stem if rel.stem.endswith("-re2") else (rel.stem + "-re2")
    return summary_out_root / "revise" / rel.with_name(stem + rel.suffix)


def _paths_for(rel: Path, *, rewrite_root: Path, reviewlog_root: Path, summary_out_root: Path) -> Tuple[Path, Path, Path, Path]:
    rewrite_path = rewrite_root / rel
    reviewlog_path = reviewlog_root / rel
    hold_path = summary_out_root / "hold" / rel
    accept_path = summary_out_root / "accept" / rel
    revise_path = _summary_revise_path(rel, summary_out_root)
    return rewrite_path, reviewlog_path, hold_path, accept_path, revise_path


def _is_completed(rel: Path, *, in_file: Path, rewrite_root: Path, reviewlog_root: Path, summary_out_root: Path) -> bool:
    rewrite_path, reviewlog_path, hold_path, accept_path, revise_path = _paths_for(
        rel, rewrite_root=rewrite_root, reviewlog_root=reviewlog_root, summary_out_root=summary_out_root
    )
    if not rewrite_path.exists() or not reviewlog_path.exists() or not hold_path.exists() or not accept_path.exists() or not revise_path.exists():
        return False
    n_in = _load_list_len(in_file)
    n_rewrite = _load_list_len(rewrite_path)
    n_review = _load_list_len(reviewlog_path)
    n_hold = _load_list_len(hold_path)
    n_accept = _load_list_len(accept_path)
    n_revise = _load_list_len(revise_path)
    if min(n_in, n_rewrite, n_review, n_hold, n_accept, n_revise) < 0:
        return False
    if n_rewrite != n_in or n_review != n_rewrite:
        return False
    return (n_hold + n_accept + n_revise) == n_review


def parse_args() -> argparse.Namespace:
    s = _load_settings()
    ap = argparse.ArgumentParser(description="Run revise-only repair pipeline.")
    ap.add_argument(
        "--revise-only",
        action="store_true",
        default=bool(s.get("ENABLE_REPAIR_PIPELINE", False)),
        help="Enable revise-only pipeline run",
    )
    ap.add_argument("--in-root", type=str, default=str(s.get("REPAIR_IN_ROOT", "output_review/revise/book")))
    ap.add_argument("--in-file", type=str, default="", help="Single input file (always force)")
    ap.add_argument("--rewrite-root", type=str, default=str(s.get("REPAIR_REWRITE_ROOT", "output_review/revise/rewrite")))
    ap.add_argument("--reviewlog-root", type=str, default=str(s.get("REPAIR_REVIEWLOG_ROOT", "output_review/revise/reviewlog")))
    ap.add_argument(
        "--summary-out-root",
        type=str,
        default=str(s.get("REPAIR_SUMMARY_OUT_ROOT", "output_review/revise/split")),
    )
    ap.add_argument("--force", action="store_true", default=bool(s.get("REPAIR_FORCE", False)))
    ap.add_argument("--skip-existing", action="store_true", default=True)
    ap.add_argument("--no-skip-existing", action="store_true")
    ap.add_argument("--disable-llm", action="store_true", default=bool(s.get("REPAIR_DISABLE_LLM", False)))
    ap.add_argument("--model", type=str, default=str(s.get("REPAIR_MODEL", "")))
    ap.add_argument("--max-tokens", type=int, default=int(s.get("REPAIR_MAX_TOKENS", 1200)))
    ap.add_argument("--llm-retries", type=int, default=int(s.get("REPAIR_LLM_RETRIES", 2)))
    ap.add_argument("--max-items", type=int, default=int(s.get("REPAIR_MAX_ITEMS", 0)))
    return ap.parse_args()


def main() -> None:
    args = parse_args()
    if not bool(args.revise_only):
        print("revise-only pipeline not enabled. Run with --revise-only", flush=True)
        return

    in_root = Path(args.in_root).expanduser().resolve()
    rewrite_root = Path(args.rewrite_root).expanduser().resolve()
    reviewlog_root = Path(args.reviewlog_root).expanduser().resolve()
    summary_out_root = Path(args.summary_out_root).expanduser().resolve()

    repair_script = Path(__file__).resolve().parent / "repair.py"
    read_script = Path(__file__).resolve().parent / "read.py"
    summary_script = Path(__file__).resolve().parent / "summary.py"
    if not repair_script.exists() or not read_script.exists() or not summary_script.exists():
        raise FileNotFoundError("Missing one of repair.py/read.py/summary.py.")

    batch_skip = bool(args.skip_existing) and (not bool(args.no_skip_existing))

    if args.in_file:
        target = Path(args.in_file).expanduser().resolve()
        rel = target.relative_to(in_root)
        rewrite_path = rewrite_root / rel

        _run(
            [
                sys.executable,
                str(repair_script),
                str(target),
                str(rewrite_root),
                "--input-root",
                str(in_root),
                "--force",
                *([] if not args.model else ["--model", str(args.model)]),
                "--max-tokens",
                str(int(args.max_tokens)),
                "--llm-retries",
                str(int(args.llm_retries)),
                "--max-items",
                str(int(args.max_items)),
                *(["--disable-llm"] if bool(args.disable_llm) else []),
            ]
        )
        _run(
            [
                sys.executable,
                str(read_script),
                str(rewrite_path),
                str(reviewlog_root),
                "--input-root",
                str(rewrite_root),
                "--force",
            ]
        )
        _run(
            [
                sys.executable,
                str(summary_script),
                "--in-root",
                str(rewrite_root),
                "--in-file",
                str(rewrite_path),
                "--reviewlog-root",
                str(reviewlog_root),
                "--out-root",
                str(summary_out_root),
                "--summary-only",
            ]
        )
        return

    files = list(_iter_json_files(in_root))
    if not files:
        print(f"No JSON files found under {in_root}")
        return

    for i, f in enumerate(files, start=1):
        rel = f.relative_to(in_root)
        if batch_skip and (not bool(args.force)):
            if _is_completed(
                rel,
                in_file=f,
                rewrite_root=rewrite_root,
                reviewlog_root=reviewlog_root,
                summary_out_root=summary_out_root,
            ):
                print(f"[revise-only][skip][{i}/{len(files)}] {f}", flush=True)
                continue

        rewrite_path = rewrite_root / rel
        print(f"[revise-only][run][{i}/{len(files)}] {f}", flush=True)
        _run(
            [
                sys.executable,
                str(repair_script),
                str(f),
                str(rewrite_root),
                "--input-root",
                str(in_root),
                *([] if not args.model else ["--model", str(args.model)]),
                "--max-tokens",
                str(int(args.max_tokens)),
                "--llm-retries",
                str(int(args.llm_retries)),
                "--max-items",
                str(int(args.max_items)),
                *(["--force"] if bool(args.force) else []),
                *(["--disable-llm"] if bool(args.disable_llm) else []),
            ]
        )
        _run(
            [
                sys.executable,
                str(read_script),
                str(rewrite_path),
                str(reviewlog_root),
                "--input-root",
                str(rewrite_root),
                *(["--force"] if bool(args.force) else []),
            ]
        )
        _run(
            [
                sys.executable,
                str(summary_script),
                "--in-root",
                str(rewrite_root),
                "--in-file",
                str(rewrite_path),
                "--reviewlog-root",
                str(reviewlog_root),
                "--out-root",
                str(summary_out_root),
                "--summary-only",
            ]
        )


if __name__ == "__main__":
    main()
