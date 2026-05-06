#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""Standalone hold-repair pipeline: repair_hold -> review_hold -> summary."""

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


def _rewrite_re3_path(rel: Path, rewrite_root: Path) -> Path:
    stem = rel.stem if rel.stem.endswith("-re3") else (rel.stem + "-re3")
    return rewrite_root / rel.with_name(stem + rel.suffix)


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


def _count_repairable_rows(in_file: Path) -> int:
    if not in_file.exists():
        return -1
    try:
        obj = json.loads(in_file.read_text(encoding="utf-8"))
    except Exception:
        return -1
    if not isinstance(obj, list):
        return -1
    n = 0
    for it in obj:
        if isinstance(it, dict) and (not _is_missing_dependency_hold(it)):
            n += 1
    return n


def _paths_for(rel: Path, *, rewrite_root: Path, reviewlog_root: Path, summary_out_root: Path) -> Tuple[Path, Path, Path, Path, Path]:
    rewrite_path = _rewrite_re3_path(rel, rewrite_root)
    rewrite_rel = rewrite_path.relative_to(rewrite_root)
    reviewlog_path = reviewlog_root / rewrite_rel
    hold_path = summary_out_root / "hold" / rewrite_rel
    accept_path = summary_out_root / "accept" / rewrite_rel
    revise_path = summary_out_root / "revise" / rewrite_rel
    return rewrite_path, reviewlog_path, hold_path, accept_path, revise_path


def _is_repair_completed(rel: Path, *, in_file: Path, rewrite_root: Path) -> bool:
    rewrite_path = _rewrite_re3_path(rel, rewrite_root)
    if not rewrite_path.exists():
        return False
    n_expected = _count_repairable_rows(in_file)
    n_rewrite = _load_list_len(rewrite_path)
    if n_expected < 0 or n_rewrite < 0:
        return False
    return n_rewrite == n_expected


def _is_review_completed(rel: Path, *, rewrite_root: Path, reviewlog_root: Path) -> bool:
    rewrite_path = _rewrite_re3_path(rel, rewrite_root)
    rewrite_rel = rewrite_path.relative_to(rewrite_root)
    reviewlog_path = reviewlog_root / rewrite_rel
    if not rewrite_path.exists() or not reviewlog_path.exists():
        return False
    n_rewrite = _load_list_len(rewrite_path)
    n_review = _load_list_len(reviewlog_path)
    if n_rewrite < 0 or n_review < 0:
        return False
    return n_review == n_rewrite


def _is_summary_completed(rel: Path, *, rewrite_root: Path, reviewlog_root: Path, summary_out_root: Path) -> bool:
    rewrite_path, reviewlog_path, hold_path, accept_path, revise_path = _paths_for(
        rel, rewrite_root=rewrite_root, reviewlog_root=reviewlog_root, summary_out_root=summary_out_root
    )
    if not rewrite_path.exists() or not reviewlog_path.exists() or not hold_path.exists() or not accept_path.exists() or not revise_path.exists():
        return False
    n_rewrite = _load_list_len(rewrite_path)
    n_review = _load_list_len(reviewlog_path)
    n_hold = _load_list_len(hold_path)
    n_accept = _load_list_len(accept_path)
    n_revise = _load_list_len(revise_path)
    if min(n_rewrite, n_review, n_hold, n_accept, n_revise) < 0:
        return False
    if n_review != n_rewrite:
        return False
    return (n_hold + n_accept + n_revise) == n_review


def _is_completed(rel: Path, *, rewrite_root: Path, reviewlog_root: Path, summary_out_root: Path) -> bool:
    return _is_summary_completed(
        rel,
        rewrite_root=rewrite_root,
        reviewlog_root=reviewlog_root,
        summary_out_root=summary_out_root,
    )


def parse_args() -> argparse.Namespace:
    s = _load_settings()
    ap = argparse.ArgumentParser(description="Run hold-only repair pipeline.")
    ap.add_argument("--hold-only", action="store_true", default=bool(s.get("ENABLE_HOLD_PIPELINE", False)), help="Enable hold-only pipeline run")
    ap.add_argument("--in-root", type=str, default=str(s.get("HOLD_IN_ROOT", "output_review/hold/book")))
    ap.add_argument("--in-file", type=str, default="", help="Single input file (always force)")
    ap.add_argument("--rewrite-root", type=str, default=str(s.get("HOLD_REWRITE_ROOT", "output_review/hold/rewrite")))
    ap.add_argument("--reviewlog-root", type=str, default=str(s.get("HOLD_REVIEWLOG_ROOT", "output_review/hold/reviewlog")))
    ap.add_argument("--summary-out-root", type=str, default=str(s.get("HOLD_SUMMARY_OUT_ROOT", "output_review/hold/split")))
    ap.add_argument("--reviewchat-root", type=str, default=str(s.get("REVIEWCHAT_ROOT", "output_review/reviewchat")))
    ap.add_argument("--force", action="store_true", default=bool(s.get("HOLD_FORCE", False)))
    ap.add_argument("--skip-existing", action="store_true", default=True)
    ap.add_argument("--no-skip-existing", action="store_true")
    ap.add_argument("--disable-llm", action="store_true", default=bool(s.get("HOLD_DISABLE_LLM", False)))
    ap.add_argument("--model", type=str, default=str(s.get("HOLD_MODEL", "")))
    ap.add_argument("--max-tokens", type=int, default=int(s.get("HOLD_MAX_TOKENS", 1200)))
    ap.add_argument("--llm-retries", type=int, default=int(s.get("HOLD_LLM_RETRIES", 2)))
    ap.add_argument("--max-items", type=int, default=int(s.get("HOLD_MAX_ITEMS", 0)))
    return ap.parse_args()


def main() -> None:
    args = parse_args()
    if not bool(args.hold_only):
        print("hold-only pipeline not enabled. Run with --hold-only", flush=True)
        return

    in_root = Path(args.in_root).expanduser().resolve()
    rewrite_root = Path(args.rewrite_root).expanduser().resolve()
    reviewlog_root = Path(args.reviewlog_root).expanduser().resolve()
    summary_out_root = Path(args.summary_out_root).expanduser().resolve()
    reviewchat_root = Path(args.reviewchat_root).expanduser().resolve()

    repair_script = Path(__file__).resolve().parent / "repair_hold.py"
    read_script = Path(__file__).resolve().parent / "read.py"
    summary_script = Path(__file__).resolve().parent / "summary.py"
    review_prompt = PROJECT_ROOT / "src" / "prompts" / "review_hold.md"
    repair_prompt = PROJECT_ROOT / "src" / "prompts" / "repair_hold.md"

    if not repair_script.exists() or not read_script.exists() or not summary_script.exists():
        raise FileNotFoundError("Missing one of repair_hold.py/read.py/summary.py.")

    batch_skip = bool(args.skip_existing) and (not bool(args.no_skip_existing))

    print(f"\n{'='*60}", flush=True)
    print(f"[hold-pipeline] Starting hold-repair pipeline", flush=True)
    print(f"[hold-pipeline]   in_root:          {in_root}", flush=True)
    print(f"[hold-pipeline]   rewrite_root:     {rewrite_root}", flush=True)
    print(f"[hold-pipeline]   reviewlog_root:   {reviewlog_root}", flush=True)
    print(f"[hold-pipeline]   summary_out_root: {summary_out_root}", flush=True)
    print(f"[hold-pipeline]   force={args.force}  skip_existing={batch_skip}  disable_llm={args.disable_llm}", flush=True)
    print(f"{'='*60}", flush=True)

    if args.in_file:
        target = Path(args.in_file).expanduser().resolve()
        rel = target.relative_to(in_root)
        rewrite_path = _rewrite_re3_path(rel, rewrite_root)

        _run(
            [
                sys.executable,
                str(repair_script),
                str(target),
                str(rewrite_root),
                "--input-root",
                str(in_root),
                "--prompt-path",
                str(repair_prompt),
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
                "--prompt-path",
                str(review_prompt),
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
                "--reviewchat-root",
                str(reviewchat_root),
                "--summary-only",
            ]
        )
        return

    files = list(_iter_json_files(in_root))
    if not files:
        print(f"[hold-pipeline] No JSON files found under {in_root}", flush=True)
        return

    total = len(files)
    n_skipped = 0
    n_processed = 0
    n_failed = 0
    print(f"[hold-pipeline] Found {total} JSON file(s) to process", flush=True)

    import time as _time
    t_start = _time.time()

    for i, f in enumerate(files, start=1):
        rel = f.relative_to(in_root)
        if batch_skip and (not bool(args.force)):
            if _is_completed(
                rel,
                rewrite_root=rewrite_root,
                reviewlog_root=reviewlog_root,
                summary_out_root=summary_out_root,
            ):
                n_skipped += 1
                print(f"[hold-pipeline][skip][{i}/{total}] {rel}", flush=True)
                continue

        rewrite_path = _rewrite_re3_path(rel, rewrite_root)
        print(f"\n[hold-pipeline][run][{i}/{total}] {rel}", flush=True)
        try:
            if (not bool(args.force)) and _is_repair_completed(rel, in_file=f, rewrite_root=rewrite_root):
                print(f"[hold-pipeline]  step 1/3: repair_hold ... skip (rewrite complete)", flush=True)
            else:
                print(f"[hold-pipeline]  step 1/3: repair_hold ... run", flush=True)
                _run(
                    [
                        sys.executable,
                        str(repair_script),
                        str(f),
                        str(rewrite_root),
                        "--input-root",
                        str(in_root),
                        "--prompt-path",
                        str(repair_prompt),
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

            if (not bool(args.force)) and _is_review_completed(rel, rewrite_root=rewrite_root, reviewlog_root=reviewlog_root):
                print(f"[hold-pipeline]  step 2/3: review (read.py) ... skip (reviewlog complete)", flush=True)
            else:
                print(f"[hold-pipeline]  step 2/3: review (read.py) ... run", flush=True)
                _run(
                    [
                        sys.executable,
                        str(read_script),
                        str(rewrite_path),
                        str(reviewlog_root),
                        "--input-root",
                        str(rewrite_root),
                        "--prompt-path",
                        str(review_prompt),
                        *(["--force"] if bool(args.force) else []),
                    ]
                )

            if (not bool(args.force)) and _is_summary_completed(
                rel, rewrite_root=rewrite_root, reviewlog_root=reviewlog_root, summary_out_root=summary_out_root
            ):
                print(f"[hold-pipeline]  step 3/3: summary ... skip (summary complete)", flush=True)
            else:
                print(f"[hold-pipeline]  step 3/3: summary ... run", flush=True)
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
                        "--reviewchat-root",
                        str(reviewchat_root),
                        "--summary-only",
                    ]
                )
            n_processed += 1
            print(f"[hold-pipeline][done][{i}/{total}] {rel}", flush=True)
        except SystemExit:
            n_failed += 1
            print(f"[hold-pipeline][FAIL][{i}/{total}] {rel}", flush=True)

    elapsed = _time.time() - t_start
    print(f"\n{'='*60}", flush=True)
    print(f"[hold-pipeline] Finished.", flush=True)
    print(f"[hold-pipeline]   total={total}  processed={n_processed}  skipped={n_skipped}  failed={n_failed}", flush=True)
    print(f"[hold-pipeline]   elapsed: {elapsed:.1f}s", flush=True)
    print(f"{'='*60}\n", flush=True)


if __name__ == "__main__":
    main()
