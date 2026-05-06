#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""Run per-file review+summary pipeline and split rows by overall_status."""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from copy import deepcopy
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple

from reviewchat import _load_config_model, update_reviewchat_for_file


def _clear_proxy_env(env: Dict[str, str]) -> Dict[str, str]:
    out = dict(env)
    for k in ("http_proxy", "https_proxy", "HTTP_PROXY", "HTTPS_PROXY", "ALL_PROXY", "all_proxy"):
        out.pop(k, None)
    return out


def _iter_json_files(root: Path) -> Iterable[Path]:
    for p in sorted(root.rglob("*.json")):
        if p.is_file():
            yield p


def _load_list(path: Path) -> List[Dict[str, Any]]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, list):
        raise ValueError(f"Expected JSON list: {path}")
    return [x for x in obj if isinstance(x, dict)]


def _write_json(path: Path, rows: List[Dict[str, Any]], dry_run: bool = False) -> None:
    if dry_run:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(rows, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _reindex_rows(rows: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    out: List[Dict[str, Any]] = []
    for i, row in enumerate(rows, start=1):
        r = deepcopy(row)
        r["index"] = i
        out.append(r)
    return out


def _derive_rel(in_file: Path, in_root: Path) -> Path:
    return in_file.resolve().relative_to(in_root.resolve())


def _paths_for_file(
    *,
    in_file: Path,
    in_root: Path,
    reviewlog_root: Path,
    out_root: Path,
) -> Tuple[Path, Path, Path, Path]:
    rel = _derive_rel(in_file, in_root)
    reviewlog = reviewlog_root / rel
    hold_out = out_root / "hold" / rel
    accept_out = out_root / "accept" / rel
    if rel.stem.endswith("-re2") or rel.stem.endswith("-re3"):
        revise_stem = rel.stem
    else:
        revise_stem = rel.stem + "-re2"
    revise_rel = rel.with_name(revise_stem + rel.suffix)
    revise_out = out_root / "revise" / revise_rel
    return reviewlog, hold_out, accept_out, revise_out


def _len_or_neg(path: Path) -> int:
    if not path.exists():
        return -1
    try:
        return len(_load_list(path))
    except Exception:
        return -1


def _is_completed(
    *,
    in_file: Path,
    in_root: Path,
    reviewlog_root: Path,
    out_root: Path,
) -> bool:
    reviewlog, hold_out, accept_out, revise_out = _paths_for_file(
        in_file=in_file,
        in_root=in_root,
        reviewlog_root=reviewlog_root,
        out_root=out_root,
    )
    if not reviewlog.exists() or not hold_out.exists() or not accept_out.exists() or not revise_out.exists():
        return False

    nat_n = _len_or_neg(in_file)
    rev_n = _len_or_neg(reviewlog)
    hold_n = _len_or_neg(hold_out)
    accept_n = _len_or_neg(accept_out)
    revise_n = _len_or_neg(revise_out)
    if min(nat_n, rev_n, hold_n, accept_n, revise_n) < 0:
        return False
    if rev_n != nat_n:
        return False
    if hold_n + accept_n + revise_n != rev_n:
        return False
    return True


def _build_indices(rows: List[Dict[str, Any]]) -> Tuple[Dict[Tuple[str, str], Dict[str, Any]], Dict[str, List[Dict[str, Any]]]]:
    by_pair: Dict[Tuple[str, str], Dict[str, Any]] = {}
    by_idx: Dict[str, List[Dict[str, Any]]] = {}
    for row in rows:
        source = str(row.get("source") or "").strip()
        source_idx = str(row.get("source_idx") or "").strip()
        if source and source_idx and (source, source_idx) not in by_pair:
            by_pair[(source, source_idx)] = row
        if source_idx:
            by_idx.setdefault(source_idx, []).append(row)
    return by_pair, by_idx


def _find_original_row(
    report_row: Dict[str, Any],
    by_pair: Dict[Tuple[str, str], Dict[str, Any]],
    by_idx: Dict[str, List[Dict[str, Any]]],
) -> Optional[Dict[str, Any]]:
    source = str(report_row.get("source") or "").strip()
    source_idx = str(report_row.get("source_idx") or "").strip()
    if source and source_idx:
        row = by_pair.get((source, source_idx))
        if row is not None:
            return row
    if source_idx:
        cands = by_idx.get(source_idx, [])
        if len(cands) == 1:
            return cands[0]
    return None


def _to_bool(v: Any) -> bool:
    if isinstance(v, bool):
        return v
    if isinstance(v, (int, float)):
        return bool(v)
    return str(v or "").strip().lower() in {"true", "1", "yes", "y"}


def _accept_transform(row: Dict[str, Any]) -> Dict[str, Any]:
    out = deepcopy(row)
    for k in [
        "problem",
        "problem_clean",
        "problem_with_context_direct",
        "problem_with_context",
        "problem_standardized_math",
    ]:
        out.pop(k, None)
    pf = out.pop("problem_finally", None)
    if pf is not None:
        out["problem"] = pf
    return out


def _revise_transform(row: Dict[str, Any], report_row: Dict[str, Any]) -> Dict[str, Any]:
    out = deepcopy(row)
    out["overall_status"] = str(report_row.get("overall_status") or "").strip().lower()
    out["reason"] = str(report_row.get("reason") or "").strip()

    issue_type = report_row.get("issue_type")
    true_issues: Dict[str, Dict[str, Any]] = {}
    if isinstance(issue_type, dict):
        for issue_name, issue_obj in issue_type.items():
            if not isinstance(issue_obj, dict):
                continue
            if _to_bool(issue_obj.get("value")):
                true_issues[str(issue_name)] = {
                    "value": True,
                    "reason": str(issue_obj.get("reason") or "").strip(),
                    "suggestion_fix": str(issue_obj.get("suggestion_fix") or "").strip(),
                }
    out["value_true_issues"] = true_issues
    return out


def _is_parse_error(reason: str, confidence: Any) -> bool:
    try:
        c = float(confidence)
    except Exception:
        c = 0.0
    if c <= 0.0:
        return True
    rr = str(reason or "").strip().lower()
    if not rr:
        return False
    return (
        "review not completed" in rr
        or "review_failed" in rr
        or "model_output_not_json_object" in rr
        or "llm_disabled_or_api_key_missing" in rr
    )


def _derive_hold_category(report_row: Dict[str, Any]) -> str:
    issue_type = report_row.get("issue_type")
    miss_dep = False
    if isinstance(issue_type, dict):
        miss_dep = _to_bool(((issue_type.get("missing_dependency") or {}).get("value")))
    if miss_dep:
        return "missing_dependency"
    c = str(report_row.get("hold_reason_type") or "").strip()
    if c in {"missing_dependency", "unsuitable_lean", "parse_error"}:
        return c
    reason = str(report_row.get("reason") or "")
    if _is_parse_error(reason, report_row.get("confidence")):
        return "parse_error"
    return "unsuitable_lean"


def _hold_transform(row: Dict[str, Any], report_row: Dict[str, Any]) -> Dict[str, Any]:
    out = deepcopy(row)
    out["overall_status"] = str(report_row.get("overall_status") or "").strip().lower() or "hold"
    out["reason"] = str(report_row.get("reason") or "").strip()
    out["hold_category"] = _derive_hold_category(report_row)
    issue_type = report_row.get("issue_type")
    true_issues: Dict[str, Dict[str, Any]] = {}
    if isinstance(issue_type, dict):
        for issue_name, issue_obj in issue_type.items():
            if not isinstance(issue_obj, dict):
                continue
            if _to_bool(issue_obj.get("value")):
                true_issues[str(issue_name)] = {
                    "value": True,
                    "reason": str(issue_obj.get("reason") or "").strip(),
                    "suggestion_fix": str(issue_obj.get("suggestion_fix") or "").strip(),
                }
    out["value_true_issues"] = true_issues
    if "confidence" in report_row:
        out["review_confidence"] = report_row.get("confidence")
    return out


def run_summary_for_file(
    *,
    in_file: Path,
    in_root: Path,
    reviewlog_root: Path,
    out_root: Path,
    dry_run: bool = False,
) -> Tuple[int, int, int, int]:
    reviewlog, hold_out, accept_out, revise_out = _paths_for_file(
        in_file=in_file,
        in_root=in_root,
        reviewlog_root=reviewlog_root,
        out_root=out_root,
    )
    if not reviewlog.exists():
        raise FileNotFoundError(f"Reviewlog not found: {reviewlog}")

    original_rows = _load_list(in_file)
    report_rows = _load_list(reviewlog)
    by_pair, by_idx = _build_indices(original_rows)

    hold_rows: List[Dict[str, Any]] = []
    accept_rows: List[Dict[str, Any]] = []
    revise_rows: List[Dict[str, Any]] = []
    missing = 0

    for rep in report_rows:
        src = _find_original_row(rep, by_pair, by_idx)
        if src is None:
            missing += 1
            continue
        status = str(rep.get("overall_status") or "").strip().lower()
        if status == "accept":
            accept_rows.append(_accept_transform(src))
        elif status == "revise":
            revise_rows.append(_revise_transform(src, rep))
        else:
            hold_rows.append(_hold_transform(src, rep))

    hold_rows = _reindex_rows(hold_rows)
    accept_rows = _reindex_rows(accept_rows)
    revise_rows = _reindex_rows(revise_rows)

    _write_json(hold_out, hold_rows, dry_run=dry_run)
    _write_json(accept_out, accept_rows, dry_run=dry_run)
    _write_json(revise_out, revise_rows, dry_run=dry_run)
    return len(hold_rows), len(accept_rows), len(revise_rows), missing


def _run_review_script(
    *,
    read_script: Path,
    in_file: Path,
    in_root: Path,
    reviewlog_root: Path,
    force: bool,
    prompt_path: str,
) -> None:
    cmd = [
        sys.executable,
        str(read_script),
        str(in_file),
        str(reviewlog_root),
        "--input-root",
        str(in_root),
    ]
    if force:
        cmd.append("--force")
    if str(prompt_path or "").strip():
        cmd.extend(["--prompt-path", str(prompt_path)])
    env = _clear_proxy_env(os.environ)
    proc = subprocess.run(cmd, stdout=sys.stdout, stderr=sys.stderr, env=env)
    if proc.returncode != 0:
        raise SystemExit(proc.returncode)


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description="Run review then summary split (accept/hold/revise).")
    ap.add_argument("--in-root", type=str, default="output_json_naturalized", help="Naturalized JSON root")
    ap.add_argument("--in-file", type=str, default="", help="Single input JSON file (always force run)")
    ap.add_argument("--reviewlog-root", type=str, default="output_review/reviewlog", help="Review log root")
    ap.add_argument("--out-root", type=str, default="output_review", help="Output root for hold/accept/revise")
    ap.add_argument("--reviewchat-root", type=str, default="output_review/reviewchat", help="Reviewchat table root")
    ap.add_argument("--skip-existing", action="store_true", default=True, help="Skip files already fully completed")
    ap.add_argument("--no-skip-existing", action="store_true", help="Do not skip completed files in batch mode")
    ap.add_argument("--force", action="store_true", help="Force rerun in batch mode")
    ap.add_argument("--dry-run", action="store_true", help="Do not write outputs")
    ap.add_argument("--review-only", action="store_true", help="Explicitly run review then summary (default behavior)")
    ap.add_argument("--summary-only", action="store_true", help="Only run summary split using existing reviewlog")
    ap.add_argument(
        "--review-prompt-path",
        type=str,
        default="",
        help="Review prompt path override when running review stage",
    )
    return ap.parse_args()


def main() -> None:
    args = parse_args()
    if bool(args.review_only) and bool(args.summary_only):
        raise SystemExit("Cannot set both --review-only and --summary-only.")
    in_root = Path(args.in_root).expanduser().resolve()
    reviewlog_root = Path(args.reviewlog_root).expanduser().resolve()
    out_root = Path(args.out_root).expanduser().resolve()
    reviewchat_root = Path(args.reviewchat_root).expanduser().resolve()
    read_script = Path(__file__).resolve().parent / "read.py"
    model_name = _load_config_model(Path(__file__).resolve().parents[2])

    if not in_root.exists():
        raise FileNotFoundError(f"Input root not found: {in_root}")
    if not read_script.exists():
        raise FileNotFoundError(f"Missing review reader script: {read_script}")

    batch_skip = bool(args.skip_existing) and (not bool(args.no_skip_existing))
    force_batch = bool(args.force)

    if args.in_file:
        target = Path(args.in_file).expanduser().resolve()
        if not target.exists():
            raise FileNotFoundError(f"Input file not found: {target}")
        print(f"[run] single-file force mode: {target}")
        if not bool(args.summary_only):
            _run_review_script(
                read_script=read_script,
                in_file=target,
                in_root=in_root,
                reviewlog_root=reviewlog_root,
                force=True,
                prompt_path=str(args.review_prompt_path or ""),
            )
        h, a, r, m = run_summary_for_file(
            in_file=target,
            in_root=in_root,
            reviewlog_root=reviewlog_root,
            out_root=out_root,
            dry_run=bool(args.dry_run),
        )
        if not bool(args.dry_run):
            rc_out = update_reviewchat_for_file(
                in_file=target,
                in_root=in_root,
                reviewlog_root=reviewlog_root,
                reviewchat_root=reviewchat_root,
                model_name=model_name,
            )
            if rc_out is not None:
                print(f"[reviewchat] {target.name} -> {rc_out}")
        print(f"[summary] hold={h} accept={a} revise={r} missing_match={m}")
        return

    files = list(_iter_json_files(in_root))
    if not files:
        print(f"No JSON files found under {in_root}")
        return

    for i, f in enumerate(files, start=1):
        if batch_skip and (not force_batch):
            if _is_completed(
                in_file=f,
                in_root=in_root,
                reviewlog_root=reviewlog_root,
                out_root=out_root,
            ):
                if not bool(args.dry_run):
                    rc_out = update_reviewchat_for_file(
                        in_file=f,
                        in_root=in_root,
                        reviewlog_root=reviewlog_root,
                        reviewchat_root=reviewchat_root,
                        model_name=model_name,
                    )
                    if rc_out is not None:
                        print(f"[reviewchat][{i}/{len(files)}] {f.name} -> {rc_out}")
                print(f"[skip][{i}/{len(files)}] {f}")
                continue

        if bool(args.summary_only):
            print(f"[run][{i}/{len(files)}] summary-only: {f}")
        else:
            print(f"[run][{i}/{len(files)}] review -> summary: {f}")
            _run_review_script(
                read_script=read_script,
                in_file=f,
                in_root=in_root,
                reviewlog_root=reviewlog_root,
                force=bool(force_batch),
                prompt_path=str(args.review_prompt_path or ""),
            )
        h, a, r, m = run_summary_for_file(
            in_file=f,
            in_root=in_root,
            reviewlog_root=reviewlog_root,
            out_root=out_root,
            dry_run=bool(args.dry_run),
        )
        if not bool(args.dry_run):
            rc_out = update_reviewchat_for_file(
                in_file=f,
                in_root=in_root,
                reviewlog_root=reviewlog_root,
                reviewchat_root=reviewchat_root,
                model_name=model_name,
            )
            if rc_out is not None:
                print(f"[reviewchat][{i}/{len(files)}] {f.name} -> {rc_out}")
        print(f"[done][{i}/{len(files)}] hold={h} accept={a} revise={r} missing_match={m}")


if __name__ == "__main__":
    main()
