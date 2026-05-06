#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""Build per-prefix review summary tables (round1/round2/round3)."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional


ROUND_ORDER = ["round1", "round2", "round3"]


def _iter_json_files(root: Path) -> Iterable[Path]:
    for p in sorted(root.rglob("*.json")):
        if p.is_file():
            yield p


def _load_list(path: Path) -> List[Dict[str, Any]]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, list):
        raise ValueError(f"Expected JSON list: {path}")
    return [x for x in obj if isinstance(x, dict)]


def _to_bool(v: Any) -> bool:
    if isinstance(v, bool):
        return v
    if isinstance(v, (int, float)):
        return bool(v)
    return str(v or "").strip().lower() in {"true", "1", "yes", "y"}


def _load_config_model(project_root: Optional[Path] = None) -> str:
    candidates: List[Path] = []
    if project_root is not None:
        candidates.append(project_root / "config.json")
    here = Path(__file__).resolve().parent
    for d in [here] + list(here.parents):
        candidates.append(d / "config.json")
    for p in candidates:
        if not p.exists():
            continue
        try:
            obj = json.loads(p.read_text(encoding="utf-8"))
        except Exception:
            continue
        if isinstance(obj, dict):
            m = str(obj.get("model") or "").strip()
            if m:
                return m
    return ""


def _normalize_prefix(stem: str) -> str:
    s = str(stem or "").strip()
    if s.endswith("-re2"):
        return s[:-4]
    if s.endswith("-re3"):
        return s[:-4]
    return s


def _detect_round(in_file: Path, reviewlog_file: Path) -> str:
    stem = in_file.stem
    if stem.endswith("-re3") or reviewlog_file.stem.endswith("-re3"):
        return "round3"
    if stem.endswith("-re2") or reviewlog_file.stem.endswith("-re2"):
        return "round2"
    reviewlog_posix = reviewlog_file.as_posix().lower()
    if "/hold/" in reviewlog_posix:
        return "round3"
    if "/revise/" in reviewlog_posix:
        return "round2"
    return "round1"


def _status_counts(report_rows: List[Dict[str, Any]]) -> Dict[str, int]:
    out = {"accept": 0, "revise": 0, "hold": 0}
    for row in report_rows:
        s = str(row.get("overall_status") or "").strip().lower()
        if s not in out:
            s = "hold"
        out[s] += 1
    return out


def _is_parse_error_row(row: Dict[str, Any]) -> bool:
    conf = row.get("confidence", 0.0)
    try:
        c = float(conf)
    except Exception:
        c = 0.0
    if c <= 0.0:
        return True
    reason = str(row.get("reason") or "").strip().lower()
    if not reason:
        return False
    return (
        "review not completed" in reason
        or "review_failed" in reason
        or "model_output_not_json_object" in reason
        or "llm_disabled_or_api_key_missing" in reason
    )


def _hold_reason_type(row: Dict[str, Any]) -> str:
    explicit = str(row.get("hold_reason_type") or "").strip()
    if explicit in {"missing_dependency", "unsuitable_lean", "parse_error"}:
        return explicit
    issue_type = row.get("issue_type")
    if isinstance(issue_type, dict):
        if _to_bool(((issue_type.get("missing_dependency") or {}).get("value"))):
            return "missing_dependency"
    if _is_parse_error_row(row):
        return "parse_error"
    return "unsuitable_lean"


def _revise_reason_counts(report_rows: List[Dict[str, Any]]) -> Dict[str, int]:
    out = {
        "total_revise": 0,
        "missing_assumption": 0,
        "task_drift": 0,
        "missing_def": 0,
    }
    for row in report_rows:
        if str(row.get("overall_status") or "").strip().lower() != "revise":
            continue
        out["total_revise"] += 1
        issue_type = row.get("issue_type")
        if not isinstance(issue_type, dict):
            continue
        if _to_bool(((issue_type.get("missing_assumption") or {}).get("value"))):
            out["missing_assumption"] += 1
        if _to_bool(((issue_type.get("task_drift") or {}).get("value"))):
            out["task_drift"] += 1
        if _to_bool(((issue_type.get("missing_def") or {}).get("value"))):
            out["missing_def"] += 1
    return out


def _hold_reason_counts(report_rows: List[Dict[str, Any]]) -> Dict[str, int]:
    out = {
        "total_hold": 0,
        "missing_dependency": 0,
        "unsuitable_lean": 0,
        "parse_error": 0,
    }
    for row in report_rows:
        if str(row.get("overall_status") or "").strip().lower() != "hold":
            continue
        out["total_hold"] += 1
        t = _hold_reason_type(row)
        if t in out:
            out[t] += 1
    return out


def _round_label(round_key: str) -> str:
    if round_key == "round2":
        return "round2_revise"
    if round_key == "round3":
        return "round3_hold(except missing_dependency)"
    return "round1_origin"


def _load_meta(meta_path: Path) -> Dict[str, Any]:
    if not meta_path.exists():
        return {}
    try:
        obj = json.loads(meta_path.read_text(encoding="utf-8"))
    except Exception:
        return {}
    return obj if isinstance(obj, dict) else {}


def _write_meta(meta_path: Path, meta: Dict[str, Any]) -> None:
    meta_path.parent.mkdir(parents=True, exist_ok=True)
    meta_path.write_text(json.dumps(meta, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _build_chat1_rows(prefix: str, rounds: Dict[str, Dict[str, Any]]) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    for rk in ROUND_ORDER:
        item = rounds.get(rk)
        if not isinstance(item, dict):
            continue
        rows.append(
            {
                "prefix": prefix,
                "round": _round_label(rk),
                "input_file_name": str(item.get("input_file_name") or ""),
                "model": str(item.get("model") or ""),
                "total": int(item.get("total") or 0),
                "accept": int(item.get("accept") or 0),
                "revise": int(item.get("revise") or 0),
                "hold": int(item.get("hold") or 0),
            }
        )
    return rows


def _build_chat2_rows(prefix: str, rounds: Dict[str, Dict[str, Any]]) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    for rk in ROUND_ORDER:
        item = rounds.get(rk)
        if not isinstance(item, dict):
            continue
        rr = item.get("revise_reasons") if isinstance(item.get("revise_reasons"), dict) else {}
        rows.append(
            {
                "prefix": prefix,
                "round": _round_label(rk),
                "total_revise": int(rr.get("total_revise") or 0),
                "missing_assumption": int(rr.get("missing_assumption") or 0),
                "task_drift": int(rr.get("task_drift") or 0),
                "missing_def": int(rr.get("missing_def") or 0),
            }
        )
    return rows


def _build_chat3_rows(prefix: str, rounds: Dict[str, Dict[str, Any]]) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    for rk in ROUND_ORDER:
        item = rounds.get(rk)
        if not isinstance(item, dict):
            continue
        hr = item.get("hold_reasons") if isinstance(item.get("hold_reasons"), dict) else {}
        rows.append(
            {
                "prefix": prefix,
                "round": _round_label(rk),
                "total_hold": int(hr.get("total_hold") or 0),
                "missing_dependency": int(hr.get("missing_dependency") or 0),
                "unsuitable_lean": int(hr.get("unsuitable_lean") or 0),
                "parse_error": int(hr.get("parse_error") or 0),
            }
        )
    return rows


def _render_markdown(prefix: str, chat1_rows: List[Dict[str, Any]], chat2_rows: List[Dict[str, Any]], chat3_rows: List[Dict[str, Any]]) -> str:
    lines = [f"# {prefix}", "", "## Processing Efficiency (chat1)", ""]
    lines.extend(
        [
            "| prefix | round | input_file_name | model | total | accept | revise | hold |",
            "|---|---|---|---|---:|---:|---:|---:|",
        ]
    )
    for r in chat1_rows:
        lines.append(
            f"| {r['prefix']} | {r['round']} | {r['input_file_name']} | {r['model']} | "
            f"{int(r['total'])} | {int(r['accept'])} | {int(r['revise'])} | {int(r['hold'])} |"
        )

    lines.extend(["", "## Revise Reasons (chat2)", ""])
    lines.extend(
        [
            "| prefix | round | total_revise | missing_assumption | task_drift | missing_def |",
            "|---|---|---:|---:|---:|---:|",
        ]
    )
    for r in chat2_rows:
        lines.append(
            f"| {r['prefix']} | {r['round']} | {int(r['total_revise'])} | "
            f"{int(r['missing_assumption'])} | {int(r['task_drift'])} | {int(r['missing_def'])} |"
        )

    lines.extend(["", "## Hold Reasons (chat3)", ""])
    lines.extend(
        [
            "| prefix | round | total_hold | missing_dependency | unsuitable_lean | parse_error |",
            "|---|---|---:|---:|---:|---:|",
        ]
    )
    for r in chat3_rows:
        lines.append(
            f"| {r['prefix']} | {r['round']} | {int(r['total_hold'])} | "
            f"{int(r['missing_dependency'])} | {int(r['unsuitable_lean'])} | {int(r['parse_error'])} |"
        )

    lines.append("")
    return "\n".join(lines)


def _write_csv(csv_path: Path, rows: List[Dict[str, Any]]) -> None:
    csv_path.parent.mkdir(parents=True, exist_ok=True)
    with csv_path.open("w", encoding="utf-8", newline="") as f:
        w = csv.writer(f)
        w.writerow(["prefix", "round", "input_file_name", "model", "total", "accept", "revise", "hold"])
        for r in rows:
            w.writerow(
                [
                    r["prefix"],
                    r["round"],
                    r["input_file_name"],
                    r["model"],
                    int(r["total"]),
                    int(r["accept"]),
                    int(r["revise"]),
                    int(r["hold"]),
                ]
            )


def _write_reason_csv(csv_path: Path, rows: List[Dict[str, Any]], *, kind: str) -> None:
    csv_path.parent.mkdir(parents=True, exist_ok=True)
    with csv_path.open("w", encoding="utf-8", newline="") as f:
        w = csv.writer(f)
        if kind == "chat2":
            w.writerow(["prefix", "round", "total_revise", "missing_assumption", "task_drift", "missing_def"])
            for r in rows:
                w.writerow(
                    [
                        r["prefix"],
                        r["round"],
                        int(r["total_revise"]),
                        int(r["missing_assumption"]),
                        int(r["task_drift"]),
                        int(r["missing_def"]),
                    ]
                )
        else:
            w.writerow(["prefix", "round", "total_hold", "missing_dependency", "unsuitable_lean", "parse_error"])
            for r in rows:
                w.writerow(
                    [
                        r["prefix"],
                        r["round"],
                        int(r["total_hold"]),
                        int(r["missing_dependency"]),
                        int(r["unsuitable_lean"]),
                        int(r["parse_error"]),
                    ]
                )


def update_reviewchat_for_file(
    *,
    in_file: Path,
    in_root: Path,
    reviewlog_root: Path,
    reviewchat_root: Path,
    model_name: str = "",
) -> Optional[Path]:
    rel = in_file.resolve().relative_to(in_root.resolve())
    reviewlog_file = reviewlog_root / rel
    if not reviewlog_file.exists():
        return None

    input_rows = _load_list(in_file)
    report_rows = _load_list(reviewlog_file)
    counts = _status_counts(report_rows)
    revise_reasons = _revise_reason_counts(report_rows)
    hold_reasons = _hold_reason_counts(report_rows)

    prefix = _normalize_prefix(in_file.stem)
    round_key = _detect_round(in_file, reviewlog_file)
    model = str(model_name or "").strip()

    out_dir = reviewchat_root / prefix
    meta_path = out_dir / "table.json"
    md_path = out_dir / "table.md"
    csv_path = out_dir / "table.csv"
    chat2_csv_path = out_dir / "table_chat2.csv"
    chat3_csv_path = out_dir / "table_chat3.csv"

    meta = _load_meta(meta_path)
    if str(meta.get("prefix") or "").strip() != prefix:
        meta = {"prefix": prefix, "rounds": {}}
    rounds = meta.get("rounds")
    if not isinstance(rounds, dict):
        rounds = {}

    rounds[round_key] = {
        "input_file_name": in_file.name,
        "model": model,
        "total": len(input_rows),
        "accept": counts["accept"],
        "revise": counts["revise"],
        "hold": counts["hold"],
        "revise_reasons": revise_reasons,
        "hold_reasons": hold_reasons,
    }

    meta["prefix"] = prefix
    meta["rounds"] = rounds
    _write_meta(meta_path, meta)

    chat1_rows = _build_chat1_rows(prefix, rounds)
    chat2_rows = _build_chat2_rows(prefix, rounds)
    chat3_rows = _build_chat3_rows(prefix, rounds)
    md_path.write_text(_render_markdown(prefix, chat1_rows, chat2_rows, chat3_rows), encoding="utf-8")
    _write_csv(csv_path, chat1_rows)
    _write_reason_csv(chat2_csv_path, chat2_rows, kind="chat2")
    _write_reason_csv(chat3_csv_path, chat3_rows, kind="chat3")
    return out_dir


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description="Build per-prefix reviewchat tables.")
    ap.add_argument("--in-root", type=str, default="output_json_naturalized", help="Input root")
    ap.add_argument("--reviewlog-root", type=str, default="output_review/reviewlog", help="Reviewlog root")
    ap.add_argument("--reviewchat-root", type=str, default="output_review/reviewchat", help="Reviewchat output root")
    ap.add_argument("--in-file", type=str, default="", help="Single input file")
    ap.add_argument("--model", type=str, default="", help="Model name override")
    return ap.parse_args()


def main() -> None:
    args = parse_args()
    in_root = Path(args.in_root).expanduser().resolve()
    reviewlog_root = Path(args.reviewlog_root).expanduser().resolve()
    reviewchat_root = Path(args.reviewchat_root).expanduser().resolve()
    model_name = str(args.model or "").strip()
    if not model_name:
        model_name = _load_config_model()

    if args.in_file:
        f = Path(args.in_file).expanduser().resolve()
        out = update_reviewchat_for_file(
            in_file=f,
            in_root=in_root,
            reviewlog_root=reviewlog_root,
            reviewchat_root=reviewchat_root,
            model_name=model_name,
        )
        if out is None:
            print(f"[reviewchat][skip] missing reviewlog for: {f}")
        else:
            print(f"[reviewchat][ok] {f} -> {out}")
        return

    files = list(_iter_json_files(in_root))
    if not files:
        print(f"No JSON files found under {in_root}")
        return
    for i, f in enumerate(files, start=1):
        out = update_reviewchat_for_file(
            in_file=f,
            in_root=in_root,
            reviewlog_root=reviewlog_root,
            reviewchat_root=reviewchat_root,
            model_name=model_name,
        )
        if out is None:
            print(f"[reviewchat][skip][{i}/{len(files)}] {f}")
        else:
            print(f"[reviewchat][ok][{i}/{len(files)}] {f} -> {out}")


if __name__ == "__main__":
    main()
