#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""Pipeline runner with resume support for the book pipeline."""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple


PROJECT_ROOT = Path(__file__).resolve().parent
INPUT_PDF_DIR: Path
OUTPUT_JSON_DIR: Path
WORK_DIR: Path
OCR_MAX_TOKENS: Optional[int]
ONLY_THESE_STEMS: set[str]
OVERWRITE_JSON: bool
OCR_WORKERS: Optional[int]
THINK_WORKERS: Optional[int]
STRICT_RESUME: bool
ATOMIC_OUTPUTS: bool
CLEAN_STALE_TMPS: bool
TEX_WARNINGS_JSON: bool
TEX_EMIT_RAW: bool
TEX_TYPE_REFINE: bool
TEX_NO_DIRECT_ANSWER: bool
TEX_LLM_SELF_CHECK: bool
TEX_LLM_MODEL: str
TEX_LLM_MAX_ITEMS: int
TEX_LLM_MAX_ROUNDS: int
TEX_LLM_CACHE_DIR: str
TEX_LLM_NO_CACHE: bool
TEX_LLM_TYPE_CHECK: bool
TEX_LLM_TYPE_MAX_ITEMS: int
TEX_LLM_DIRECT_ANSWER_FALLBACK: bool
TEX_LLM_DIRECT_ANSWER_MAX_ITEMS: int
TEX_REQUIRE_CLEAN: bool
TEX_FINAL_JSON_ONLY: bool
MDTOTEX_SKIP_TAG_RECOVERY: bool
OUTPUT_JSON_NATURALIZED_DIR: Path
ENABLE_NATURALIZE: bool
NATURALIZE_MODEL: str
NATURALIZE_MAX_TOKENS: int
NATURALIZE_MAX_ITEMS: int
NATURALIZE_PROMPT_VERSION: str
NATURALIZE_CACHE_DIR: str
NATURALIZE_NO_CACHE: bool
NATURALIZE_DISABLE_LLM: bool
NATURALIZE_FORCE: bool
NATURALIZE_CLEAN_CACHE_ON_EXIT: bool
OUTPUT_REVIEW_DIR: Path
ENABLE_REVIEW: bool
REVIEW_MODEL: str
REVIEW_MAX_TOKENS: int
REVIEW_MAX_ITEMS: int
REVIEW_LLM_RETRIES: int
REVIEW_DISABLE_LLM: bool
REVIEW_FORCE: bool
ENABLE_HOLD_PIPELINE: bool


def find_settings_json() -> Path:
    path = PROJECT_ROOT / "settings.json"
    if not path.exists():
        raise FileNotFoundError(f"Missing settings file: {path}")
    return path


def load_settings() -> dict[str, Any]:
    path = find_settings_json()
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"{path} must contain a JSON object.")
    return data


def get_setting(settings: dict[str, Any], key: str, default: Any) -> Any:
    return settings.get(key, default)


def run_cmd(cmd: list[str]) -> None:
    print("\n$ " + " ".join(cmd), flush=True)
    env = os.environ.copy()
    # Keep valid HTTP(S) proxies, drop only unsupported socks:// proxy values.
    # httpx/OpenAI client raises on values like "socks://127.0.0.1:7897/".
    for k in ("http_proxy", "https_proxy", "HTTP_PROXY", "HTTPS_PROXY", "ALL_PROXY", "all_proxy"):
        v = str(env.get(k, "") or "").strip().lower()
        if v.startswith("socks://"):
            env.pop(k, None)
    proc = subprocess.run(cmd, stdout=sys.stdout, stderr=sys.stderr, env=env)
    if proc.returncode != 0:
        raise SystemExit(proc.returncode)


def ensure_scripts_exist(script_dir: Path) -> tuple[Path, Path, Path]:
    src_dir = script_dir / "src" / "book"
    pdf_to_md = src_dir / "pdfTomd.py"
    md_to_tex = src_dir / "mdTotex.py"
    tex_to_json = src_dir / "texTojson.py"
    missing = [p for p in [pdf_to_md, md_to_tex, tex_to_json] if not p.exists()]
    if missing:
        raise SystemExit("Missing scripts:\n" + "\n".join(str(p) for p in missing))
    return pdf_to_md, md_to_tex, tex_to_json


def ensure_naturalize_script_exists(script_dir: Path) -> Path:
    p = script_dir / "src" / "book" / "jsonNaturalize.py"
    if not p.exists():
        raise SystemExit(f"Missing script: {p}")
    return p


def ensure_review_script_exists(script_dir: Path) -> Path:
    p = script_dir / "src" / "review" / "read.py"
    if not p.exists():
        raise SystemExit(f"Missing script: {p}")
    return p


def ensure_summary_script_exists(script_dir: Path) -> Path:
    p = script_dir / "src" / "review" / "summary.py"
    if not p.exists():
        raise SystemExit(f"Missing script: {p}")
    return p


def _tmp_path(final_path: Path) -> Path:
    return final_path.with_name(final_path.name + ".tmp")


def _file_nonempty(p: Path) -> bool:
    return p.exists() and p.is_file() and p.stat().st_size > 0


_PAGE_SENTINEL_RE = re.compile(r"(?m)^\s*<!--\s*PAGE\s+(\d+)\s*-->\s*$")


def _pdf_page_count(pdf_path: Path) -> Optional[int]:
    """Best-effort PDF page count using PyMuPDF (fitz)."""
    try:
        import fitz  # type: ignore
    except Exception:
        return None
    try:
        doc = fitz.open(str(pdf_path))
        try:
            return int(doc.page_count)
        finally:
            doc.close()
    except Exception:
        return None


def md_complete(md_path: Path, pdf_path: Path) -> bool:
    """MD is complete iff it contains the last PAGE sentinel matching PDF page count."""
    if not _file_nonempty(md_path):
        return False
    if not STRICT_RESUME:
        return True

    # Read a tail window first (fast for large files); fall back to full read if needed.
    try:
        tail_bytes = 1024 * 1024  # 1 MiB
        with md_path.open("rb") as f:
            try:
                f.seek(0, 2)
                size = f.tell()
                f.seek(max(0, size - tail_bytes), 0)
            except Exception:
                # Some file-like implementations may not support seek/tell well; fall back.
                f.seek(0)
            chunk = f.read()
        tail_text = chunk.decode("utf-8", errors="ignore")
        pages = [int(x) for x in _PAGE_SENTINEL_RE.findall(tail_text)]
        if not pages:
            # fallback: full file read
            text = md_path.read_text(encoding="utf-8", errors="ignore")
            pages = [int(x) for x in _PAGE_SENTINEL_RE.findall(text)]
    except Exception:
        return False
    if not pages:
        # If the OCR script didn't emit page sentinels, fall back to non-empty.
        return True

    max_md_page = max(pages)
    n_pdf = _pdf_page_count(pdf_path)
    if n_pdf is None:
        # can't confirm; accept as complete
        return True

    return max_md_page >= n_pdf


def tex_complete(tex_path: Path) -> bool:
    """TEX is complete iff it has \begin{document} and ends with \end{document} (best-effort)."""
    if not _file_nonempty(tex_path):
        return False
    if not STRICT_RESUME:
        return True

    try:
        head_bytes = 64 * 1024  # 64 KiB
        tail_bytes = 64 * 1024  # 64 KiB

        with tex_path.open("rb") as f:
            head = f.read(head_bytes)

            try:
                f.seek(0, 2)
                size = f.tell()
                f.seek(max(0, size - tail_bytes), 0)
            except Exception:
                # fall back: if seek/tell fails, just keep reading (small files)
                pass

            tail = f.read()

        head_text = head.decode("utf-8", errors="ignore")
        tail_text = tail.decode("utf-8", errors="ignore")
    except Exception:
        return False

    if "\\begin{document}" not in head_text and "\\begin{document}" not in tail_text:
        return False

    # Allow trailing whitespace/comments after \end{document}
    if re.search(r"\\end\{document\}\s*\Z", tail_text) is None:
        return False

    return True


def json_complete(json_path: Path) -> bool:
    """JSON is complete iff it parses and is a non-empty list/dict."""
    if not _file_nonempty(json_path):
        return False
    if not STRICT_RESUME:
        return True

    try:
        obj = json.loads(json_path.read_text(encoding="utf-8"))
    except Exception:
        return False

    if isinstance(obj, list):
        return len(obj) > 0
    if isinstance(obj, dict):
        return len(obj) > 0
    return False


def naturalized_complete(json_path: Path) -> bool:
    return json_complete(json_path)


def review_complete(json_path: Path, naturalized_path: Optional[Path] = None) -> bool:
    if not json_complete(json_path):
        return False
    if naturalized_path is None or not json_complete(naturalized_path):
        return True
    try:
        review_obj = json.loads(json_path.read_text(encoding="utf-8"))
        nat_obj = json.loads(naturalized_path.read_text(encoding="utf-8"))
    except Exception:
        return False
    if not isinstance(review_obj, list) or not isinstance(nat_obj, list):
        return False
    return len(review_obj) == len(nat_obj)


def summary_complete(naturalized_path: Path, out_root: Path) -> bool:
    if not json_complete(naturalized_path):
        return False
    try:
        rel = naturalized_path.relative_to(OUTPUT_JSON_NATURALIZED_DIR)
    except Exception:
        return False
    hold_path = out_root / "hold" / rel
    accept_path = out_root / "accept" / rel
    revise_stem = rel.stem if rel.stem.endswith("-re2") else (rel.stem + "-re2")
    revise_path = out_root / "revise" / rel.with_name(revise_stem + rel.suffix)
    if not hold_path.exists() or not accept_path.exists() or not revise_path.exists():
        return False
    try:
        n_in = len(json.loads(naturalized_path.read_text(encoding="utf-8")))
        n_hold = len(json.loads(hold_path.read_text(encoding="utf-8")))
        n_accept = len(json.loads(accept_path.read_text(encoding="utf-8")))
        n_revise = len(json.loads(revise_path.read_text(encoding="utf-8")))
    except Exception:
        return False
    return int(n_hold) + int(n_accept) + int(n_revise) == int(n_in)


def _read_stats_json(path: Path) -> Dict[str, int]:
    if not path.exists():
        return {}
    try:
        obj = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {}
    if not isinstance(obj, dict):
        return {}
    out: Dict[str, int] = {}
    for k in ("rows", "llm_touched", "ok", "fallback", "skipped", "failed"):
        try:
            out[k] = int(obj.get(k, 0))
        except Exception:
            out[k] = 0
    return out


Validator = Callable[[Path], bool]


def run_stage_atomic(
    *,
    cmd: list[str],
    out_path: Path,
    validate_out: Validator,
) -> None:
    tmp = _tmp_path(out_path)
    if CLEAN_STALE_TMPS and tmp.exists():
        try:
            tmp.unlink()
        except Exception:
            pass

    if len(cmd) < 4:
        raise RuntimeError("cmd too short (expected: python script IN OUT [flags...])")
    cmd2 = list(cmd)
    cmd2[3] = str(tmp)

    run_cmd(cmd2)

    if not validate_out(tmp):
        raise SystemExit(f"Stage produced incomplete output: {tmp}")

    tmp.replace(out_path)


def process_one(
    pdf_path: Path,
    pdf_to_md: Path,
    md_to_tex: Path,
    tex_to_json: Path,
    *,
    input_pdf_dir: Path,
    output_json_dir: Path,
    work_dir: Path,
) -> Tuple[Path, Optional[Dict[str, int]]]:
    rel_pdf = pdf_path.relative_to(input_pdf_dir)
    rel_no_suffix = rel_pdf.with_suffix("")

    job_dir = work_dir / rel_no_suffix
    job_dir.mkdir(parents=True, exist_ok=True)

    stem = pdf_path.stem
    md_path = job_dir / f"{stem}.md"
    tex_path = job_dir / f"{stem}.tex"

    json_path = (output_json_dir / rel_pdf).with_suffix(".json")
    json_path.parent.mkdir(parents=True, exist_ok=True)

    naturalized_path = (OUTPUT_JSON_NATURALIZED_DIR / rel_pdf).with_suffix(".json")
    naturalized_path.parent.mkdir(parents=True, exist_ok=True)
    naturalize_stats_path = job_dir / f"{stem}.naturalize.stats.json"
    review_path = (OUTPUT_REVIEW_DIR / rel_pdf).with_suffix(".json")
    review_path.parent.mkdir(parents=True, exist_ok=True)

    needs_naturalize = (
        ENABLE_NATURALIZE
        and (
            NATURALIZE_FORCE
            or (not naturalized_complete(naturalized_path))
        )
    )
    needs_review = (
        ENABLE_REVIEW
        and ENABLE_NATURALIZE
        and (
            REVIEW_FORCE
            or (not review_complete(review_path, naturalized_path))
        )
    )
    summary_out_root = OUTPUT_REVIEW_DIR.parent
    needs_summary = (
        ENABLE_REVIEW
        and ENABLE_NATURALIZE
        and (
            REVIEW_FORCE
            or (not summary_complete(naturalized_path, summary_out_root))
        )
    )

    def _run_review_for_path(in_nat_json_path: Path) -> None:
        review_read = ensure_review_script_exists(PROJECT_ROOT)
        print(f"[stage] JSON review: {in_nat_json_path} -> {review_path}", flush=True)
        cmd5 = [sys.executable, str(review_read), str(in_nat_json_path), str(OUTPUT_REVIEW_DIR)]
        cmd5 += ["--input-root", str(OUTPUT_JSON_NATURALIZED_DIR)]
        if REVIEW_MODEL:
            cmd5 += ["--model", str(REVIEW_MODEL)]
        cmd5 += ["--max-tokens", str(int(REVIEW_MAX_TOKENS))]
        cmd5 += ["--max-items", str(int(REVIEW_MAX_ITEMS))]
        cmd5 += ["--llm-retries", str(int(REVIEW_LLM_RETRIES))]
        if REVIEW_DISABLE_LLM:
            cmd5 += ["--disable-llm"]
        if REVIEW_FORCE:
            cmd5 += ["--force"]
        run_cmd(cmd5)
        if not review_complete(review_path, in_nat_json_path):
            raise SystemExit(f"Review output incomplete: {review_path}")

    def _run_summary_for_path(in_nat_json_path: Path) -> None:
        review_summary = ensure_summary_script_exists(PROJECT_ROOT)
        print(f"[stage] JSON summary: {in_nat_json_path} -> {summary_out_root}", flush=True)
        cmd6 = [
            sys.executable,
            str(review_summary),
            "--summary-only",
            "--in-root",
            str(OUTPUT_JSON_NATURALIZED_DIR),
            "--in-file",
            str(in_nat_json_path),
            "--reviewlog-root",
            str(OUTPUT_REVIEW_DIR),
            "--out-root",
            str(summary_out_root),
            "--reviewchat-root",
            str(summary_out_root / "reviewchat"),
        ]
        run_cmd(cmd6)
        if not summary_complete(in_nat_json_path, summary_out_root):
            raise SystemExit(f"Summary output incomplete for: {in_nat_json_path}")

    if json_complete(json_path) and not OVERWRITE_JSON:
        print(f"[skip] {rel_pdf.as_posix()} -> JSON exists: {json_path}")
        if needs_naturalize:
            json_naturalize = ensure_naturalize_script_exists(PROJECT_ROOT)
            cmd4 = [sys.executable, str(json_naturalize), str(json_path), str(naturalized_path)]
            if NATURALIZE_MODEL:
                cmd4 += ["--model", str(NATURALIZE_MODEL)]
            cmd4 += ["--max-tokens", str(int(NATURALIZE_MAX_TOKENS))]
            cmd4 += ["--max-items", str(int(NATURALIZE_MAX_ITEMS))]
            if NATURALIZE_PROMPT_VERSION:
                cmd4 += ["--prompt-version", str(NATURALIZE_PROMPT_VERSION)]
            if NATURALIZE_CACHE_DIR:
                cmd4 += ["--cache-dir", str(NATURALIZE_CACHE_DIR)]
            if NATURALIZE_NO_CACHE:
                cmd4 += ["--no-cache"]
            if NATURALIZE_DISABLE_LLM:
                cmd4 += ["--disable-llm"]
            if NATURALIZE_FORCE:
                cmd4 += ["--force"]
            if not NATURALIZE_CLEAN_CACHE_ON_EXIT:
                cmd4 += ["--no-cleanup-cache-on-exit"]
            cmd4 += ["--stats-out", str(naturalize_stats_path)]

            run_cmd(cmd4)
            if not naturalized_complete(naturalized_path):
                raise SystemExit(f"Naturalize output incomplete: {naturalized_path}")
            if needs_review:
                _run_review_for_path(naturalized_path)
            if needs_summary:
                _run_summary_for_path(naturalized_path)
            return json_path, _read_stats_json(naturalize_stats_path)
        if needs_review:
            _run_review_for_path(naturalized_path)
        if needs_summary:
            _run_summary_for_path(naturalized_path)
        return json_path, None

    if md_complete(md_path, pdf_path):
        print(f"[resume] skip PDF->MD (complete): {md_path}")
    else:
        cmd1 = [sys.executable, str(pdf_to_md), str(pdf_path), str(md_path)]
        if OCR_MAX_TOKENS is not None:
            cmd1 += ["--max-tokens", str(OCR_MAX_TOKENS)]
        if OCR_WORKERS is not None:
            cmd1 += ["--workers", str(int(OCR_WORKERS))]

        if ATOMIC_OUTPUTS:
            run_stage_atomic(
                cmd=cmd1,
                out_path=md_path,
                validate_out=lambda p: md_complete(p, pdf_path),
            )
        else:
            run_cmd(cmd1)
            if not md_complete(md_path, pdf_path):
                raise SystemExit(f"PDF->MD output incomplete: {md_path}")

    if tex_complete(tex_path):
        print(f"[resume] skip MD->TEX (complete): {tex_path}")
    else:
        print(f"[stage] MD->TEX: {md_path} -> {tex_path}", flush=True)
        cmd2 = [sys.executable, str(md_to_tex), str(md_path), str(tex_path)]
        if THINK_WORKERS is not None:
            cmd2 += ["--workers", str(int(THINK_WORKERS))]
        # Single route: mdTotex handles Theorem/Lemma/Definition detection directly.
        cmd2 += ["--detect-stmts"]
        # Keep tag recovery enabled in single-route mode.
        if MDTOTEX_SKIP_TAG_RECOVERY:
            print("[info] single route detected: ignore MDTOTEX_SKIP_TAG_RECOVERY and keep tag recovery enabled")

        if ATOMIC_OUTPUTS:
            run_stage_atomic(
                cmd=cmd2,
                out_path=tex_path,
                validate_out=tex_complete,
            )
        else:
            run_cmd(cmd2)
            if not tex_complete(tex_path):
                raise SystemExit(f"MD->TEX output incomplete: {tex_path}")

    if json_complete(json_path) and not OVERWRITE_JSON:
        print(f"[resume] skip TEX->JSON (complete): {json_path}")
        return json_path, None

    print(f"[stage] TEX->JSON: {tex_path} -> {json_path}", flush=True)
    cmd3 = [sys.executable, str(tex_to_json), str(tex_path), str(json_path)]
    # Carry per-PDF source name into JSON rows (e.g. "book/foo/bar").
    cmd3 += ["--source-name", rel_no_suffix.as_posix()]
    if TEX_WARNINGS_JSON:
        cmd3 += ["--warnings-json", str(job_dir / f"{stem}.warnings.json")]
    if TEX_EMIT_RAW:
        cmd3 += ["--emit-raw"]
    if TEX_TYPE_REFINE:
        cmd3 += ["--type-refine"]
    if TEX_NO_DIRECT_ANSWER:
        cmd3 += ["--no-direct-answer"]
    if TEX_LLM_SELF_CHECK:
        cmd3 += ["--llm-self-check"]
    if TEX_LLM_MODEL:
        cmd3 += ["--llm-model", str(TEX_LLM_MODEL)]
    cmd3 += ["--llm-max-items", str(int(TEX_LLM_MAX_ITEMS))]
    cmd3 += ["--llm-max-rounds", str(int(TEX_LLM_MAX_ROUNDS))]
    if TEX_LLM_CACHE_DIR:
        cmd3 += ["--llm-cache-dir", str(TEX_LLM_CACHE_DIR)]
    if TEX_LLM_NO_CACHE:
        cmd3 += ["--llm-no-cache"]
    if TEX_LLM_TYPE_CHECK:
        cmd3 += ["--llm-type-check"]
    cmd3 += ["--llm-type-max-items", str(int(TEX_LLM_TYPE_MAX_ITEMS))]
    if TEX_LLM_DIRECT_ANSWER_FALLBACK:
        cmd3 += ["--llm-direct-answer-fallback"]
    cmd3 += ["--llm-direct-answer-max-items", str(int(TEX_LLM_DIRECT_ANSWER_MAX_ITEMS))]
    if TEX_REQUIRE_CLEAN:
        cmd3 += ["--require-clean"]
    if TEX_FINAL_JSON_ONLY:
        cmd3 += ["--final-json-only"]
    if TEX_RECURSIVE_MORE:
        cmd3 += ["--recursive-more"]
    cmd3 += ["--recursive-more-max-steps", str(int(TEX_RECURSIVE_MORE_MAX_STEPS))]
    cmd3 += ["--recursive-more-max-items", str(int(TEX_RECURSIVE_MORE_MAX_ITEMS))]
    if TEX_CLEAN_PROBLEM:
        cmd3 += ["--clean-problem"]

    if ATOMIC_OUTPUTS:
        run_stage_atomic(
            cmd=cmd3,
            out_path=json_path,
            validate_out=json_complete,
        )
    else:
        run_cmd(cmd3)
        if not json_complete(json_path):
            raise SystemExit(f"TEX->JSON output incomplete: {json_path}")

    if ENABLE_NATURALIZE:
        json_naturalize = ensure_naturalize_script_exists(PROJECT_ROOT)
        print(f"[stage] JSON naturalize: {json_path} -> {naturalized_path}", flush=True)
        cmd4 = [sys.executable, str(json_naturalize), str(json_path), str(naturalized_path)]
        if NATURALIZE_MODEL:
            cmd4 += ["--model", str(NATURALIZE_MODEL)]
        cmd4 += ["--max-tokens", str(int(NATURALIZE_MAX_TOKENS))]
        cmd4 += ["--max-items", str(int(NATURALIZE_MAX_ITEMS))]
        if NATURALIZE_PROMPT_VERSION:
            cmd4 += ["--prompt-version", str(NATURALIZE_PROMPT_VERSION)]
        if NATURALIZE_CACHE_DIR:
            cmd4 += ["--cache-dir", str(NATURALIZE_CACHE_DIR)]
        if NATURALIZE_NO_CACHE:
            cmd4 += ["--no-cache"]
        if NATURALIZE_DISABLE_LLM:
            cmd4 += ["--disable-llm"]
        if NATURALIZE_FORCE:
            cmd4 += ["--force"]
        if not NATURALIZE_CLEAN_CACHE_ON_EXIT:
            cmd4 += ["--no-cleanup-cache-on-exit"]
        cmd4 += ["--stats-out", str(naturalize_stats_path)]

        run_cmd(cmd4)
        if not naturalized_complete(naturalized_path):
            raise SystemExit(f"Naturalize output incomplete: {naturalized_path}")
        if needs_review:
            _run_review_for_path(naturalized_path)
        if needs_summary:
            _run_summary_for_path(naturalized_path)
        return json_path, _read_stats_json(naturalize_stats_path)

    return json_path, None


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description="Run the OCR -> Markdown -> TeX -> JSON pipeline.")
    return ap.parse_args()


def main() -> None:
    global INPUT_PDF_DIR, OUTPUT_JSON_DIR, WORK_DIR
    global OCR_MAX_TOKENS, ONLY_THESE_STEMS, OVERWRITE_JSON
    global OCR_WORKERS, THINK_WORKERS, STRICT_RESUME, ATOMIC_OUTPUTS, CLEAN_STALE_TMPS
    global TEX_WARNINGS_JSON, TEX_EMIT_RAW, TEX_TYPE_REFINE, TEX_NO_DIRECT_ANSWER
    global TEX_LLM_SELF_CHECK, TEX_LLM_MODEL, TEX_LLM_MAX_ITEMS, TEX_LLM_MAX_ROUNDS
    global TEX_LLM_CACHE_DIR, TEX_LLM_NO_CACHE
    global TEX_LLM_TYPE_CHECK, TEX_LLM_TYPE_MAX_ITEMS
    global TEX_LLM_DIRECT_ANSWER_FALLBACK, TEX_LLM_DIRECT_ANSWER_MAX_ITEMS
    global TEX_REQUIRE_CLEAN, TEX_FINAL_JSON_ONLY
    global TEX_RECURSIVE_MORE, TEX_RECURSIVE_MORE_MAX_STEPS, TEX_RECURSIVE_MORE_MAX_ITEMS
    global TEX_CLEAN_PROBLEM
    global MDTOTEX_SKIP_TAG_RECOVERY
    global OUTPUT_JSON_NATURALIZED_DIR, ENABLE_NATURALIZE
    global NATURALIZE_MODEL, NATURALIZE_MAX_TOKENS, NATURALIZE_MAX_ITEMS
    global NATURALIZE_PROMPT_VERSION, NATURALIZE_CACHE_DIR
    global NATURALIZE_NO_CACHE, NATURALIZE_DISABLE_LLM, NATURALIZE_FORCE, NATURALIZE_CLEAN_CACHE_ON_EXIT
    global OUTPUT_REVIEW_DIR, ENABLE_REVIEW, REVIEW_MODEL
    global REVIEW_MAX_TOKENS, REVIEW_MAX_ITEMS, REVIEW_LLM_RETRIES, REVIEW_DISABLE_LLM, REVIEW_FORCE
    global ENABLE_HOLD_PIPELINE

    settings = load_settings()
    INPUT_PDF_DIR = PROJECT_ROOT / str(get_setting(settings, "INPUT_PDF_DIR", "input_pdfs"))
    OUTPUT_JSON_DIR = PROJECT_ROOT / str(get_setting(settings, "OUTPUT_JSON_DIR", "output_json"))
    OUTPUT_JSON_NATURALIZED_DIR = PROJECT_ROOT / str(
        get_setting(settings, "OUTPUT_JSON_NATURALIZED_DIR", "output_json_naturalized")
    )
    OUTPUT_REVIEW_DIR = PROJECT_ROOT / str(
        get_setting(settings, "OUTPUT_REVIEW_DIR", "output_review/reviewlog")
    )
    WORK_DIR = PROJECT_ROOT / str(get_setting(settings, "WORK_DIR", "work"))
    OCR_MAX_TOKENS = get_setting(settings, "OCR_MAX_TOKENS", None)
    ONLY_THESE_STEMS = set(get_setting(settings, "ONLY_THESE_STEMS", []))
    OVERWRITE_JSON = bool(get_setting(settings, "OVERWRITE_JSON", False))
    OCR_WORKERS = get_setting(settings, "OCR_WORKERS", 4)
    THINK_WORKERS = get_setting(settings, "THINK_WORKERS", 4)
    STRICT_RESUME = bool(get_setting(settings, "STRICT_RESUME", True))
    ATOMIC_OUTPUTS = bool(get_setting(settings, "ATOMIC_OUTPUTS", True))
    CLEAN_STALE_TMPS = bool(get_setting(settings, "CLEAN_STALE_TMPS", True))
    TEX_WARNINGS_JSON = bool(get_setting(settings, "TEX_WARNINGS_JSON", False))
    TEX_EMIT_RAW = bool(get_setting(settings, "TEX_EMIT_RAW", False))
    TEX_TYPE_REFINE = bool(get_setting(settings, "TEX_TYPE_REFINE", False))
    TEX_NO_DIRECT_ANSWER = bool(get_setting(settings, "TEX_NO_DIRECT_ANSWER", False))
    TEX_LLM_SELF_CHECK = bool(get_setting(settings, "TEX_LLM_SELF_CHECK", False))
    TEX_LLM_MODEL = str(get_setting(settings, "TEX_LLM_MODEL", "gpt-5-mini"))
    TEX_LLM_MAX_ITEMS = int(get_setting(settings, "TEX_LLM_MAX_ITEMS", 20))
    TEX_LLM_MAX_ROUNDS = int(get_setting(settings, "TEX_LLM_MAX_ROUNDS", 3))
    TEX_LLM_CACHE_DIR = str(get_setting(settings, "TEX_LLM_CACHE_DIR", ""))
    TEX_LLM_NO_CACHE = bool(get_setting(settings, "TEX_LLM_NO_CACHE", False))
    TEX_LLM_TYPE_CHECK = bool(get_setting(settings, "TEX_LLM_TYPE_CHECK", False))
    TEX_LLM_TYPE_MAX_ITEMS = int(get_setting(settings, "TEX_LLM_TYPE_MAX_ITEMS", 200))
    TEX_LLM_DIRECT_ANSWER_FALLBACK = bool(get_setting(settings, "TEX_LLM_DIRECT_ANSWER_FALLBACK", False))
    TEX_LLM_DIRECT_ANSWER_MAX_ITEMS = int(get_setting(settings, "TEX_LLM_DIRECT_ANSWER_MAX_ITEMS", 0))
    TEX_REQUIRE_CLEAN = bool(get_setting(settings, "TEX_REQUIRE_CLEAN", False))
    TEX_FINAL_JSON_ONLY = bool(get_setting(settings, "TEX_FINAL_JSON_ONLY", False))
    TEX_RECURSIVE_MORE = bool(get_setting(settings, "TEX_RECURSIVE_MORE", False))
    TEX_RECURSIVE_MORE_MAX_STEPS = int(get_setting(settings, "TEX_RECURSIVE_MORE_MAX_STEPS", 50))
    TEX_RECURSIVE_MORE_MAX_ITEMS = int(get_setting(settings, "TEX_RECURSIVE_MORE_MAX_ITEMS", 200))
    TEX_CLEAN_PROBLEM = bool(get_setting(settings, "TEX_CLEAN_PROBLEM", False))
    MDTOTEX_SKIP_TAG_RECOVERY = bool(get_setting(settings, "MDTOTEX_SKIP_TAG_RECOVERY", False))
    ENABLE_NATURALIZE = bool(get_setting(settings, "ENABLE_NATURALIZE", False))
    NATURALIZE_MODEL = str(get_setting(settings, "NATURALIZE_MODEL", ""))
    NATURALIZE_MAX_TOKENS = int(get_setting(settings, "NATURALIZE_MAX_TOKENS", 900))
    NATURALIZE_MAX_ITEMS = int(get_setting(settings, "NATURALIZE_MAX_ITEMS", 0))
    NATURALIZE_PROMPT_VERSION = str(get_setting(settings, "NATURALIZE_PROMPT_VERSION", "v1"))
    NATURALIZE_CACHE_DIR = str(get_setting(settings, "NATURALIZE_CACHE_DIR", ""))
    NATURALIZE_NO_CACHE = bool(get_setting(settings, "NATURALIZE_NO_CACHE", False))
    NATURALIZE_DISABLE_LLM = bool(get_setting(settings, "NATURALIZE_DISABLE_LLM", False))
    NATURALIZE_FORCE = bool(get_setting(settings, "NATURALIZE_FORCE", False))
    NATURALIZE_CLEAN_CACHE_ON_EXIT = bool(get_setting(settings, "NATURALIZE_CLEAN_CACHE_ON_EXIT", True))
    ENABLE_REVIEW = bool(get_setting(settings, "ENABLE_REVIEW", False))
    REVIEW_MODEL = str(get_setting(settings, "REVIEW_MODEL", ""))
    REVIEW_MAX_TOKENS = int(get_setting(settings, "REVIEW_MAX_TOKENS", 1200))
    REVIEW_MAX_ITEMS = int(get_setting(settings, "REVIEW_MAX_ITEMS", 0))
    REVIEW_LLM_RETRIES = int(get_setting(settings, "REVIEW_LLM_RETRIES", 2))
    REVIEW_DISABLE_LLM = bool(get_setting(settings, "REVIEW_DISABLE_LLM", False))
    REVIEW_FORCE = bool(get_setting(settings, "REVIEW_FORCE", False))
    ENABLE_HOLD_PIPELINE = bool(get_setting(settings, "ENABLE_HOLD_PIPELINE", False))

    parse_args()

    INPUT_PDF_DIR.mkdir(parents=True, exist_ok=True)
    OUTPUT_JSON_DIR.mkdir(parents=True, exist_ok=True)
    OUTPUT_JSON_NATURALIZED_DIR.mkdir(parents=True, exist_ok=True)
    OUTPUT_REVIEW_DIR.mkdir(parents=True, exist_ok=True)
    WORK_DIR.mkdir(parents=True, exist_ok=True)

    pdf_to_md, md_to_tex, tex_to_json = ensure_scripts_exist(PROJECT_ROOT)
    mode_input_dir = INPUT_PDF_DIR / "book"
    mode_input_dir.mkdir(parents=True, exist_ok=True)

    pdfs = sorted(mode_input_dir.rglob("*.pdf"))

    if ONLY_THESE_STEMS:
        raw_selectors = list(ONLY_THESE_STEMS)

        norm: List[str] = []
        for s in raw_selectors:
            t = s.strip().replace("\\", "/")
            if t.endswith(".pdf"):
                t = t[:-4]
            norm.append(t)

        def _matches(p: Path) -> bool:
            rel = p.relative_to(INPUT_PDF_DIR)
            rel_no_suffix_posix = rel.with_suffix("").as_posix()

            for sel in norm:
                if not sel:
                    continue
                sel_strip = sel.rstrip("/")

                if p.stem == sel_strip:
                    return True

                if rel_no_suffix_posix == sel_strip:
                    return True

                if rel_no_suffix_posix.startswith(sel_strip + "/"):
                    return True

            return False

        pdfs = [p for p in pdfs if _matches(p)]

    def _json_out_path(p: Path) -> Path:
        rel = p.relative_to(INPUT_PDF_DIR)
        return (OUTPUT_JSON_DIR / rel).with_suffix(".json")

    def _json_nat_out_path(p: Path) -> Path:
        rel = p.relative_to(INPUT_PDF_DIR)
        return (OUTPUT_JSON_NATURALIZED_DIR / rel).with_suffix(".json")

    def _review_out_path(p: Path) -> Path:
        rel = p.relative_to(INPUT_PDF_DIR)
        return (OUTPUT_REVIEW_DIR / rel).with_suffix(".json")

    if not OVERWRITE_JSON:
        def _needs_work(p: Path) -> bool:
            j1 = _json_out_path(p)
            if not json_complete(j1):
                return True
            if ENABLE_NATURALIZE:
                j2 = _json_nat_out_path(p)
                if NATURALIZE_FORCE or (not naturalized_complete(j2)):
                    return True
                if ENABLE_REVIEW:
                    j3 = _review_out_path(p)
                    if REVIEW_FORCE or (not review_complete(j3, j2)):
                        return True
            return False

        pdfs = [p for p in pdfs if _needs_work(p)]

    if not pdfs:
        print(f"No PDFs to process in: {mode_input_dir}")
        return

    print("Mode: book")
    print(f"Found {len(pdfs)} PDF(s) to process in {mode_input_dir}")
    naturalize_totals: Dict[str, int] = {
        "rows": 0,
        "llm_touched": 0,
        "ok": 0,
        "fallback": 0,
        "skipped": 0,
        "failed": 0,
    }
    for pdf in pdfs:
        print(f"\n=== Processing: {pdf.relative_to(INPUT_PDF_DIR).as_posix()} ===")
        out_json, nat_stats = process_one(
            pdf,
            pdf_to_md,
            md_to_tex,
            tex_to_json,
            input_pdf_dir=INPUT_PDF_DIR,
            output_json_dir=OUTPUT_JSON_DIR,
            work_dir=WORK_DIR,
        )
        print(f"[ok] JSON -> {out_json}")
        if nat_stats:
            for k in naturalize_totals:
                naturalize_totals[k] += int(nat_stats.get(k, 0))

    if ENABLE_NATURALIZE:
        print(
            "[naturalize-summary] "
            f"rows={naturalize_totals['rows']}, "
            f"llm_touched={naturalize_totals['llm_touched']}, "
            f"ok={naturalize_totals['ok']}, "
            f"fallback={naturalize_totals['fallback']}, "
            f"skipped={naturalize_totals['skipped']}, "
            f"failed={naturalize_totals['failed']}"
        )

    if ENABLE_HOLD_PIPELINE and ENABLE_REVIEW:
        hold_run_script = PROJECT_ROOT / "src" / "review" / "hold_run.py"
        if hold_run_script.exists():
            print("\n=== Running hold-repair pipeline ===")
            run_cmd([sys.executable, str(hold_run_script), "--hold-only"])
        else:
            print(f"[warn] hold_run.py not found: {hold_run_script}")

    print("\nALL DONE")


if __name__ == "__main__":
    main()
