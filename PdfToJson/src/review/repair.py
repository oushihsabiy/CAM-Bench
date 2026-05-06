#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""Repair revise JSON rows one-by-one with LLM and write progressive outputs."""

from __future__ import annotations

import argparse
import json
import os
import sys
from copy import deepcopy
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple

from openai import OpenAI

_SRC_ROOT = Path(__file__).resolve().parents[1]
if str(_SRC_ROOT) not in sys.path:
    sys.path.append(str(_SRC_ROOT))

from token_usage import (
    extract_base_url,
    log_call_error,
    log_call_started,
    log_estimated_usage,
    log_usage_with_fallback,
)


ALLOWED_FIELDS = [
    "index",
    "problem",
    "problem_clean",
    "proof",
    "direct_answer",
    "题目类型",
    "预估难度",
    "source",
    "source_idx",
    "problem_with_context",
    "problem_standardized_math",
    "problem_finally",
]


def _clear_proxy_env() -> None:
    for k in ("http_proxy", "https_proxy", "HTTP_PROXY", "HTTPS_PROXY", "ALL_PROXY", "all_proxy"):
        os.environ.pop(k, None)


def find_config_json() -> Path:
    p = Path.cwd() / "config.json"
    if p.exists():
        return p.resolve()
    here = Path(__file__).resolve().parent
    for d in [here] + list(here.parents):
        q = d / "config.json"
        if q.exists():
            return q.resolve()
    raise FileNotFoundError("config.json not found (checked CWD and script parents).")


def load_config() -> Dict[str, Any]:
    cfg_path = find_config_json()
    data = json.loads(cfg_path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"{cfg_path} must contain a JSON object.")
    return data


def _load_prompt(prompt_path: str = "") -> str:
    if str(prompt_path or "").strip():
        p = Path(str(prompt_path)).expanduser().resolve()
        if not p.exists():
            raise FileNotFoundError(f"Repair prompt not found: {p}")
        return p.read_text(encoding="utf-8").strip()
    p = _SRC_ROOT / "prompts" / "repair.md"
    if not p.exists():
        raise FileNotFoundError(f"Repair prompt not found: {p}")
    return p.read_text(encoding="utf-8").strip()


def _iter_json_files(in_path: Path) -> Iterable[Path]:
    if in_path.is_file() and in_path.suffix.lower() == ".json":
        yield in_path
        return
    if in_path.is_dir():
        for p in sorted(in_path.rglob("*.json")):
            if p.is_file():
                yield p


def _load_list(path: Path) -> List[Dict[str, Any]]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, list):
        raise ValueError(f"Expected JSON list: {path}")
    return [x for x in obj if isinstance(x, dict)]


def _extract_first_json_object(text: str) -> Optional[Dict[str, Any]]:
    s = (text or "").strip()
    if not s:
        return None
    try:
        v = json.loads(s)
        if isinstance(v, dict):
            return v
    except Exception:
        pass
    l = s.find("{")
    r = s.rfind("}")
    if l >= 0 and r > l:
        try:
            v = json.loads(s[l : r + 1])
            if isinstance(v, dict):
                return v
        except Exception:
            return None
    return None


def _collect_stream_text(stream_obj: Any) -> Tuple[str, Optional[Any]]:
    parts: List[str] = []
    stream_usage: Optional[Any] = None
    try:
        for chunk in stream_obj:
            chunk_usage = getattr(chunk, "usage", None)
            if chunk_usage is not None:
                stream_usage = chunk_usage
            choices = getattr(chunk, "choices", None) or []
            if not choices:
                continue
            delta = getattr(choices[0], "delta", None)
            if delta is None:
                continue
            content = getattr(delta, "content", None)
            if isinstance(content, str):
                parts.append(content)
            elif isinstance(content, list):
                for it in content:
                    if isinstance(it, dict):
                        t = it.get("text") or it.get("content") or ""
                    else:
                        t = getattr(it, "text", "") or getattr(it, "content", "") or ""
                    if isinstance(t, str) and t:
                        parts.append(t)
    finally:
        close_fn = getattr(stream_obj, "close", None)
        if callable(close_fn):
            try:
                close_fn()
            except Exception:
                pass
    return "".join(parts).strip(), stream_usage


def _is_max_tokens_unsupported_error(err: Exception) -> bool:
    msg = str(err or "").lower()
    return "unsupported parameter" in msg and "max_tokens" in msg and "max_completion_tokens" in msg


def _chat_completion_text(
    client: OpenAI,
    *,
    model: str,
    prompt: str,
    max_tokens: int,
    source_idx: str,
) -> str:
    _clear_proxy_env()
    base_url = extract_base_url(client)
    kwargs = {
        "model": model,
        "messages": [{"role": "user", "content": prompt}],
        "temperature": 0.0,
        "top_p": 1.0,
        "max_tokens": max_tokens,
    }

    def _with_completion_tokens(base: Dict[str, Any]) -> Dict[str, Any]:
        k = dict(base)
        if "max_tokens" in k:
            k.pop("max_tokens", None)
            k["max_completion_tokens"] = max_tokens
        return k

    call_id = log_call_started(
        endpoint="chat.completions",
        model=model,
        call_type="repair",
        item_label=source_idx,
        base_url=base_url,
        source="src/review/repair.py",
        config_path=find_config_json(),
        extra={"script": "src/review/repair.py"},
    )
    try:
        stream_obj = client.chat.completions.create(stream=True, stream_options={"include_usage": True}, **kwargs)
        out, stream_usage = _collect_stream_text(stream_obj)
        log_usage_with_fallback(
            stream_usage,
            endpoint="chat.completions",
            model=model,
            prompt_text=prompt,
            output_text=out,
            call_id=call_id,
            call_type="repair",
            item_label=source_idx,
            usage_source_if_real="api_stream",
            base_url=base_url,
            source="src/review/repair.py",
            config_path=find_config_json(),
            extra={"script": "src/review/repair.py", "reason": "stream_repair"},
        )
        return out
    except Exception as e:
        if _is_max_tokens_unsupported_error(e):
            call_id_2 = log_call_started(
                endpoint="chat.completions",
                model=model,
                call_type="repair",
                item_label=source_idx,
                base_url=base_url,
                source="src/review/repair.py",
                config_path=find_config_json(),
                extra={"script": "src/review/repair.py", "retry": "max_completion_tokens"},
            )
            try:
                stream_obj = client.chat.completions.create(
                    stream=True,
                    stream_options={"include_usage": True},
                    **_with_completion_tokens(kwargs),
                )
                out, stream_usage = _collect_stream_text(stream_obj)
                log_usage_with_fallback(
                    stream_usage,
                    endpoint="chat.completions",
                    model=model,
                    prompt_text=prompt,
                    output_text=out,
                    call_id=call_id_2,
                    call_type="repair",
                    item_label=source_idx,
                    usage_source_if_real="api_stream",
                    base_url=base_url,
                    source="src/review/repair.py",
                    config_path=find_config_json(),
                    extra={"script": "src/review/repair.py", "reason": "stream_repair"},
                )
                return out
            except Exception as ee:
                log_call_error(
                    endpoint="chat.completions",
                    model=model,
                    call_id=call_id_2,
                    call_type="repair",
                    item_label=source_idx,
                    base_url=base_url,
                    source="src/review/repair.py",
                    config_path=find_config_json(),
                    extra={"script": "src/review/repair.py", "error": f"{ee.__class__.__name__}: {ee}"},
                )
                raise
        log_call_error(
            endpoint="chat.completions",
            model=model,
            call_id=call_id,
            call_type="repair",
            item_label=source_idx,
            base_url=base_url,
            source="src/review/repair.py",
            config_path=find_config_json(),
            extra={"script": "src/review/repair.py", "error": f"{e.__class__.__name__}: {e}"},
        )
        raise


def _build_prompt(template: str, row: Dict[str, Any]) -> str:
    return template + "\n\nInput JSON:\n" + json.dumps(row, ensure_ascii=False)


def _build_repaired_row(original: Dict[str, Any], model_obj: Optional[Dict[str, Any]]) -> Dict[str, Any]:
    out: Dict[str, Any] = {}
    for k in ALLOWED_FIELDS:
        if k == "problem_finally":
            continue
        out[k] = deepcopy(original.get(k))

    repaired_pf = None
    if isinstance(model_obj, dict):
        repaired_pf = model_obj.get("problem_finally")
    if repaired_pf is None:
        repaired_pf = original.get("problem_finally")
    out["problem_finally"] = repaired_pf
    return out


def _reindex_rows(rows: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    out: List[Dict[str, Any]] = []
    for i, row in enumerate(rows, start=1):
        r = dict(row)
        r["index"] = i
        out.append(r)
    return out


def _derive_out_path(in_file: Path, in_root: Path, out_root: Path) -> Path:
    rel = in_file.resolve().relative_to(in_root.resolve())
    return out_root / rel


def _write_progressive(path: Path, rows: List[Dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(rows, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description="Repair revise rows with LLM.")
    ap.add_argument("in_path", type=str, nargs="?", default="output_review/revise/book", help="Input file or root")
    ap.add_argument("out_root", type=str, nargs="?", default="output_review/revise/rewrite", help="Output root")
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
        help="Repair prompt path override (default: src/prompts/repair.md)",
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
        call_type="repair",
        base_url=base_url,
        source="src/review/repair.py",
        config_path=find_config_json(),
        extra={"script": "src/review/repair.py", "reason": "run_start"},
    )

    use_llm = (not bool(args.disable_llm)) and bool(api_key)
    client: Optional[OpenAI] = None
    if use_llm:
        if base_url:
            client = OpenAI(api_key=api_key, base_url=base_url, timeout=180)
        else:
            client = OpenAI(api_key=api_key, timeout=180)
    else:
        why = "disable-llm flag" if bool(args.disable_llm) else "missing api_key"
        print(f"[repair] llm disabled: {why}", flush=True)

    template = _load_prompt(str(args.prompt_path or ""))
    files = list(_iter_json_files(in_path))
    if not files:
        print(f"No JSON files found under {in_path}")
        return

    if args.input_root:
        input_root = Path(args.input_root).expanduser().resolve()
    else:
        input_root = in_path if in_path.is_dir() else in_path.parent

    llm_budget = max(0, int(args.max_items))
    for in_file in files:
        rows = _load_list(in_file)
        out_path = _derive_out_path(in_file, input_root, out_root)
        if len(rows) == 0:
            _write_progressive(out_path, [])
            print(f"[repair][skip-empty] {in_file} -> {out_path} (0/0)", flush=True)
            continue

        done_rows: List[Dict[str, Any]] = []
        if out_path.exists() and not bool(args.force):
            try:
                prev = _load_list(out_path)
            except Exception:
                prev = []
            if len(prev) >= len(rows):
                print(f"[repair][skip] {in_file} -> {out_path} ({len(rows)}/{len(rows)})", flush=True)
                continue
            done_rows = prev
        elif bool(args.force):
            _write_progressive(out_path, [])

        start_idx = len(done_rows)
        llm_used = 0
        for i, row in enumerate(rows[start_idx:], start=start_idx + 1):
            source_idx = str(row.get("source_idx") or f"row{i}").strip()
            model_obj: Optional[Dict[str, Any]] = None
            can_use_llm = use_llm and (llm_budget == 0 or llm_used < llm_budget)
            if can_use_llm:
                llm_used += 1
                prompt = _build_prompt(template, row)
                last_err: Optional[str] = None
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
                        last_err = "model_output_not_json_object"
                    except Exception as e:
                        last_err = f"{e.__class__.__name__}: {e}"
                if model_obj is None and last_err:
                    # fallback to original problem_finally when repair call fails
                    pass

            repaired = _build_repaired_row(row, model_obj)
            done_rows.append(repaired)
            done_rows = _reindex_rows(done_rows)
            _write_progressive(out_path, done_rows)
            print(f"[repair][{i}/{len(rows)}] {source_idx}", flush=True)


if __name__ == "__main__":
    main()
