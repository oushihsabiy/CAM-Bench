#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""Review one JSON block with LLM according to src/prompts/review*.md."""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

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

_ALLOWED_STATUS = {"accept", "revise", "hold"}


def _safe_json_load(s: str) -> Optional[Dict[str, Any]]:
    try:
        v = json.loads(s)
    except Exception:
        return None
    return v if isinstance(v, dict) else None


def _extract_first_json_object(text: str) -> Optional[Dict[str, Any]]:
    s = (text or "").strip()
    if not s:
        return None
    direct = _safe_json_load(s)
    if direct is not None:
        return direct
    l = s.find("{")
    r = s.rfind("}")
    if l >= 0 and r > l:
        return _safe_json_load(s[l : r + 1])
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


def _find_prompt_path(prompt_path: str = "") -> Path:
    if str(prompt_path or "").strip():
        p = Path(str(prompt_path)).expanduser().resolve()
        if not p.exists():
            raise FileNotFoundError(f"Review prompt not found: {p}")
        return p
    p = _SRC_ROOT / "prompts" / "review.md"
    if not p.exists():
        raise FileNotFoundError(f"Review prompt not found: {p}")
    return p


def load_review_prompt(prompt_path: str = "") -> str:
    return _find_prompt_path(prompt_path).read_text(encoding="utf-8").strip()


def _clear_proxy_env() -> None:
    for k in ("http_proxy", "https_proxy", "HTTP_PROXY", "HTTPS_PROXY", "ALL_PROXY", "all_proxy"):
        os.environ.pop(k, None)


def _make_review_input(record: Dict[str, Any]) -> Dict[str, Any]:
    return {
        "source_idx": str(record.get("source_idx") or "").strip(),
        "source": str(record.get("source") or "").strip(),
        "problem": str(record.get("problem") or "").strip(),
        "problem_clean": str(record.get("problem_clean") or "").strip(),
        "problem_standardized_math": str(record.get("problem_standardized_math") or "").strip(),
        "problem_finally": str(record.get("problem_finally") or "").strip(),
    }


def _build_prompt(template: str, payload: Dict[str, Any]) -> str:
    return template + "\n\nInput JSON:\n" + json.dumps(payload, ensure_ascii=False)


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
        call_type="review",
        item_label=source_idx,
        base_url=base_url,
        source="src/review/review.py",
        config_path=find_config_json(),
        extra={"script": "src/review/review.py"},
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
            call_type="review",
            item_label=source_idx,
            usage_source_if_real="api_stream",
            base_url=base_url,
            source="src/review/review.py",
            config_path=find_config_json(),
            extra={"script": "src/review/review.py", "reason": "stream_review"},
        )
        return out
    except Exception as e:
        if _is_max_tokens_unsupported_error(e):
            call_id_2 = log_call_started(
                endpoint="chat.completions",
                model=model,
                call_type="review",
                item_label=source_idx,
                base_url=base_url,
                source="src/review/review.py",
                config_path=find_config_json(),
                extra={"script": "src/review/review.py", "retry": "max_completion_tokens"},
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
                    call_type="review",
                    item_label=source_idx,
                    usage_source_if_real="api_stream",
                    base_url=base_url,
                    source="src/review/review.py",
                    config_path=find_config_json(),
                    extra={"script": "src/review/review.py", "reason": "stream_review"},
                )
                return out
            except Exception as ee:
                log_call_error(
                    endpoint="chat.completions",
                    model=model,
                    call_id=call_id_2,
                    call_type="review",
                    item_label=source_idx,
                    base_url=base_url,
                    source="src/review/review.py",
                    config_path=find_config_json(),
                    extra={"script": "src/review/review.py", "error": f"{ee.__class__.__name__}: {ee}"},
                )
                raise
        log_call_error(
            endpoint="chat.completions",
            model=model,
            call_id=call_id,
            call_type="review",
            item_label=source_idx,
            base_url=base_url,
            source="src/review/review.py",
            config_path=find_config_json(),
            extra={"script": "src/review/review.py", "error": f"{e.__class__.__name__}: {e}"},
        )
        raise


def _fallback_report(record: Dict[str, Any], reason: str) -> Dict[str, Any]:
    source_idx = str(record.get("source_idx") or "").strip()
    source = str(record.get("source") or "").strip()
    msg = (reason or "review_failed").strip()
    return {
        "source_idx": source_idx,
        "source": source,
        "overall_status": "hold",
        "reason": f"Review not completed: {msg}.",
        "issue_type": {
            "missing_assumption": {"value": False, "reason": f"Review not completed: {msg}.", "suggestion_fix": "Regenerate review."},
            "task_drift": {"value": False, "reason": f"Review not completed: {msg}.", "suggestion_fix": "Regenerate review."},
            "missing_dependency": {"value": False, "reason": f"Review not completed: {msg}.", "suggestion_fix": "Regenerate review."},
            "missing_def": {"value": False, "reason": f"Review not completed: {msg}.", "suggestion_fix": "Regenerate review."},
        },
        "confidence": 0.0,
    }


def _to_bool(v: Any) -> bool:
    if isinstance(v, bool):
        return v
    if isinstance(v, (int, float)):
        return bool(v)
    s = str(v or "").strip().lower()
    if s in {"true", "1", "yes", "y"}:
        return True
    return False


def _normalize_status(v: Any) -> str:
    s = str(v or "").strip().lower()
    if s not in _ALLOWED_STATUS:
        return "hold"
    return s


def _is_parse_error_reason(reason: str) -> bool:
    rr = str(reason or "").strip().lower()
    if not rr:
        return False
    patterns = [
        "review not completed",
        "review_failed",
        "model_output_not_json_object",
        "llm_disabled_or_api_key_missing",
    ]
    return any(p in rr for p in patterns)


def _derive_hold_reason_type(out: Dict[str, Any]) -> str:
    status = str(out.get("overall_status") or "").strip().lower()
    if status != "hold":
        return ""
    issue_type = out.get("issue_type") if isinstance(out.get("issue_type"), dict) else {}
    miss_dep = bool(((issue_type.get("missing_dependency") or {}).get("value")))
    if miss_dep:
        return "missing_dependency"
    conf = out.get("confidence", 0.0)
    try:
        c = float(conf)
    except Exception:
        c = 0.0
    if c <= 0.0 or _is_parse_error_reason(str(out.get("reason") or "")):
        return "parse_error"
    return "unsuitable_lean"


def _derive_overall_reason(status: str, issue_type: Dict[str, Any], raw_reason: str) -> str:
    rr = (raw_reason or "").strip()
    if rr:
        return rr
    missing_assumption = bool(((issue_type.get("missing_assumption") or {}).get("value")))
    task_drift = bool(((issue_type.get("task_drift") or {}).get("value")))
    missing_dependency = bool(((issue_type.get("missing_dependency") or {}).get("value")))
    missing_def = bool(((issue_type.get("missing_def") or {}).get("value")))
    if status == "accept":
        return "No blocking issue found; assumptions/task are preserved and the statement is suitable for Lean formalization."
    if status == "revise":
        flags = []
        if missing_assumption:
            flags.append("missing_assumption")
        if task_drift:
            flags.append("task_drift")
        if missing_def:
            flags.append("missing_def")
        if not flags:
            flags.append("content_revision_needed")
        return "Revision required due to: " + ", ".join(flags) + "."
    flags = []
    if missing_dependency:
        flags.append("missing_dependency")
    if not flags:
        flags.append("formalizability_or_dependency_hold")
    return "Hold required due to: " + ", ".join(flags) + "."


def _normalize_report(record: Dict[str, Any], report: Dict[str, Any]) -> Dict[str, Any]:
    source_idx = str(report.get("source_idx") or record.get("source_idx") or "").strip()
    source = str(report.get("source") or record.get("source") or "").strip()
    overall_status = _normalize_status(report.get("overall_status", report.get("overall_type")))

    issue_obj = report.get("issue_type")
    if not isinstance(issue_obj, dict):
        issue_obj = {}

    def _norm_issue(name: str) -> Dict[str, Any]:
        raw = issue_obj.get(name)
        if not isinstance(raw, dict):
            raw = {}
        value = _to_bool(raw.get("value"))
        reason = str(raw.get("reason") or "").strip() or "No issue details provided."
        suggestion_fix = str(raw.get("suggestion_fix") or "").strip() or ("No fix needed." if not value else "Please revise.")
        return {"value": value, "reason": reason, "suggestion_fix": suggestion_fix}

    out = {
        "source_idx": source_idx,
        "source": source,
        "overall_status": overall_status,
        "reason": "",
        "issue_type": {
            "missing_assumption": _norm_issue("missing_assumption"),
            "task_drift": _norm_issue("task_drift"),
            "missing_dependency": _norm_issue("missing_dependency"),
            "missing_def": _norm_issue("missing_def"),
        },
        "confidence": report.get("confidence", 0.0),
    }
    out["reason"] = _derive_overall_reason(
        out["overall_status"],
        out["issue_type"],
        str(report.get("reason") or "").strip(),
    )
    try:
        out["confidence"] = float(out["confidence"])
    except Exception:
        out["confidence"] = 0.0
    if out["confidence"] < 0:
        out["confidence"] = 0.0
    if out["confidence"] > 1:
        out["confidence"] = 1.0
    if out["overall_status"] == "hold":
        out["hold_reason_type"] = _derive_hold_reason_type(out)
    return out


def review_one(
    record: Dict[str, Any],
    *,
    client: Optional[OpenAI],
    model: str,
    max_tokens: int,
    prompt_template: str,
    llm_retries: int = 2,
) -> Dict[str, Any]:
    source_idx = str(record.get("source_idx") or "").strip()
    payload = _make_review_input(record)
    prompt = _build_prompt(prompt_template, payload)

    if client is None:
        return _normalize_report(record, _fallback_report(record, "llm_disabled_or_api_key_missing"))

    last_err: Optional[str] = None
    attempts = max(1, int(llm_retries))
    for _ in range(attempts):
        try:
            raw = _chat_completion_text(
                client,
                model=model,
                prompt=prompt,
                max_tokens=int(max_tokens),
                source_idx=source_idx,
            )
            obj = _extract_first_json_object(raw)
            if obj is None:
                last_err = "model_output_not_json_object"
                continue
            if not str(obj.get("source_idx") or "").strip():
                obj["source_idx"] = source_idx
            if not str(obj.get("source") or "").strip():
                obj["source"] = str(record.get("source") or "").strip()
            return _normalize_report(record, obj)
        except Exception as e:
            last_err = f"{e.__class__.__name__}: {e}"

    return _normalize_report(record, _fallback_report(record, last_err or "review_failed"))


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description="Review one JSON record with LLM.")
    ap.add_argument("in_json", type=str, help="Input record JSON path (dict)")
    ap.add_argument("--out-json", type=str, default="", help="Optional output JSON file path")
    ap.add_argument("--model", type=str, default="", help="LLM model override")
    ap.add_argument("--max-tokens", type=int, default=1200, help="Max output tokens")
    ap.add_argument("--llm-retries", type=int, default=2, help="Max retries per record")
    ap.add_argument("--disable-llm", action="store_true", help="Do not call LLM")
    ap.add_argument(
        "--prompt-path",
        type=str,
        default="",
        help="Review prompt path override (default: src/prompts/review.md)",
    )
    return ap.parse_args()


def main() -> None:
    args = parse_args()
    in_path = Path(args.in_json).expanduser().resolve()
    row = json.loads(in_path.read_text(encoding="utf-8"))
    if not isinstance(row, dict):
        raise ValueError("in_json must be a JSON object (single record).")

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
        call_type="review",
        base_url=base_url,
        source="src/review/review.py",
        config_path=find_config_json(),
        extra={"script": "src/review/review.py", "reason": "run_start"},
    )

    use_llm = (not bool(args.disable_llm)) and bool(api_key)
    client: Optional[OpenAI] = None
    if use_llm:
        if base_url:
            client = OpenAI(api_key=api_key, base_url=base_url, timeout=180)
        else:
            client = OpenAI(api_key=api_key, timeout=180)

    template = load_review_prompt(str(args.prompt_path or ""))
    report = review_one(
        row,
        client=client,
        model=model,
        max_tokens=int(args.max_tokens),
        prompt_template=template,
        llm_retries=int(args.llm_retries),
    )

    s = json.dumps(report, ensure_ascii=False, indent=2)
    if args.out_json:
        out_path = Path(args.out_json).expanduser().resolve()
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(s + "\n", encoding="utf-8")
    else:
        print(s)


if __name__ == "__main__":
    main()
