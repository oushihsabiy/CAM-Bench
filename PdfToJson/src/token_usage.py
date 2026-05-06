#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Token-usage logging — real provider data only.

Main log  : work/token_usage/token_usage.jsonl   (real provider-reported usage ONLY)
Estimated : work/token_usage/token_usage_estimated.jsonl  (heuristic fallback, separate)

Every call_start is paired with call_end (real usage) or call_error.
Estimated token counts are NEVER written into the main log.
"""

from __future__ import annotations

import json
import os
import uuid
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Dict, Optional
import logging

logger = logging.getLogger(__name__)

_TZ_UTC = timezone.utc
_TZ_BEIJING = timezone(timedelta(hours=8))


# ---------------------------------------------------------------------------
# Usage extraction helpers
# ---------------------------------------------------------------------------

def _to_plain_dict(obj: Any) -> Dict[str, Any]:
    if obj is None:
        return {}
    if isinstance(obj, dict):
        return dict(obj)
    model_dump = getattr(obj, "model_dump", None)
    if callable(model_dump):
        try:
            v = model_dump()
            if isinstance(v, dict):
                return v
        except Exception:
            pass
    out: Dict[str, Any] = {}
    for k in (
        "prompt_tokens",
        "completion_tokens",
        "total_tokens",
        "input_tokens",
        "output_tokens",
        "input_cached_tokens",
        "output_cached_tokens",
        "reasoning_tokens",
    ):
        try:
            val = getattr(obj, k, None)
        except Exception:
            val = None
        if isinstance(val, (int, float)):
            out[k] = int(val)
    return out


def _extract_usage(response_or_usage: Any) -> Dict[str, Any]:
    if response_or_usage is None:
        return {}

    if isinstance(response_or_usage, dict) and "usage" in response_or_usage:
        usage_obj = response_or_usage["usage"]
    else:
        usage_obj = getattr(response_or_usage, "usage", None)
        if usage_obj is None:
            usage_obj = response_or_usage

    usage = _to_plain_dict(usage_obj)
    if not usage:
        return {}

    prompt_tokens = usage.get("prompt_tokens")
    if prompt_tokens is None:
        prompt_tokens = usage.get("input_tokens")

    completion_tokens = usage.get("completion_tokens")
    if completion_tokens is None:
        completion_tokens = usage.get("output_tokens")

    total_tokens = usage.get("total_tokens")
    if total_tokens is None and isinstance(prompt_tokens, int) and isinstance(completion_tokens, int):
        total_tokens = prompt_tokens + completion_tokens

    normalized: Dict[str, Any] = dict(usage)
    if isinstance(prompt_tokens, int):
        normalized["prompt_tokens"] = int(prompt_tokens)
    if isinstance(completion_tokens, int):
        normalized["completion_tokens"] = int(completion_tokens)
    if isinstance(total_tokens, int):
        normalized["total_tokens"] = int(total_tokens)
    return normalized


def _has_real_usage(usage: Dict[str, Any]) -> bool:
    return bool(usage) and int(usage.get("total_tokens", 0) or 0) > 0


def extract_base_url(client: Any) -> str:
    """Best-effort extraction of base_url from an OpenAI client object."""
    if client is None:
        return ""
    for attr in ("_base_url", "base_url"):
        val = getattr(client, attr, None)
        if val is not None:
            s = str(val).strip().rstrip("/")
            if s:
                return s
    return ""


# ---------------------------------------------------------------------------
# Path helpers
# ---------------------------------------------------------------------------

def _default_log_path(config_path: Optional[Path]) -> Path:
    if config_path is not None:
        return config_path.parent / "work" / "token_usage" / "token_usage.jsonl"
    return Path.cwd() / "work" / "token_usage" / "token_usage.jsonl"


def _estimated_log_path(config_path: Optional[Path]) -> Path:
    if config_path is not None:
        return config_path.parent / "work" / "token_usage" / "token_usage_estimated.jsonl"
    return Path.cwd() / "work" / "token_usage" / "token_usage_estimated.jsonl"


def resolve_log_path(config_path: Optional[Path], explicit_path: Optional[str] = None) -> Path:
    env_path = os.getenv("TOKEN_USAGE_LOG_PATH", "").strip()
    if explicit_path and str(explicit_path).strip():
        p = Path(str(explicit_path).strip()).expanduser()
    elif env_path:
        p = Path(env_path).expanduser()
    else:
        p = _default_log_path(config_path)
    if not p.is_absolute():
        base = config_path.parent if config_path is not None else Path.cwd()
        p = (base / p).resolve()
    return p


# ---------------------------------------------------------------------------
# Row writers
# ---------------------------------------------------------------------------

def _write_row(row: Dict[str, Any], *, config_path: Optional[Path],
               configured_log_path: Optional[str] = None) -> None:
    """Append a JSON row to the main real-usage log and flush."""
    log_path = resolve_log_path(config_path=config_path, explicit_path=configured_log_path)
    log_path.parent.mkdir(parents=True, exist_ok=True)
    try:
        with log_path.open("a", encoding="utf-8") as f:
            f.write(json.dumps(row, ensure_ascii=False) + "\n")
            f.flush()
    except Exception:
        pass
    _print_summary(row)


def _write_estimated_row(row: Dict[str, Any], *, config_path: Optional[Path]) -> None:
    """Append a JSON row to the separate estimated-usage log (never main)."""
    log_path = _estimated_log_path(config_path)
    log_path.parent.mkdir(parents=True, exist_ok=True)
    try:
        with log_path.open("a", encoding="utf-8") as f:
            f.write(json.dumps(row, ensure_ascii=False) + "\n")
            f.flush()
    except Exception:
        pass


def _print_summary(row: Dict[str, Any]) -> None:
    """Real-time terminal feedback."""
    event = row.get("event", "")
    model = row.get("model", "")
    total = row.get("total_tokens", 0)
    call_type = row.get("call_type", "")
    source = row.get("source", "")
    tag = f" [{source}]" if source else ""
    if event == "call_end" and total:
        logger.debug(f"[token_usage] {event} model={model} type={call_type}{tag} tokens={total}")
    elif event == "call_error":
        reason = ""
        ex = row.get("extra")
        if isinstance(ex, dict):
            reason = ex.get("reason", ex.get("error", ""))
        logger.debug(f"[token_usage] {event} model={model} type={call_type}{tag} reason={reason}")
    elif event == "call_start":
        logger.debug(f"[token_usage] {event} model={model} type={call_type}{tag}")


# ---------------------------------------------------------------------------
# Base row builder
# ---------------------------------------------------------------------------

def _new_base_row(*, endpoint: str, model: str, usage_source: str, estimated: bool = False,
                   base_url: str = "", source: str = "") -> Dict[str, Any]:
    now_utc = datetime.now(_TZ_UTC)
    now_beijing = datetime.now(_TZ_BEIJING)
    row: Dict[str, Any] = {
        "schema_version": 2,
        "ts_utc": now_utc.isoformat(timespec="seconds"),
        "timestamp_beijing": now_beijing.isoformat(timespec="seconds"),
        "endpoint": endpoint,
        "model": model,
        "base_url": base_url,
        "usage_source": usage_source,
        "source": source,
    }
    if estimated:
        row["estimated"] = True
    return row


# ---------------------------------------------------------------------------
# Public logging API
# ---------------------------------------------------------------------------

def log_openai_usage(
    response_or_usage: Any,
    *,
    endpoint: str,
    model: str,
    usage_source: str = "api",
    call_id: str = "",
    call_type: str = "",
    item_label: str = "",
    base_url: str = "",
    source: str = "",
    config_path: Optional[Path] = None,
    configured_log_path: Optional[str] = None,
    extra: Optional[Dict[str, Any]] = None,
) -> bool:
    """Log real provider-reported usage.  Returns True if real usage was logged."""
    usage = _extract_usage(response_or_usage)
    if not _has_real_usage(usage):
        return False

    row: Dict[str, Any] = {
        **_new_base_row(endpoint=endpoint, model=model, usage_source=usage_source,
                        base_url=base_url, source=source),
        "event": "call_end",
        "prompt_tokens": usage.get("prompt_tokens", 0),
        "completion_tokens": usage.get("completion_tokens", 0),
        "total_tokens": usage.get("total_tokens", 0),
    }
    if call_id:
        row["call_id"] = call_id
    if call_type:
        row["call_type"] = call_type
    if item_label:
        row["item_label"] = item_label
    if isinstance(extra, dict) and extra:
        row["extra"] = extra
    _write_row(row, config_path=config_path, configured_log_path=configured_log_path)
    return True


def _write_estimated_to_separate_log(
    *,
    endpoint: str,
    model: str,
    prompt_text: str,
    output_text: str,
    call_id: str = "",
    call_type: str = "",
    base_url: str = "",
    source: str = "",
    config_path: Optional[Path] = None,
) -> None:
    """Write heuristic token estimate to the separate estimated-usage log ONLY."""
    p_chars = len(prompt_text or "")
    o_chars = len(output_text or "")
    if p_chars == 0 and o_chars == 0:
        return
    prompt_tokens = max(1, (p_chars + 3) // 4) if p_chars else 0
    completion_tokens = max(1, (o_chars + 3) // 4) if o_chars else 0
    total_tokens = prompt_tokens + completion_tokens

    row: Dict[str, Any] = {
        **_new_base_row(endpoint=endpoint, model=model, usage_source="estimated",
                        estimated=True, base_url=base_url, source=source),
        "event": "call_end",
        "prompt_tokens": prompt_tokens,
        "completion_tokens": completion_tokens,
        "total_tokens": total_tokens,
    }
    if call_id:
        row["call_id"] = call_id
    if call_type:
        row["call_type"] = call_type
    _write_estimated_row(row, config_path=config_path)


def log_estimated_usage(
    *,
    endpoint: str,
    model: str,
    prompt_text: str,
    output_text: str,
    call_id: str = "",
    call_type: str = "",
    item_label: str = "",
    base_url: str = "",
    source: str = "",
    config_path: Optional[Path] = None,
    configured_log_path: Optional[str] = None,
    extra: Optional[Dict[str, Any]] = None,
) -> None:
    """Write estimated usage to the SEPARATE estimated log only (backward-compat wrapper)."""
    _write_estimated_to_separate_log(
        endpoint=endpoint,
        model=model,
        prompt_text=prompt_text,
        output_text=output_text,
        call_id=call_id,
        call_type=call_type,
        base_url=base_url,
        source=source,
        config_path=config_path,
    )


def log_usage_with_fallback(
    response_or_usage: Any,
    *,
    endpoint: str,
    model: str,
    prompt_text: str,
    output_text: str,
    call_id: str = "",
    call_type: str = "",
    item_label: str = "",
    usage_source_if_real: str = "api",
    base_url: str = "",
    source: str = "",
    config_path: Optional[Path] = None,
    configured_log_path: Optional[str] = None,
    extra: Optional[Dict[str, Any]] = None,
) -> None:
    """Log real usage if available; otherwise write call_error to main log.

    REAL usage → main log (call_end with provider tokens).
    MISSING usage → main log gets call_error; estimated log gets estimate.
    Estimated token counts are NEVER written into the main log.
    """
    usage = _extract_usage(response_or_usage)
    if _has_real_usage(usage):
        log_openai_usage(
            usage,
            endpoint=endpoint,
            model=model,
            usage_source=usage_source_if_real,
            call_id=call_id,
            call_type=call_type,
            item_label=item_label,
            base_url=base_url,
            source=source,
            config_path=config_path,
            configured_log_path=configured_log_path,
            extra=extra,
        )
        return

    # --- Provider did NOT return usage: write call_error to main log ---
    error_extra: Dict[str, Any] = dict(extra or {})
    error_extra["reason"] = "missing_usage_from_provider"
    log_call_error(
        endpoint=endpoint,
        model=model,
        call_id=call_id,
        call_type=call_type,
        item_label=item_label,
        base_url=base_url,
        source=source,
        config_path=config_path,
        configured_log_path=configured_log_path,
        extra=error_extra,
    )

    # --- Write estimate to SEPARATE file (never to main log) ---
    _write_estimated_to_separate_log(
        endpoint=endpoint,
        model=model,
        prompt_text=prompt_text,
        output_text=output_text,
        call_id=call_id,
        call_type=call_type,
        base_url=base_url,
        source=source,
        config_path=config_path,
    )


def log_call_started(
    *,
    endpoint: str,
    model: str,
    call_type: str = "",
    item_label: str = "",
    base_url: str = "",
    source: str = "",
    config_path: Optional[Path] = None,
    configured_log_path: Optional[str] = None,
    extra: Optional[Dict[str, Any]] = None,
) -> str:
    call_id = uuid.uuid4().hex[:12]
    row: Dict[str, Any] = {
        **_new_base_row(endpoint=endpoint, model=model, usage_source="pending",
                        base_url=base_url, source=source),
        "event": "call_start",
        "call_id": call_id,
        "prompt_tokens": 0,
        "completion_tokens": 0,
        "total_tokens": 0,
    }
    if call_type:
        row["call_type"] = call_type
    if item_label:
        row["item_label"] = item_label
    if isinstance(extra, dict) and extra:
        row["extra"] = extra
    _write_row(row, config_path=config_path, configured_log_path=configured_log_path)
    return call_id


def log_call_error(
    *,
    endpoint: str,
    model: str,
    call_id: str = "",
    call_type: str = "",
    item_label: str = "",
    base_url: str = "",
    source: str = "",
    config_path: Optional[Path] = None,
    configured_log_path: Optional[str] = None,
    extra: Optional[Dict[str, Any]] = None,
) -> None:
    row: Dict[str, Any] = {
        **_new_base_row(endpoint=endpoint, model=model, usage_source="error",
                        base_url=base_url, source=source),
        "event": "call_error",
        "prompt_tokens": 0,
        "completion_tokens": 0,
        "total_tokens": 0,
    }
    if call_id:
        row["call_id"] = call_id
    if call_type:
        row["call_type"] = call_type
    if item_label:
        row["item_label"] = item_label
    if isinstance(extra, dict) and extra:
        row["extra"] = extra
    _write_row(row, config_path=config_path, configured_log_path=configured_log_path)
