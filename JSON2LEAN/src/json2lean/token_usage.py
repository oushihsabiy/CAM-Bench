"""Token usage logging for API calls."""

from __future__ import annotations

import json
import os
from datetime import datetime
from pathlib import Path
from typing import Any, Dict


def _truthy_env(value: str | None) -> bool:
    if value is None:
        return False
    return value.strip().lower() not in {"", "0", "false", "no", "off"}


def _resolve_realtime_log_file(log_dir: str | Path | None = None) -> Path:
    env_file = os.environ.get("JSON2LEAN_REALTIME_LOG_FILE", "").strip()
    if env_file:
        return Path(env_file)

    env_dir = os.environ.get("JSON2LEAN_TOKEN_LOG_DIR", "").strip()
    root = Path(log_dir) if log_dir is not None else Path(env_dir or "logs")
    return root / "token_usage.jsonl"


def log_realtime_usage(
    model: str = "",
    base_url: str = "",
    call_type: str = "",
    exercise_label: str = "",
    usage: Dict[str, int] | None = None,
    usage_source: str = "",
    log_dir: str | Path | None = None,
    enabled: bool | None = None,
    **kwargs: Any,
) -> None:
    """Log token usage to a JSON Lines file if enabled.

    Set JSON2LEAN_REALTIME_LOG environment variable, pass ``enabled=True``,
    or pass a ``log_dir`` to enable logging.
    Each call appends a record with timestamp, model, call type, and token counts.
    
    Args:
        model: LLM model name
        base_url: API base URL
        call_type: Type of call (e.g., "translate", "review")
        exercise_label: Exercise identifier
        usage: Dict with 'prompt_tokens', 'completion_tokens', 'total_tokens'
        usage_source: Source of token counts (e.g., "counted", "estimated")
        log_dir: Directory for token_usage.jsonl
        enabled: Explicit logging switch. Defaults to env/log_dir behavior
        **kwargs: Additional fields to log
    """
    if enabled is None:
        enabled = (
            log_dir is not None
            or _truthy_env(os.environ.get("JSON2LEAN_REALTIME_LOG"))
            or bool(os.environ.get("JSON2LEAN_REALTIME_LOG_FILE", "").strip())
            or bool(os.environ.get("JSON2LEAN_TOKEN_LOG_DIR", "").strip())
        )
    if not enabled:
        return

    log_file = _resolve_realtime_log_file(log_dir)
    
    record = {
        "timestamp": datetime.now().isoformat(),
        "model": model,
        "base_url": base_url,
        "call_type": call_type,
        "exercise_label": exercise_label,
        "usage_source": usage_source,
    }
    if usage:
        record.update(usage)
    record.update(kwargs)
    
    try:
        log_file.parent.mkdir(parents=True, exist_ok=True)
        with open(log_file, "a", encoding="utf-8") as f:
            f.write(json.dumps(record, ensure_ascii=False) + "\n")
    except Exception:
        pass  # Silently fail if logging is not possible
