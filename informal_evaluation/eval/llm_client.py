#!/usr/bin/env python3
"""OpenAI-compatible chat completion client used by informal evaluation."""

from __future__ import annotations

import json
import urllib.error
import urllib.request
from dataclasses import dataclass


MAX_TOKENS_PER_CALL = 1_000_000


@dataclass
class ModelConfig:
    model: str
    base_url: str
    api_key: str = "EMPTY"
    temperature: float = 0.6
    max_tokens: int = 4096
    stream: bool = False

    def __post_init__(self) -> None:
        self.max_tokens = min(int(self.max_tokens), MAX_TOKENS_PER_CALL)


@dataclass
class Usage:
    prompt_tokens: int = 0
    completion_tokens: int = 0
    total_tokens: int = 0


def _parse_usage(obj: dict | None) -> Usage:
    if not obj:
        return Usage()
    prompt = int(obj.get("prompt_tokens", 0) or 0)
    completion = int(obj.get("completion_tokens", 0) or 0)
    total = int(obj.get("total_tokens", 0) or 0) or prompt + completion
    return Usage(prompt_tokens=prompt, completion_tokens=completion, total_tokens=total)


def generate_with_usage(
    messages: list[dict[str, str]],
    cfg: ModelConfig,
    *,
    timeout: float | None = None,
) -> tuple[str, Usage]:
    """Call an OpenAI-compatible chat completion endpoint."""
    url = f"{cfg.base_url.rstrip('/')}/chat/completions"
    payload = {
        "model": cfg.model,
        "messages": messages,
        "temperature": float(cfg.temperature),
        "max_tokens": min(int(cfg.max_tokens), MAX_TOKENS_PER_CALL),
        "stream": bool(cfg.stream),
    }
    data = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    headers = {
        "Content-Type": "application/json",
        "Authorization": f"Bearer {cfg.api_key}",
        "User-Agent": "informal-evaluation/1.0",
    }
    req = urllib.request.Request(url, data=data, headers=headers, method="POST")

    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            raw = resp.read().decode("utf-8")
    except urllib.error.HTTPError as err:
        body = err.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"LLM API error {err.code}: {body[:500]}") from err
    except urllib.error.URLError as err:
        raise RuntimeError(f"LLM API connection error: {err.reason}") from err

    parts: list[str] = []
    usage = Usage()
    for line in raw.splitlines():
        if not line.startswith("data: ") or line.strip() == "data: [DONE]":
            continue
        try:
            chunk = json.loads(line[6:])
        except json.JSONDecodeError:
            continue
        choices = chunk.get("choices") or [{}]
        delta = choices[0].get("delta", {}) if isinstance(choices[0], dict) else {}
        piece = delta.get("content", "")
        if piece:
            parts.append(str(piece))
        chunk_usage = _parse_usage(chunk.get("usage"))
        if chunk_usage.total_tokens:
            usage = chunk_usage

    if parts:
        return "".join(parts), usage

    try:
        body = json.loads(raw)
    except json.JSONDecodeError as err:
        raise RuntimeError(f"LLM returned non-JSON response: {raw[:500]}") from err

    choices = body.get("choices") or []
    if not choices:
        raise RuntimeError(f"LLM returned no choices. Raw response: {raw[:500]}")
    content = choices[0].get("message", {}).get("content", "")
    usage = _parse_usage(body.get("usage"))
    if not str(content).strip():
        raise RuntimeError(f"LLM returned empty content. Raw response: {raw[:500]}")
    return str(content), usage

