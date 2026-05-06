#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""llm_client.py: OpenAI-compatible LLM 调用封装。"""

from __future__ import annotations

import json
import urllib.error
import urllib.request
from dataclasses import dataclass


MAX_SOLVE_TOKENS = 1_000_000


@dataclass
class ModelConfig:
    """模型配置（与现有实验 JSON 字段对齐）。"""
    model: str
    base_url: str
    api_key: str = "EMPTY"
    temperature: float = 0.6
    max_tokens: int = 4096
    stream: bool = False

    def __post_init__(self) -> None:
        """Normalize and cap token budget to avoid overly large requests."""
        self.max_tokens = min(int(self.max_tokens), MAX_SOLVE_TOKENS)


@dataclass
class Usage:
    """Token usage returned by API."""
    prompt_tokens: int = 0
    completion_tokens: int = 0
    total_tokens: int = 0


def _parse_usage(obj: dict | None) -> Usage:
    """Parse usage fields from OpenAI-compatible response payload."""
    if not obj:
        return Usage()
    pt = int(obj.get("prompt_tokens", 0) or 0)
    ct = int(obj.get("completion_tokens", 0) or 0)
    tt = int(obj.get("total_tokens", 0) or 0)
    if tt == 0:
        tt = pt + ct
    return Usage(prompt_tokens=pt, completion_tokens=ct, total_tokens=tt)


def generate_with_usage(
    messages: list[dict[str, str]],
    cfg: ModelConfig,
    *,
    timeout: float | None = None,
) -> tuple[str, Usage]:
    """Call API and return generated content plus token usage."""
    # Hard cap for solve calls: never request more than 1M output tokens.
    max_tokens = min(int(cfg.max_tokens), MAX_SOLVE_TOKENS)

    url = f"{cfg.base_url.rstrip('/')}/chat/completions"
    payload = {
        "model": cfg.model,
        "messages": messages,
        "temperature": cfg.temperature,
        "max_tokens": max_tokens,
        "stream": bool(cfg.stream),
    }
    data = json.dumps(payload).encode("utf-8")
    headers = {
        "Content-Type": "application/json",
        "Authorization": f"Bearer {cfg.api_key}",
        "User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36",
    }

    req = urllib.request.Request(url, data=data, headers=headers, method="POST")
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            raw = resp.read().decode("utf-8")
    except urllib.error.HTTPError as e:
        err_body = e.read().decode("utf-8", errors="replace")
        raise RuntimeError(
            f"LLM API error {e.code}: {err_body[:500]}"
        ) from e
    except urllib.error.URLError as e:
        raise RuntimeError(f"LLM API connection error: {e.reason}") from e

    # ---- 解析 SSE（Server-Sent Events）流式响应 ----
    content_parts: list[str] = []
    usage = Usage()
    for line in raw.splitlines():
        if not line.startswith("data: ") or line.strip() == "data: [DONE]":
            continue
        try:
            chunk = json.loads(line[6:])
            delta = chunk.get("choices", [{}])[0].get("delta", {})
            piece = delta.get("content", "")
            if piece:
                content_parts.append(piece)

            # 部分服务会把 usage 放在流的最后一个 chunk
            chunk_usage = _parse_usage(chunk.get("usage"))
            if chunk_usage.total_tokens > 0:
                usage = chunk_usage
        except (json.JSONDecodeError, IndexError, KeyError, TypeError):
            continue

    if not content_parts:
        # 兼容非流式响应（某些 endpoint 可能忽略 stream 参数）
        try:
            body = json.loads(raw)
            choices = body.get("choices", [])
            if choices:
                usage = _parse_usage(body.get("usage"))
                return choices[0]["message"]["content"], usage
        except json.JSONDecodeError:
            pass
        raise RuntimeError(f"LLM returned empty content. Raw response: {raw[:500]}")

    return "".join(content_parts), usage


def generate(
    messages: list[dict[str, str]],
    cfg: ModelConfig,
    *,
    timeout: float | None = None,
) -> str:
    """
    调用 OpenAI-compatible /v1/chat/completions 接口。

    Parameters
    ----------
    messages : 标准 OpenAI messages 列表
    cfg : 模型配置
    timeout : 请求超时秒数（None 表示无限等待）

    Returns
    -------
    模型回复文本
    """
    text, _ = generate_with_usage(messages, cfg, timeout=timeout)
    return text


def extract_lean_code(response: str) -> str:
    """
    从 LLM 回复中提取 Lean 代码块。

    优先提取 ```lean ... ``` 代码块；若不存在则返回原文去首尾空白。
    """
    import re
    m = re.search(r"```lean4?\s*\n(.*?)```", response, re.DOTALL)
    if m:
        return m.group(1).strip()
    m = re.search(r"```\s*\n(.*?)```", response, re.DOTALL)
    if m:
        return m.group(1).strip()
    return response.strip()
