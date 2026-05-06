"""OpenAI API client wrapper with token-usage tracking."""

from __future__ import annotations

import json
import math
import os
import random
import sys
import time
from pathlib import Path
from typing import Any, Dict, List, Optional

from openai import OpenAI

from ..models import TokenUsage
from ..token_usage import log_realtime_usage


class EmptyResponseError(RuntimeError):
    """Raised when provider returns an empty text response."""


class APIClient:
    """Thin wrapper around OpenAI that records token consumption."""

    def __init__(
        self,
        api_key: str,
        base_url: str,
        model: str,
        timeout: float = 180.0,
        token_log_dir: str | Path | None = None,
        realtime_token_log: bool | None = None,
    ) -> None:
        self._normalize_proxy_env_for_httpx()
        self._client = OpenAI(
            api_key=api_key,
            base_url=base_url,
            timeout=timeout,
        )
        self.base_url = base_url
        self.model = model
        base_url_norm = (base_url or "").strip().lower()
        self._is_codex_gateway = "codex-for.me" in base_url_norm
        # codex-for.me gateways are stream-first and are more stable in stream mode.
        self._force_stream: Optional[bool] = True if self._is_codex_gateway else None
        self.usage_log: List[TokenUsage] = []
        self.max_retries: int = max(1, int(os.environ.get("JSON2LEAN_API_MAX_RETRIES", "4")))
        self.backoff_base_seconds: float = float(
            os.environ.get("JSON2LEAN_API_BACKOFF_BASE_SECONDS", "0.8")
        )
        self.backoff_max_seconds: float = float(
            os.environ.get("JSON2LEAN_API_BACKOFF_MAX_SECONDS", "8.0")
        )
        self._token_param_hint = os.environ.get("JSON2LEAN_TOKEN_PARAM_HINT", "").strip()
        self.token_log_dir = Path(token_log_dir) if token_log_dir is not None else None
        self.realtime_token_log = realtime_token_log
        timeout_env = os.environ.get("JSON2LEAN_API_REQUEST_TIMEOUT")
        self.request_timeout_seconds: float | None = (
            float(timeout_env) if timeout_env else None
        )

    @staticmethod
    def _normalize_proxy_env_for_httpx() -> None:
        """Normalize proxy env so httpx/OpenAI client won't fail on socks:// scheme."""

        def _norm(url: str) -> str:
            u = (url or "").strip()
            if not u:
                return u
            if u.lower().startswith("socks://"):
                return "socks5://" + u[len("socks://") :]
            return u

        def _set_pair(lower: str, upper: str, value: str) -> None:
            os.environ[lower] = value
            os.environ[upper] = value

        # Optional hard switch to ignore ALL_PROXY for API calls.
        if os.getenv("JSON2LEAN_API_IGNORE_ALL_PROXY", "1").strip() == "1":
            os.environ.pop("all_proxy", None)
            os.environ.pop("ALL_PROXY", None)

        for lower, upper in (
            ("http_proxy", "HTTP_PROXY"),
            ("https_proxy", "HTTPS_PROXY"),
            ("all_proxy", "ALL_PROXY"),
        ):
            cur = os.getenv(lower) or os.getenv(upper) or ""
            cur = _norm(cur)
            if cur:
                _set_pair(lower, upper, cur)

    # ------------------------------------------------------------------
    # Streaming helpers
    # ------------------------------------------------------------------

    @staticmethod
    def _collect_stream(stream: Any) -> tuple[str, Optional[Dict[str, int]]]:
        parts: List[str] = []
        usage: Optional[Dict[str, int]] = None
        try:
            for chunk in stream:
                chunk_usage = getattr(chunk, "usage", None)
                if chunk_usage:
                    usage = {
                        "prompt_tokens": getattr(chunk_usage, "prompt_tokens", 0) or 0,
                        "completion_tokens": getattr(chunk_usage, "completion_tokens", 0) or 0,
                        "total_tokens": getattr(chunk_usage, "total_tokens", 0) or 0,
                    }
                choices = getattr(chunk, "choices", None) or []
                if not choices:
                    continue
                delta = getattr(choices[0], "delta", None)
                if delta is None:
                    continue
                content = getattr(delta, "content", None)
                if isinstance(content, str):
                    parts.append(content)
        finally:
            close_fn = getattr(stream, "close", None)
            if callable(close_fn):
                try:
                    close_fn()
                except Exception:
                    pass
        return "".join(parts), usage

    @staticmethod
    def _estimate_tokens(text: str) -> int:
        """Rough token estimate fallback when provider omits usage."""
        stripped = (text or "").strip()
        if not stripped:
            return 0
        return max(1, math.ceil(len(stripped) / 4))

    # ------------------------------------------------------------------
    # Core chat call
    # ------------------------------------------------------------------

    def chat(
        self,
        *,
        prompt: str,
        max_tokens: int = 4096,
        call_type: str = "",
        exercise_label: str = "",
        json_mode: bool = False,
    ) -> str:
        """Send a chat-completion request and return the assistant text.

        Token usage (if reported by the API) is appended to
        ``self.usage_log``.
        """
        base_kwargs: Dict[str, Any] = dict(
            model=self.model,
            messages=[{"role": "user", "content": prompt}],
            temperature=0.0,
            top_p=1.0,
        )
        if json_mode:
            base_kwargs["response_format"] = {"type": "json_object"}

        usage = TokenUsage(call_type=call_type, exercise_label=exercise_label)

        text = ""
        last_err: Exception | None = None
        call_max_retries = self.max_retries
        if call_type == "postprocess_comment_rewrite":
            call_max_retries = max(
                1,
                int(os.environ.get("JSON2LEAN_POSTPROCESS_COMMENT_MAX_RETRIES", "2")),
            )

        for attempt in range(1, call_max_retries + 1):
            try:
                # Try non-streaming first; fall back to streaming if forced.
                if self._force_stream is True:
                    text, stream_usage = self._call_chat_stream_with_token_fallback(
                        base_kwargs, max_tokens
                    )
                    if stream_usage:
                        usage.prompt_tokens = stream_usage["prompt_tokens"]
                        usage.completion_tokens = stream_usage["completion_tokens"]
                        usage.total_tokens = stream_usage["total_tokens"]
                        usage.usage_source = "api_stream"
                else:
                    try:
                        resp = self._call_chat_non_stream_with_token_fallback(
                            base_kwargs, max_tokens
                        )
                        text = (resp.choices[0].message.content or "").strip()
                        # Record token usage from response
                        if hasattr(resp, "usage") and resp.usage:
                            usage.prompt_tokens = resp.usage.prompt_tokens or 0
                            usage.completion_tokens = resp.usage.completion_tokens or 0
                            usage.total_tokens = resp.usage.total_tokens or 0
                            usage.usage_source = "api"
                    except Exception as err:
                        if "stream must be set to true" in str(err).lower():
                            self._force_stream = True
                            text, stream_usage = self._call_chat_stream_with_token_fallback(
                                base_kwargs, max_tokens
                            )
                            if stream_usage:
                                usage.prompt_tokens = stream_usage["prompt_tokens"]
                                usage.completion_tokens = stream_usage["completion_tokens"]
                                usage.total_tokens = stream_usage["total_tokens"]
                                usage.usage_source = "api_stream"
                        else:
                            raise
                if not text.strip():
                    raise EmptyResponseError("Empty response text from provider")
                break
            except Exception as err:
                last_err = err
                if isinstance(err, EmptyResponseError) and self._force_stream is not True:
                    # Some gateways occasionally return empty non-stream content.
                    # Switching to stream mode often recovers.
                    self._force_stream = True
                if attempt >= call_max_retries or not self._is_retryable_error(err):
                    raise
                delay = self._backoff_seconds(attempt)
                print(
                    f"[api_client] retry {attempt}/{call_max_retries} after error: {err}",
                    file=sys.stderr,
                )
                time.sleep(delay)

        if last_err is not None and not text:
            raise last_err

        if usage.total_tokens <= 0:
            usage.prompt_tokens = self._estimate_tokens(prompt)
            usage.completion_tokens = self._estimate_tokens(text)
            usage.total_tokens = usage.prompt_tokens + usage.completion_tokens
            usage.usage_source = "estimated"

        self.usage_log.append(usage)
        log_realtime_usage(
            model=self.model,
            base_url=self.base_url,
            call_type=call_type,
            exercise_label=exercise_label,
            usage={
                "prompt_tokens": usage.prompt_tokens,
                "completion_tokens": usage.completion_tokens,
                "total_tokens": usage.total_tokens,
            },
            usage_source=usage.usage_source,
            log_dir=self.token_log_dir,
            enabled=self.realtime_token_log,
        )
        return text

    def _is_retryable_error(self, err: Exception) -> bool:
        msg = str(err).lower()
        name = type(err).__name__

        if "timed out" in msg or "timeout" in msg:
            return True
        if "temporarily unavailable" in msg or "connection reset" in msg:
            return True
        if "invalid api key" in msg:
            # Some OpenAI-compatible gateways may return transient auth failures.
            return True
        if isinstance(err, EmptyResponseError):
            return True

        retryable_by_name = {
            "RateLimitError",
            "APITimeoutError",
            "APIConnectionError",
            "InternalServerError",
            "AuthenticationError",
            "APIStatusError",
        }
        if name in retryable_by_name:
            return True

        status_code = getattr(err, "status_code", None)
        if isinstance(status_code, int):
            if status_code in {401, 408, 409, 429}:
                return True
            if 500 <= status_code < 600:
                return True

        return False

    def _backoff_seconds(self, attempt: int) -> float:
        delay = self.backoff_base_seconds * (2 ** (attempt - 1))
        jitter = random.uniform(0.8, 1.2)
        return min(delay * jitter, self.backoff_max_seconds)

    def _is_unsupported_token_param(self, err: Exception, token_param: str) -> bool:
        msg = str(err).lower()
        if token_param.lower() not in msg:
            return False
        return (
            "unknown parameter" in msg
            or "unexpected keyword argument" in msg
            or "not supported" in msg
            or "invalid request" in msg
        )

    def _token_param_order(self) -> List[str]:
        ordered = ["max_completion_tokens", "max_tokens"]
        hint = self._token_param_hint
        if hint in ordered:
            return [hint] + [p for p in ordered if p != hint]
        return ordered

    def _call_chat_non_stream_with_token_fallback(
        self,
        base_kwargs: Dict[str, Any],
        max_tokens: int,
    ) -> Any:
        last_err: Exception | None = None
        for token_param in self._token_param_order():
            req = dict(base_kwargs)
            req[token_param] = max_tokens
            if self.request_timeout_seconds is not None:
                req["timeout"] = self.request_timeout_seconds
            try:
                resp = self._client.chat.completions.create(**req)
                self._token_param_hint = token_param
                return resp
            except Exception as err:
                last_err = err
                if self._is_unsupported_token_param(err, token_param):
                    continue
                raise
        if last_err is not None:
            raise last_err
        raise RuntimeError("chat completion failed without a concrete error")

    def _call_chat_stream_with_token_fallback(
        self,
        base_kwargs: Dict[str, Any],
        max_tokens: int,
    ) -> tuple[str, Optional[Dict[str, int]]]:
        last_err: Exception | None = None
        for token_param in self._token_param_order():
            req = dict(base_kwargs)
            req[token_param] = max_tokens
            if self.request_timeout_seconds is not None:
                req["timeout"] = self.request_timeout_seconds
            try:
                text, usage = self._do_stream(req)
                self._token_param_hint = token_param
                return text, usage
            except Exception as err:
                last_err = err
                if self._is_unsupported_token_param(err, token_param):
                    continue
                raise
        if last_err is not None:
            raise last_err
        raise RuntimeError("chat stream completion failed without a concrete error")

    def _do_stream(self, kwargs: Dict[str, Any]) -> tuple[str, Optional[Dict[str, int]]]:
        stream = self._client.chat.completions.create(
            stream=True,
            stream_options={"include_usage": True},
            **kwargs,
        )
        text, usage = self._collect_stream(stream)
        return text.strip(), usage

    # ------------------------------------------------------------------
    # Aggregation helpers
    # ------------------------------------------------------------------

    def total_usage(self) -> Dict[str, int]:
        totals = {"prompt_tokens": 0, "completion_tokens": 0, "total_tokens": 0}
        for u in self.usage_log:
            totals["prompt_tokens"] += u.prompt_tokens
            totals["completion_tokens"] += u.completion_tokens
            totals["total_tokens"] += u.total_tokens
        return totals

    def dump_usage(self) -> List[Dict[str, Any]]:
        return [u.to_dict() for u in self.usage_log]


# ------------------------------------------------------------------
# JSON extraction utility (shared by preprocessor & translater)
# ------------------------------------------------------------------

def _fix_unescaped_backslashes(text: str) -> str:
    """Double any backslash not already part of a valid JSON escape sequence.

    LLMs that emit LaTeX (e.g. ``\\nabla``, ``\\text{}``, ``\\le``) inside
    JSON strings commonly forget to double the backslash.  This function
    repairs those occurrences so that ``json.loads`` can succeed.

    Valid single-character JSON escapes after ``\\`` are: ``"  \\  /  b  f  n  r  t  u``
    Everything else is invalid and must be doubled.
    """
    import re as _re
    # Match a backslash NOT followed by a valid JSON escape character
    return _re.sub(r'\\(?!["\\\/bfnrtu])', r'\\\\', text)


def extract_json_value(text: str) -> Any:
    """Best-effort extraction of a JSON value from model output."""
    stripped = (text or "").strip()
    if not stripped:
        raise ValueError("Model returned empty output.")

    try:
        return json.loads(stripped)
    except json.JSONDecodeError:
        pass

    # Try inside code fences
    fence_start = stripped.find("```")
    if fence_start >= 0:
        fence_end = stripped.rfind("```")
        if fence_end > fence_start:
            fenced = stripped[fence_start + 3 : fence_end].strip()
            nl = fenced.find("\n")
            if nl >= 0 and fenced[:nl].strip().lower() in ("json", ""):
                fenced = fenced[nl + 1 :].strip()
            try:
                return json.loads(fenced)
            except json.JSONDecodeError:
                pass
            # Retry with backslash repair
            try:
                return json.loads(_fix_unescaped_backslashes(fenced))
            except json.JSONDecodeError:
                pass

    # Try first { … } or [ … ]
    for open_ch, close_ch in [("{", "}"), ("[", "]")]:
        start = stripped.find(open_ch)
        end = stripped.rfind(close_ch)
        if start >= 0 and end > start:
            candidate = stripped[start : end + 1]
            try:
                return json.loads(candidate)
            except json.JSONDecodeError:
                pass
            # Retry with backslash repair
            try:
                return json.loads(_fix_unescaped_backslashes(candidate))
            except json.JSONDecodeError:
                pass

    raise ValueError("Model output is not valid JSON.")


def extract_lean_code(text: str) -> str:
    """Extract Lean code from a model response (handles code fences)."""
    stripped = (text or "").strip()
    if not stripped:
        raise ValueError("Model returned empty output.")

    # If wrapped in ```lean … ```
    fence_start = stripped.find("```")
    if fence_start >= 0:
        fence_end = stripped.rfind("```")
        if fence_end > fence_start:
            inner = stripped[fence_start + 3 : fence_end].strip()
            nl = inner.find("\n")
            if nl >= 0 and inner[:nl].strip().lower() in ("lean", "lean4", ""):
                inner = inner[nl + 1 :]
            return inner.strip()

    return stripped
