"""Codex CLI client wrapper with token-usage tracking."""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Sequence

from ..models import TokenUsage
from ..token_usage import log_realtime_usage


_TOKENS_USED_RE = re.compile(
    r"tokens used(?:\s*[:=]?\s*|\s*\n\s*)([0-9][0-9,]*)",
    re.IGNORECASE,
)


class CodexCLIClient:
    """Thin wrapper around `codex exec` that mimics the APIClient interface."""

    def __init__(
        self,
        *,
        codex_bin: str,
        workdir: str | Path,
        model: str,
        reasoning_effort: str | None = None,
        disable_plugins: bool = True,
        max_retries: int = 3,
        retry_backoff_base_seconds: float = 1.0,
        retry_backoff_max_seconds: float = 8.0,
        call_log_dir: str | Path | None = None,
        token_log_dir: str | Path | None = None,
        realtime_token_log: bool | None = None,
        source_config_path: str | Path | None = None,
        extra_args: Sequence[str] | None = None,
    ) -> None:
        self.codex_bin = str(codex_bin)
        self.workdir = Path(workdir).resolve()
        self.model = str(model or "").strip()
        self.reasoning_effort = str(reasoning_effort or "").strip() or None
        self.disable_plugins = bool(disable_plugins)
        self.max_retries = max(1, int(max_retries))
        self.retry_backoff_base_seconds = max(0.1, float(retry_backoff_base_seconds))
        self.retry_backoff_max_seconds = max(
            self.retry_backoff_base_seconds, float(retry_backoff_max_seconds)
        )
        self.source_config_path = (
            str(Path(source_config_path).resolve()) if source_config_path else None
        )
        self.extra_args = list(extra_args or [])
        self.base_url = "codex-cli"
        self.usage_log: List[TokenUsage] = []
        self.token_log_dir = Path(token_log_dir) if token_log_dir is not None else None
        self.call_log_dir = (
            Path(call_log_dir)
            if call_log_dir is not None
            else (self.token_log_dir / "codex_cli_calls" if self.token_log_dir is not None else None)
        )
        self.realtime_token_log = realtime_token_log

    @staticmethod
    def _estimate_tokens(text: str) -> int:
        stripped = (text or "").strip()
        if not stripped:
            return 0
        return max(1, (len(stripped) + 3) // 4)

    @staticmethod
    def _parse_tokens_used(text: str) -> int | None:
        matches = list(_TOKENS_USED_RE.finditer(text or ""))
        if not matches:
            return None
        return int(matches[-1].group(1).replace(",", ""))

    def _build_cmd(self, output_path: Path) -> list[str]:
        cmd = [self.codex_bin]
        if self.disable_plugins:
            # Avoid startup remote plugin sync that requires ChatGPT OAuth and can
            # fail in API-key-only deployments.
            cmd += ["--disable", "plugins"]
        cmd += ["exec", "--full-auto", "-C", str(self.workdir), "-o", str(output_path)]
        if self.model:
            cmd += ["-m", self.model]
        if self.reasoning_effort:
            cmd += ["-c", f'model_reasoning_effort="{self.reasoning_effort}"']
        cmd.extend(self.extra_args)
        cmd.append("-")
        return cmd

    def _is_responses_incompatible(self, text: str) -> bool:
        low = (text or "").lower()
        return "response.completed" in low or "stream disconnected before completion" in low

    def _is_retryable_failure(self, text: str) -> bool:
        low = (text or "").lower()
        retry_markers = (
            "reconnecting...",
            "stream disconnected",
            "connection error",
            "timed out",
            "timeout",
            "temporary failure",
            "service unavailable",
            "rate limit",
        )
        return any(marker in low for marker in retry_markers)

    def _retry_delay_seconds(self, attempt: int) -> float:
        # attempt is 1-based
        delay = self.retry_backoff_base_seconds * (2 ** max(0, attempt - 1))
        return min(delay, self.retry_backoff_max_seconds)

    @staticmethod
    def _stderr(msg: str) -> None:
        try:
            print(msg, file=sys.stderr, flush=True)
        except Exception:
            pass

    def _log_call(
        self,
        *,
        attempt: int,
        call_type: str,
        exercise_label: str,
        cmd: Sequence[str],
        prompt: str,
        response: str,
        result: subprocess.CompletedProcess[str],
    ) -> None:
        if self.call_log_dir is None:
            return
        try:
            self.call_log_dir.mkdir(parents=True, exist_ok=True)
            ts = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
            safe_call = re.sub(r"[^A-Za-z0-9_.-]+", "_", call_type or "chat")
            safe_label = re.sub(r"[^A-Za-z0-9_.-]+", "_", exercise_label or "na")
            path = self.call_log_dir / f"{ts}_{safe_call}_{safe_label}_a{attempt}.log"
            payload = {
                "ts_utc": ts,
                "attempt": attempt,
                "call_type": call_type,
                "exercise_label": exercise_label,
                "returncode": int(result.returncode),
                "cmd": list(cmd),
                "workdir": str(self.workdir),
            }
            text = (
                "META:\n"
                + json.dumps(payload, ensure_ascii=False, indent=2)
                + "\n\nPROMPT:\n"
                + prompt
                + "\n\nOUTPUT:\n"
                + response
                + "\n\nSTDERR:\n"
                + (result.stderr or "")
                + "\n\nSTDOUT:\n"
                + (result.stdout or "")
            )
            path.write_text(text, encoding="utf-8")
        except Exception:
            # Logging should never break the main pipeline path.
            pass

    def chat(
        self,
        *,
        prompt: str,
        max_tokens: int = 4096,
        call_type: str = "",
        exercise_label: str = "",
        json_mode: bool = False,
    ) -> str:
        usage = TokenUsage(call_type=call_type, exercise_label=exercise_label)

        if not self.workdir.exists():
            raise FileNotFoundError(f"Codex workdir does not exist: {self.workdir}")

        env = None
        if self.source_config_path:
            env = dict(os.environ)
            env["JSON2LEAN_CODEX_SOURCE_CONFIG"] = self.source_config_path
            if self.model:
                env["JSON2LEAN_CODEX_MODEL"] = self.model
            if self.reasoning_effort:
                env["JSON2LEAN_CODEX_REASONING_EFFORT"] = self.reasoning_effort

        final_result: subprocess.CompletedProcess[str] | None = None
        final_response = ""
        for attempt in range(1, self.max_retries + 1):
            started_at = time.monotonic()
            self._stderr(
                f"[codex_cli] call_type={call_type or 'chat'} "
                f"label={exercise_label or 'na'} attempt={attempt}/{self.max_retries}"
            )
            with tempfile.TemporaryDirectory(prefix="json2lean_codex_") as tmpdir:
                output_path = Path(tmpdir) / "last_message.txt"
                cmd = self._build_cmd(output_path)
                result = subprocess.run(
                    cmd,
                    cwd=str(self.workdir),
                    input=prompt,
                    text=True,
                    capture_output=True,
                    env=env,
                )
                response = (
                    output_path.read_text(encoding="utf-8").strip()
                    if output_path.exists()
                    else ""
                )
                self._log_call(
                    attempt=attempt,
                    call_type=call_type,
                    exercise_label=exercise_label,
                    cmd=cmd,
                    prompt=prompt,
                    response=response,
                    result=result,
                )

            final_result = result
            final_response = response
            elapsed = time.monotonic() - started_at
            self._stderr(
                f"[codex_cli] done call_type={call_type or 'chat'} "
                f"label={exercise_label or 'na'} attempt={attempt} "
                f"rc={result.returncode} response_chars={len(response or '')} "
                f"elapsed_s={elapsed:.1f}"
            )

            if result.returncode == 0 and response:
                self._stderr(
                    f"[codex_cli] OK call_type={call_type or 'chat'} "
                    f"label={exercise_label or 'na'} attempt={attempt}"
                )
                break

            err_text = (result.stderr or result.stdout or "").strip()
            if self._is_responses_incompatible(err_text):
                raise RuntimeError(
                    "codex exec failed: provider responses endpoint appears incompatible "
                    "(stream closed before response.completed). "
                    "This backend currently requires a provider with stable /responses streaming."
                )
            if attempt >= self.max_retries or not self._is_retryable_failure(err_text):
                tail = err_text[-2000:] if len(err_text) > 2000 else err_text
                if result.returncode != 0:
                    raise RuntimeError(
                        f"codex exec failed with code {result.returncode}: {tail}"
                    )
                raise RuntimeError("codex exec returned empty output")
            self._stderr(
                f"[codex_cli] retrying call_type={call_type or 'chat'} "
                f"label={exercise_label or 'na'} after attempt={attempt}"
            )
            time.sleep(self._retry_delay_seconds(attempt))

        if final_result is None:
            raise RuntimeError("codex exec did not run")
        result = final_result
        response = final_response
        if not response:
            raise RuntimeError("codex exec returned empty output")

        used = self._parse_tokens_used(result.stderr) or self._parse_tokens_used(result.stdout)
        if used is not None:
            usage.total_tokens = used
            usage.prompt_tokens = min(used, self._estimate_tokens(prompt))
            usage.completion_tokens = max(0, used - usage.prompt_tokens)
            usage.usage_source = "cli_reported"
        else:
            usage.prompt_tokens = self._estimate_tokens(prompt)
            usage.completion_tokens = self._estimate_tokens(response)
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
        return response

    def total_usage(self) -> Dict[str, int]:
        totals = {"prompt_tokens": 0, "completion_tokens": 0, "total_tokens": 0}
        for u in self.usage_log:
            totals["prompt_tokens"] += u.prompt_tokens
            totals["completion_tokens"] += u.completion_tokens
            totals["total_tokens"] += u.total_tokens
        return totals

    def dump_usage(self) -> List[Dict[str, Any]]:
        return [u.to_dict() for u in self.usage_log]
