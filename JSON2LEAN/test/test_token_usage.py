from __future__ import annotations

import json
import sys
import types
from pathlib import Path

_SRC = Path(__file__).resolve().parents[1] / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))

from json2lean.token_usage import log_realtime_usage

try:
    import openai  # noqa: F401
except ModuleNotFoundError:
    openai_stub = types.ModuleType("openai")

    class _FakeOpenAI:
        def __init__(self, **_kwargs) -> None:
            self.chat = types.SimpleNamespace(
                completions=types.SimpleNamespace(create=lambda **_kw: None)
            )

    openai_stub.OpenAI = _FakeOpenAI
    sys.modules["openai"] = openai_stub

from json2lean.config.api_client import APIClient


def test_log_realtime_usage_writes_when_log_dir_is_passed(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.delenv("JSON2LEAN_REALTIME_LOG", raising=False)
    monkeypatch.delenv("JSON2LEAN_REALTIME_LOG_FILE", raising=False)
    monkeypatch.delenv("JSON2LEAN_TOKEN_LOG_DIR", raising=False)

    log_realtime_usage(
        model="test-model",
        call_type="translate",
        exercise_label="ex1",
        usage={"prompt_tokens": 2, "completion_tokens": 3, "total_tokens": 5},
        usage_source="api",
        log_dir=tmp_path,
    )

    log_path = tmp_path / "token_usage.jsonl"
    assert log_path.exists()
    record = json.loads(log_path.read_text(encoding="utf-8").strip())
    assert record["model"] == "test-model"
    assert record["call_type"] == "translate"
    assert record["total_tokens"] == 5


def test_api_client_chat_appends_realtime_token_log(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.delenv("JSON2LEAN_REALTIME_LOG", raising=False)
    monkeypatch.delenv("JSON2LEAN_REALTIME_LOG_FILE", raising=False)
    monkeypatch.delenv("JSON2LEAN_TOKEN_LOG_DIR", raising=False)

    class _Usage:
        prompt_tokens = 7
        completion_tokens = 11
        total_tokens = 18

    class _Message:
        content = "ok"

    class _Choice:
        message = _Message()

    class _Response:
        choices = [_Choice()]
        usage = _Usage()

    client = APIClient(
        api_key="test-key",
        base_url="https://example.com/v1",
        model="test-model",
        token_log_dir=tmp_path,
        realtime_token_log=True,
    )
    monkeypatch.setattr(
        client,
        "_call_chat_non_stream_with_token_fallback",
        lambda _base_kwargs, _max_tokens: _Response(),
    )

    assert client.chat(prompt="hello", call_type="translate", exercise_label="ex2") == "ok"

    records = [
        json.loads(line)
        for line in (tmp_path / "token_usage.jsonl").read_text(encoding="utf-8").splitlines()
    ]
    assert len(records) == 1
    assert records[0]["exercise_label"] == "ex2"
    assert records[0]["prompt_tokens"] == 7
    assert records[0]["usage_source"] == "api"
