import sys
from pathlib import Path

sys.path.insert(0, "src")

from json2lean.compile import compiling_fixer as cf
from json2lean.config import mcp_helper
from json2lean.models import Exercise


class _DummyClient:
    def chat(self, prompt: str, max_tokens: int, call_type: str, exercise_label: str) -> str:
        return "```lean\ntheorem t : True := by\n  trivial\n```"


class _DummyCompileResult:
    def __init__(self) -> None:
        self.returncode = 0
        self.warnings = []
        self.errors = []


def test_mcp_tool_names_follow_configured_list_exactly() -> None:
    names = cf._mcp_tool_names(
        tool_mode="all",
        has_focus_pos=True,
        configured_tools=["lean_leansearch", "lean_hover", "lean_leansearch"],
    )
    assert names == ["lean_leansearch", "lean_hover"]


def test_recover_all_passes_enabled_tools_to_mcp_context(monkeypatch, tmp_path: Path) -> None:
    captured: dict[str, object] = {}

    def _fake_gather(**kwargs):
        captured["enabled_tools"] = kwargs.get("enabled_tools")
        return ""

    def _fake_validate(exercise, lean_file, toolchain_dir, lean_timeout):
        exercise.compile_returncode = 0
        exercise.errors = []
        exercise.warnings = []
        return _DummyCompileResult()

    monkeypatch.setattr(mcp_helper, "gather_recovery_context", _fake_gather)
    monkeypatch.setattr(cf, "validate_exercise", _fake_validate)

    ex = Exercise(raw={"source_idx": "x", "kind": "theorem"}, index=1, label="x")
    ex.lean_code = "theorem t : True := by\n  trivial"
    ex.errors = [{"line": 1, "column": 1, "message": "dummy error"}]
    ex.compile_returncode = 1

    # recover_all computes context path as output_dir / f"{safe_label(label)}.lean"
    (tmp_path / "x.lean").write_text(ex.lean_code, encoding="utf-8")

    still_broken = cf.recover_all(
        _DummyClient(),
        [ex],
        tmp_path,
        toolchain_dir="lean",
        mcp_enabled=True,
        mcp_tools=["lean_leansearch", "lean_hover"],
        max_retries=1,
    )

    assert still_broken == []
    assert captured["enabled_tools"] == ["lean_leansearch", "lean_hover"]


def test_gather_context_uses_enabled_tools_as_execution_list(monkeypatch, tmp_path: Path) -> None:
    captured: dict[str, object] = {}

    def _fake_call_all_tools(**kwargs):
        captured["tool_calls"] = kwargs.get("tool_calls")
        captured["enabled_tools"] = kwargs.get("enabled_tools")
        return {}

    monkeypatch.setattr(mcp_helper, "call_all_tools", _fake_call_all_tools)

    f = tmp_path / "x.lean"
    f.write_text("theorem t : True := by trivial\n", encoding="utf-8")
    mcp_helper.gather_recovery_context(
        file_path=f,
        project_root=tmp_path,
        tool_mode="focused",
        focus_line=1,
        focus_column=2,
        errors=[{"line": 1, "column": 2, "message": "unknown identifier `foo`"}],
        enabled_tools=["lean_unified_search", "lean_hover", "lean_leansearch"],
    )

    calls = captured["tool_calls"]
    assert isinstance(calls, list) and calls
    names = [str(c.get("name")) for c in calls if isinstance(c, dict)]
    # unified first; hover included due to focus position; search provider calls exist
    assert names[0] == "lean_unified_search"
    assert "lean_hover" in names
    assert "lean_leansearch" in names
    assert captured["enabled_tools"] == ["lean_unified_search", "lean_hover", "lean_leansearch"]
