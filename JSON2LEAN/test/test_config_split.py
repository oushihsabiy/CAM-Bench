"""Tests for config split: load_settings + overlay_settings."""
import sys
import json
import tempfile
from pathlib import Path

sys.path.insert(0, "src")

from json2lean.loader import load_settings
from json2lean.models import PipelineConfig


def test_load_settings_none():
    result = load_settings(None)
    assert result == {}


def test_load_settings_missing_file():
    result = load_settings("/tmp/nonexistent_settings_12345.json")
    assert result == {}


def test_load_settings_valid():
    with tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False) as f:
        json.dump({"semantic": {"enabled": True, "max_rounds": 5}}, f)
        f.flush()
        result = load_settings(f.name)
    assert result["semantic"]["enabled"] is True
    assert result["semantic"]["max_rounds"] == 5
    Path(f.name).unlink()


def test_overlay_settings_empty():
    cfg = PipelineConfig(api_key="k", base_url="u", model="m")
    original_rounds = cfg.semantic_max_rounds
    cfg.overlay_settings({})
    assert cfg.semantic_max_rounds == original_rounds


def test_overlay_settings_nested():
    cfg = PipelineConfig(api_key="k", base_url="u", model="m")
    assert cfg.semantic_enabled is False
    assert cfg.semantic_max_rounds == 8
    cfg.overlay_settings({
        "semantic": {"enabled": True, "max_rounds": 3},
        "translation": {"max_tokens": 8192},
    })
    assert cfg.semantic_enabled is True
    assert cfg.semantic_max_rounds == 3
    assert cfg.translation_max_tokens == 8192


def test_overlay_settings_top_level_scalar():
    cfg = PipelineConfig(api_key="k", base_url="u", model="m")
    cfg.overlay_settings({"timeout_seconds": 300.0})
    assert cfg.timeout_seconds == 300.0


def test_overlay_settings_partial():
    cfg = PipelineConfig(api_key="k", base_url="u", model="m")
    original_retries = cfg.recovery_max_retries
    cfg.overlay_settings({"recovery": {"max_tokens": 2048}})
    assert cfg.recovery_max_tokens == 2048
    assert cfg.recovery_max_retries == original_retries  # unchanged


if __name__ == "__main__":
    import inspect
    tests = [
        (name, obj)
        for name, obj in sorted(globals().items())
        if name.startswith("test_") and inspect.isfunction(obj)
    ]
    passed = 0
    for name, fn in tests:
        try:
            fn()
            passed += 1
            print(f"  PASS  {name}")
        except Exception as e:
            print(f"  FAIL  {name}: {e}")
    print(f"\n{passed}/{len(tests)} tests passed")
