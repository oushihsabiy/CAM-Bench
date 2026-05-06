"""Load JSON input files and config."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict, List

from .models import PipelineConfig


def load_json(path: Path) -> Any:
    """Read a JSON file and return parsed data."""
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, data: Any) -> None:
    """Write data to a JSON file with pretty-printing."""
    path.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(data, ensure_ascii=False, indent=2)
    path.write_text(text + "\n", encoding="utf-8")


def find_config(start: Path | None = None) -> Path:
    """Search for config.json starting from *start* (default: cwd), then up."""
    candidates: List[Path] = []
    if start:
        candidates.append(Path(start).resolve() / "config.json")
    candidates.append(Path.cwd() / "config.json")

    here = Path(__file__).resolve().parent
    for parent in [here] + list(here.parents):
        candidates.append(parent / "config.json")

    for c in candidates:
        if c.exists():
            return c.resolve()

    raise FileNotFoundError(
        "config.json not found (checked CWD and all parent directories)."
    )


def load_config(path: Path | None = None) -> PipelineConfig:
    """Load and validate pipeline configuration."""
    config_path = path or find_config()
    raw = load_json(config_path)
    if not isinstance(raw, dict):
        raise ValueError(f"{config_path} must contain a JSON object.")
    for key in ("api_key", "base_url", "model"):
        val = raw.get(key)
        if not isinstance(val, str) or not val.strip():
            raise KeyError(f"Missing or empty '{key}' in {config_path}")
    return PipelineConfig.from_dict(raw)


def load_prompt(name: str, prompts_dir: Path | None = None) -> str:
    """Load a prompt template by name from the prompts/ directory.

    *name* should be the stem, e.g. ``"concise_to_lean"`` →
    ``prompts/concise_to_lean.md``, or with subdirectory prefix,
    e.g. ``"translate/json_to_lean"`` → ``prompts/translate/json_to_lean.md``.
    
    Also supports backward compatibility: if a prompt file is not found
    in the specified location, searches in subdirectories (preprocess/, translate/, fixer/).
    """
    if prompts_dir is None:
        prompts_dir = Path(__file__).resolve().parents[2] / "prompts"

    # First try exact path with subdirectory if specified
    prompt_path = prompts_dir / f"{name}.md"
    if prompt_path.exists():
        text = prompt_path.read_text(encoding="utf-8").strip()
        if not text:
            raise ValueError(f"Prompt file is empty: {prompt_path}")
        return text
    
    # Fallback: search in common subdirectories if not found directly
    _subdirs = ["preprocess", "translate", "fixer"]
    for subdir in _subdirs:
        fallback_path = prompts_dir / subdir / f"{name}.md"
        if fallback_path.exists():
            text = fallback_path.read_text(encoding="utf-8").strip()
            if not text:
                raise ValueError(f"Prompt file is empty: {fallback_path}")
            return text
    
    raise FileNotFoundError(f"Prompt file not found: {prompt_path} (searched in {_subdirs})")


def load_settings(path: Path | str | None = None) -> Dict[str, Any]:
    """Load runtime settings from a JSON file.

    Settings are runtime-only parameters (not credentials).  If *path* is
    ``None`` or the file does not exist, an empty dict is returned so that
    the caller can proceed with defaults.
    """
    if path is None:
        return {}
    p = Path(path)
    if not p.exists():
        return {}
    raw = load_json(p)
    if not isinstance(raw, dict):
        raise ValueError(f"settings file must contain a JSON object: {p}")
    return raw
