#!/usr/bin/env python3
"""Load chapter JSON files for informal proof generation."""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any


_BLOCK_KEYS = ("blocks", "problems", "items", "data")


@dataclass(frozen=True)
class ProblemBlock:
    chapter_path: str
    chapter_stem: str
    ordinal: int
    original: dict[str, Any]
    problem_id: str
    problem_slug: str
    problem_text: str
    source_idx: str
    source: str


def _short_hash(obj: Any) -> str:
    raw = json.dumps(obj, ensure_ascii=False, sort_keys=True, default=str)
    return hashlib.sha1(raw.encode("utf-8")).hexdigest()[:10]


def safe_slug(value: object, *, fallback: str = "problem") -> str:
    text = str(value or "").strip()
    text = re.sub(r"\s+", "_", text)
    text = text.replace("/", "_").replace("\\", "_")
    text = re.sub(r"[^A-Za-z0-9._-]+", "_", text)
    text = re.sub(r"_+", "_", text).strip("._-")
    return text or fallback


def load_json(path: str | Path) -> Any:
    return json.loads(Path(path).read_text(encoding="utf-8"))


def _extract_entries(data: Any, path: Path) -> list[Any]:
    if isinstance(data, list):
        return data
    if isinstance(data, dict):
        for key in _BLOCK_KEYS:
            value = data.get(key)
            if isinstance(value, list):
                return value
        if "problem" in data or "statement" in data:
            return [data]
    raise ValueError(
        f"{path} must be a JSON list, an object with one of {_BLOCK_KEYS}, "
        "or a single object containing 'problem'/'statement'"
    )


def _problem_text(entry: dict[str, Any]) -> str:
    for key in ("problem", "statement", "question", "prompt"):
        value = entry.get(key)
        if value is not None and str(value).strip():
            return str(value).strip()
    return ""


def _problem_id(entry: dict[str, Any], ordinal: int) -> str:
    source_idx = str(entry.get("source_idx", "") or "").strip()
    if source_idx:
        return source_idx
    idx = entry.get("index")
    if idx is not None and str(idx).strip():
        return str(idx).strip()
    return f"problem_{ordinal:04d}"


def load_chapter(path: str | Path) -> list[ProblemBlock]:
    """Load one chapter JSON file and return normalized problem blocks."""
    chapter = Path(path).resolve()
    data = load_json(chapter)
    entries = _extract_entries(data, chapter)

    blocks: list[ProblemBlock] = []
    seen_slugs: dict[str, int] = {}
    for ordinal, raw_entry in enumerate(entries, start=1):
        if isinstance(raw_entry, dict):
            entry = dict(raw_entry)
        else:
            entry = {"problem": str(raw_entry)}

        problem_text = _problem_text(entry)
        if not problem_text:
            raise ValueError(f"{chapter}: block {ordinal} has no problem/statement text")

        pid = _problem_id(entry, ordinal)
        base_slug = safe_slug(pid, fallback=f"problem_{ordinal:04d}")
        count = seen_slugs.get(base_slug, 0)
        seen_slugs[base_slug] = count + 1
        slug = base_slug if count == 0 else f"{base_slug}_{_short_hash(entry)}"

        blocks.append(
            ProblemBlock(
                chapter_path=str(chapter),
                chapter_stem=chapter.stem,
                ordinal=ordinal,
                original=entry,
                problem_id=pid,
                problem_slug=slug,
                problem_text=problem_text,
                source_idx=str(entry.get("source_idx", "") or "").strip(),
                source=str(entry.get("source", "") or "").strip(),
            )
        )
    return blocks


def task_key(chapter_path: object, problem_id: object, model: object) -> str:
    chapter = str(chapter_path or "")
    try:
        chapter = str(Path(chapter).resolve())
    except Exception:
        pass
    return "\x1f".join([chapter, str(problem_id or ""), str(model or "")])

