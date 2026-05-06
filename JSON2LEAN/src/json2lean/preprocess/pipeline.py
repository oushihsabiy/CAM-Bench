"""Pipeline orchestrator — ties all preprocessing stages together."""

from __future__ import annotations

import os
import sys
import time
from pathlib import Path
from typing import Any, Callable, Dict, List

from ..config.api_client import APIClient
from ..loader import load_prompt, write_json
from ..models import Block, Exercise, StructuredExercise
from ._common import PROMPT_NAMES
from .models import FlatRecord
from .definition import _run_definition_extraction
from .hint_extraction import _run_hint_extraction
from .masking import _run_masking_stage
from .normalization import _run_normalization
from .theorem import _run_theorem_construction


# ------------------------------------------------------------------
# Public API: preprocess a single exercise
# ------------------------------------------------------------------

def preprocess_exercise(
    client: APIClient,
    exercise: Exercise,
    *,
    max_tokens: int = 4096,
    max_attempts: int = 4,
    prompts: Dict[str, str] | None = None,
    normalize: bool = True,
    normalize_skip_thm: bool = False,
) -> List[FlatRecord]:
    """Rewrite ``exercise`` into flat records via the new pipeline.

    Stages:
      0a: hint extraction with indexed markers
    0b: definition extraction (optimization-domain terms only)
    1:  special-block extraction (opt_prob / algo) with name assignment
      2:  theorem construction (placeholder filling + NL repair)
      3:  optional normalization pass

    Returns a list of :class:`FlatRecord` objects.

    Also updates ``exercise.structured``, ``exercise.preprocessed_problem``,
    and ``exercise.problem`` / ``exercise.raw["problem"]`` for backward
    compatibility with the downstream translation pipeline.
    """
    if prompts is None:
        prompts = {}
        for key, name in PROMPT_NAMES.items():
            try:
                prompts[key] = load_prompt(name)
            except FileNotFoundError:
                pass  # optional prompts (e.g. normalize)

    original_text = exercise.problem
    source = exercise.raw.get("source", "")

    # Resolve source_idx: top-level → nested content → index fallback
    _sid = exercise.raw.get("source_idx")
    if _sid is None or _sid == "":
        _content = exercise.raw.get("content")
        if isinstance(_content, dict):
            _sid = _content.get("source_idx")
    if _sid is None or _sid == "":
        _sid = exercise.raw.get("index")
    if _sid is None or _sid == "":
        _sid = exercise.index
    source_idx = str(_sid)

    # --- Stage 0a: hint extraction ---
    print("[preprocess]   stage: hint extraction", file=sys.stderr)
    hint_result = _run_hint_extraction(
        client,
        original_text,
        exercise.label,
        max_tokens=max_tokens,
        max_attempts=max_attempts,
        prompt_text=prompts.get("hint"),
    )

    hint_masked_text = hint_result.masked_text if hint_result.masked_text else original_text

    # --- Stage 0b: technical-term extraction ---
    print("[preprocess]   stage: technical-term extraction", file=sys.stderr)
    definition_items = _run_definition_extraction(
        client,
        hint_masked_text,  # after hint masking, before special-block masking
        exercise.label,
        max_tokens=max_tokens,
        max_attempts=max_attempts,
        prompt_text=prompts.get("definition"),
    )

    # --- Stage 1: special-block extraction ---
    print("[preprocess]   stage: special block extraction", file=sys.stderr)
    masking_result = _run_masking_stage(
        client,
        hint_masked_text,
        exercise.label,
        max_tokens=max_tokens,
        max_attempts=max_attempts,
        prompt_text=prompts.get("special_blocks"),
    )

    # Text for theorem construction: masking_result.masked_text (with hint + special placeholders)
    theorem_source_text = masking_result.masked_text

    # --- Stage 2: theorem construction ---
    print("[preprocess]   stage: theorem construction", file=sys.stderr)
    theorem_items = _run_theorem_construction(
        client,
        theorem_source_text,
        hint_result.items,
        masking_result.placeholders,
        exercise.label,
        max_tokens=max_tokens,
        max_attempts=max_attempts,
        prompt_text=prompts.get("construct_theorem"),
    )

    # --- Build flat records ---
    records: List[FlatRecord] = []
    record_idx = 0

    # Hint records
    for hint_item in hint_result.items:
        records.append(FlatRecord(
            index=record_idx,
            source=source,
            source_idx=source_idx,
            kind="hints",
            content=hint_item["text"],
        ))
        record_idx += 1

    # Definition records
    for defn_item in definition_items:
        records.append(FlatRecord(
            index=record_idx,
            source=source,
            source_idx=source_idx,
            kind="defn",
            content=defn_item["definition"],
            term=defn_item["term"],
        ))
        record_idx += 1

    # Opt_prob and algo records (ordered by position)
    for ph in sorted(masking_result.placeholders, key=lambda p: p.source_position):
        rec_kind = "opt_prob" if ph.kind == "optimization_problem" else "algo"
        records.append(FlatRecord(
            index=record_idx,
            source=source,
            source_idx=source_idx,
            kind=rec_kind,
            content=ph.original_text,
            term=ph.assigned_name,
        ))
        record_idx += 1

    # Theorem records
    for thm_item in theorem_items:
        records.append(FlatRecord(
            index=record_idx,
            source=source,
            source_idx=source_idx,
            kind="thm",
            content=thm_item["content"],
        ))
        record_idx += 1

    # --- Stage 3 (optional): normalization ---
    if normalize and "normalize" in prompts:
        print("[preprocess]   stage: normalization", file=sys.stderr)
        records = _run_normalization(
            client,
            records,
            exercise.label,
            max_tokens=max_tokens,
            max_attempts=max_attempts,
            prompt_text=prompts.get("normalize"),
            normalize_skip_thm=normalize_skip_thm,
        )

    # --- Backward compatibility: update exercise in-place ---
    blocks: List[Block] = []
    for rec in records:
        blocks.append(Block(
            id=str(rec.index),
            kind=rec.kind,
            text=rec.content,
        ))

    structured = StructuredExercise(
        index=source_idx,
        source_document=source,
        blocks=blocks,
    )
    exercise.structured = structured

    # Keep original problem for reference, but do NOT merge records back into exercise.problem
    # Records are now the primary unit for translation
    exercise.preprocessed_problem = original_text

    return records


# ------------------------------------------------------------------
# Public API: preprocess all exercises and write output
# ------------------------------------------------------------------

def preprocess_all(
    client: APIClient,
    exercises: List[Exercise],
    *,
    max_tokens: int = 4096,
    max_attempts: int = 4,
    normalize: bool = True,
    normalize_skip_thm: bool = False,
    exclude_hints: bool = False,
    output_dir: Path | str | None = None,
    input_stem: str = "",
    on_failure: Callable[[Exercise, Exception], None] | None = None,
) -> List[str]:
    """Preprocess all exercises via the new pipeline.

    Writes flat-record JSON to ``preprocessed_data/<input_stem>.json`` when
    *output_dir* is provided (or uses ``preprocessed_data/`` relative to
    the project root).

    Args:
        exclude_hints: If True, filter out records with kind="hints" before writing.

    Returns labels that failed.
    """
    prompts: Dict[str, str] = {}
    for key, name in PROMPT_NAMES.items():
        try:
            prompts[key] = load_prompt(name)
        except FileNotFoundError:
            pass

    exercise_retries = max(
        1, int(os.environ.get("JSON2LEAN_PREPROCESS_EXERCISE_RETRIES", "2"))
    )
    failed: List[str] = []
    total = len(exercises)
    all_records: List[Dict[str, Any]] = []

    for i, ex in enumerate(exercises, 1):
        print(f"[preprocess] [{i}/{total}] {ex.label}", file=sys.stderr)
        for attempt in range(1, exercise_retries + 1):
            try:
                records = preprocess_exercise(
                    client, ex,
                    max_tokens=max_tokens,
                    max_attempts=max_attempts,
                    prompts=prompts,
                    normalize=normalize,
                    normalize_skip_thm=normalize_skip_thm,
                )
                all_records.extend(r.to_dict() for r in records)
                break
            except Exception as err:
                if attempt >= exercise_retries:
                    failed.append(ex.label)
                    print(f"[preprocess] FAILED {ex.label}: {err}", file=sys.stderr)
                    if on_failure is not None:
                        try:
                            on_failure(ex, err)
                        except Exception as cb_err:
                            print(
                                f"[preprocess] failure callback error for {ex.label}: {cb_err}",
                                file=sys.stderr,
                            )
                    break
                delay = min(2 ** (attempt - 1), 8)
                print(
                    f"[preprocess] retry exercise {ex.label} "
                    f"{attempt}/{exercise_retries} after error: {err}",
                    file=sys.stderr,
                )
                time.sleep(delay)

    # Write output file
    if output_dir is None:
        project_root = Path(__file__).resolve().parents[3]
        output_dir = project_root / "preprocessed_data"
    else:
        output_dir = Path(output_dir)

    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    # Filter out hints if requested
    records_to_write = all_records
    if exclude_hints:
        original_count = len(all_records)
        records_to_write = [r for r in all_records if r.get("kind") != "hints"]
        hints_count = original_count - len(records_to_write)
        if hints_count > 0:
            print(f"[preprocess] Excluding {hints_count} hint records (exclude_hints=True)", file=sys.stderr)

    # Reindex output records globally to keep a stable contiguous sequence.
    # Use 1-based indexing for downstream readability in flat JSON artifacts.
    for i, rec in enumerate(records_to_write, 1):
        rec["index"] = i

    stem = input_stem or "preprocessed"
    output_path = output_dir / f"{stem}.json"
    write_json(output_path, records_to_write)
    print(f"[preprocess] Wrote {len(records_to_write)} records to {output_path}", file=sys.stderr)

    return failed


# ------------------------------------------------------------------
# Utility: re-index flat records for a single exercise
# ------------------------------------------------------------------

def reindex_records(records: List[FlatRecord], start: int = 0) -> None:
    """Re-assign sequential indices starting from *start*."""
    for i, rec in enumerate(records, start):
        rec.index = i
