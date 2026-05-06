"""Translate a preprocessed exercise into Lean 4 code via the LLM."""

from __future__ import annotations

import json
import sys
import re
from typing import Any, Dict, List

from .config.api_client import APIClient, extract_lean_code
from .semantic.declaration_policy import validate_top_level_contract
from .loader import load_prompt
from .models import Exercise, ExerciseStatus


def _kind_hint(kind_value: Any) -> str:
    """Quick kind-specific constraint reminder (detailed rules in json_to_lean.md).

    Note: Block comments, directives, variable placement, and other constraints are
    defined in the main prompt (json_to_lean.md) and need not be repeated here.
    """
    k = str(kind_value or "").strip().lower()
    constraints = {
        "defn": "Kind: definition. Use `def` (not theorem/structure). Must have concrete body (no sorry). Maximize reuse from section_context.",
        "thm": "Kind: theorem. Use `theorem` (not def/structure). One top-level theorem only. Proof body: `by sorry`. Reuse existing definitions from section_context.",
        "alg": "Kind: algorithmic schema. Use `structure` as primal declaration (not def/theorem).",
        "algo": "Kind: algorithmic schema. Use `structure` as primal declaration (not def/theorem).",
        "opt_prob": "Kind: optimization problem. Use `structure` as primal declaration (not def/theorem).",
        "hints": "",
    }
    return constraints.get(k, "")


def _build_prompt(
    base_prompt: str,
    exercise: Exercise,
    translation_record: Dict[str, Any] | None = None,
    section_context: str = "",
    mcp_context: str = "",
) -> str:
    if translation_record is not None:
        payload: Dict[str, Any] = dict(translation_record)
        for k in ("index", "source", "source_idx", "kind", "term", "content", "problem"):
            if k not in payload and isinstance(exercise.raw, dict):
                payload[k] = exercise.raw.get(k)
    else:
        payload = exercise.raw
    kind_instruction = _kind_hint(payload.get("kind") if isinstance(payload, dict) else "")
    obj_json = json.dumps(payload, ensure_ascii=False, indent=2)
    ctx = str(section_context or "").strip()
    context_block = ""
    if ctx:
        context_block = (
            "\n\nSection-local Lean context (read-only — reuse existing definitions):\n\n"
            f"{ctx}\n"
        )
    mcp = str(mcp_context or "").strip()
    mcp_block = ""
    if mcp:
        mcp_block = (
            "\n\nMCP auxiliary context (read-only — use to understand domain and avoid conflicts):\n\n"
            f"{mcp}\n"
        )
    if kind_instruction:
        return f"{base_prompt}\n\n{kind_instruction}\n{context_block}{mcp_block}\n{obj_json}"
    return f"{base_prompt}{context_block}{mcp_block}\n\n{obj_json}"





def translate_exercise(
    client: APIClient,
    exercise: Exercise,
    *,
    max_tokens: int = 4096,
    max_attempts: int = 3,
    prompt_text: str | None = None,
    translation_record: Dict[str, Any] | None = None,
    section_context: str = "",
    mcp_context: str = "",
) -> None:
    """Translate one exercise to Lean 4 code **in-place**.

    Sets ``exercise.lean_code`` and updates ``exercise.status``.
    """
    if prompt_text is None:
        prompt_text = load_prompt("json_to_lean")

    last_error = ""
    for attempt in range(1, max_attempts + 1):
        full_prompt = _build_prompt(
            prompt_text,
            exercise,
            translation_record=translation_record,
            section_context=section_context,
            mcp_context=mcp_context,
        )
        try:
            response = client.chat(
                prompt=full_prompt,
                max_tokens=max_tokens,
                call_type="translate",
                exercise_label=exercise.label,
            )
            code = extract_lean_code(response)
        except Exception as err:
            last_error = str(err)
            print(
                f"[translate] attempt {attempt} failed for {exercise.label}: {err}",
                file=sys.stderr,
            )
            continue

        if not code.strip():
            last_error = "Empty Lean code returned"
            continue

        kind = str((exercise.raw or {}).get("kind") or "").strip().lower()
        contract_error = validate_top_level_contract(kind, code)
        if contract_error:
            last_error = contract_error
            print(
                f"[translate] attempt {attempt} contract violation for {exercise.label}: {contract_error}",
                file=sys.stderr,
            )
            continue

        exercise.lean_code = code
        exercise.status = ExerciseStatus.TRANSLATED
        return

    raise RuntimeError(
        f"Translation failed for {exercise.label} after {max_attempts} attempts: {last_error}"
    )


def translate_all(
    client: APIClient,
    exercises: List[Exercise],
    *,
    max_tokens: int = 4096,
    max_attempts: int = 3,
    translation_record_by_label: Dict[str, Dict[str, Any]] | None = None,
    section_context_by_label: Dict[str, str] | None = None,
    mcp_context_by_label: Dict[str, str] | None = None,
) -> List[str]:
    """Translate every exercise. Returns labels that failed."""
    prompt_text = load_prompt("json_to_lean")
    failed: List[str] = []
    total = len(exercises)

    for i, ex in enumerate(exercises, 1):
        print(f"[translate] [{i}/{total}] {ex.label}", file=sys.stderr)
        try:
            translate_exercise(
                client, ex,
                max_tokens=max_tokens,
                max_attempts=max_attempts,
                prompt_text=prompt_text,
                translation_record=(translation_record_by_label or {}).get(str(ex.label)),
                section_context=(section_context_by_label or {}).get(str(ex.label), ""),
                mcp_context=(mcp_context_by_label or {}).get(str(ex.label), ""),
            )
        except Exception as err:
            failed.append(ex.label)
            ex.status = ExerciseStatus.ERROR
            print(f"[translate] FAILED {ex.label}: {err}", file=sys.stderr)

    return failed
