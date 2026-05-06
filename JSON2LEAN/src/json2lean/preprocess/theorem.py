"""Stage 2 — Theorem construction with conservative placeholder filling."""

from __future__ import annotations

import json
from typing import Dict, List

from ..config.api_client import APIClient, extract_json_value
from ..loader import load_prompt
from ._common import PROMPT_NAMES
from .models import Placeholder
from .validators import _validate_theorem_output


def _build_theorem_prompt(
    base_prompt: str,
    problem_text: str,
    hint_items: List[Dict[str, str]],
    placeholders: List[Placeholder],
    feedback: str = "",
) -> str:
    """Build prompt for theorem construction stage.

    Benchmark-oriented policy: provide original placeholder text so the model
    can perform minimally invasive reconstruction of theorem statements.
    """
    placeholder_info = []
    for ph in placeholders:
        ph_kind = "opt_prob" if ph.kind == "optimization_problem" else "algo"
        replacement_text = ph.original_text.strip() or ph.assigned_name
        placeholder_info.append({
            "token": f"<<{ph.token}>>",
            "kind": ph_kind,
            "original_text": ph.original_text,
            "assigned_name": ph.assigned_name,
            "replacement_text": replacement_text,
        })

    context = json.dumps({
        "hint_markers": [f"[HINT{i+1}_EXTRACTED]" for i in range(len(hint_items))],
        "placeholders": placeholder_info,
    }, ensure_ascii=False, indent=2)

    extra = ""
    if feedback:
        extra = (
            "\n\nThe previous output was invalid. Fix it strictly according to "
            "this validation feedback:\n" + feedback + "\n"
        )

    return (
        f"{base_prompt}{extra}\n\n"
        f"Placeholder and hint context:\n{context}\n\n"
        f"Problem text (with markers and placeholders):\n{problem_text}"
    )


def _run_theorem_construction(
    client: APIClient,
    masked_text: str,
    hint_items: List[Dict[str, str]],
    placeholders: List[Placeholder],
    exercise_label: str,
    *,
    max_tokens: int = 4096,
    max_attempts: int = 4,
    prompt_text: str | None = None,
) -> List[Dict[str, str]]:
    """Construct theorem statements from masked text.

    - Hint placeholders are deleted entirely.
    - Opt_prob / algo placeholders are replaced conservatively (prefer original text).
    - Natural-language repair should be minimal and source-faithful.
    - May split multi-part exercises into multiple theorems.

    Returns a list of dicts with 'content' key.
    """
    if prompt_text is None:
        prompt_text = load_prompt(PROMPT_NAMES["construct_theorem"])

    feedback = ""
    last_error = ""

    for _ in range(max_attempts):
        full_prompt = _build_theorem_prompt(
            prompt_text, masked_text, hint_items, placeholders, feedback,
        )
        try:
            response = client.chat(
                prompt=full_prompt,
                max_tokens=max_tokens,
                call_type="preprocess_construct_theorem",
                exercise_label=exercise_label,
                json_mode=True,
            )
        except Exception as err:
            last_error = f"API call failed: {err}"
            feedback = last_error
            continue

        try:
            candidate = extract_json_value(response)
        except Exception as err:
            last_error = str(err)
            feedback = f"JSON parsing failed: {err}"
            continue

        validation_error = _validate_theorem_output(candidate)
        if validation_error:
            last_error = validation_error
            feedback = validation_error
            continue

        return candidate["theorems"]

    raise RuntimeError(
        f"Theorem construction failed for {exercise_label} "
        f"after {max_attempts} attempts: {last_error}"
    )
