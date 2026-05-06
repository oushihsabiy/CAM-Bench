"""Stage 0a — Hint extraction with indexed markers."""

from __future__ import annotations

from typing import Dict, List

from ..config.api_client import APIClient, extract_json_value
from ..loader import load_prompt
from ._common import PROMPT_NAMES, build_stage_prompt
from .models import StageResult
from .validators import _validate_hint_output


def _run_hint_extraction(
    client: APIClient,
    problem_text: str,
    exercise_label: str,
    *,
    max_tokens: int = 4096,
    max_attempts: int = 4,
    prompt_text: str | None = None,
) -> StageResult:
    """Extract hints and return masked text with indexed markers."""
    if prompt_text is None:
        prompt_text = load_prompt(PROMPT_NAMES["hint"])

    feedback = ""
    last_error = ""

    for _ in range(max_attempts):
        full_prompt = build_stage_prompt(prompt_text, problem_text, feedback)
        try:
            response = client.chat(
                prompt=full_prompt,
                max_tokens=max_tokens,
                call_type="preprocess_hint",
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

        validation_error = _validate_hint_output(candidate)
        if validation_error:
            last_error = validation_error
            feedback = validation_error
            continue

        return StageResult(
            items=candidate["items"],
            masked_text=candidate["masked_text"],
        )

    raise RuntimeError(
        f"Hint extraction failed for {exercise_label} "
        f"after {max_attempts} attempts: {last_error}"
    )
