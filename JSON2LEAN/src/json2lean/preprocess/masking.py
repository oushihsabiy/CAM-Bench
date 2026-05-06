"""Stage 0b — Special-block extraction (opt_prob / algo) with name assignment."""

from __future__ import annotations

import sys
from typing import Dict, List

from ..config.api_client import APIClient, extract_json_value
from ..loader import load_prompt
from ._common import PROMPT_NAMES, build_stage_prompt
from .models import MaskingResult, Placeholder
from .validators import _validate_masking_output


def _run_masking_stage(
    client: APIClient,
    problem_text: str,
    exercise_label: str,
    *,
    max_tokens: int = 4096,
    max_attempts: int = 4,
    prompt_text: str | None = None,
) -> MaskingResult:
    """Identify opt probs and algorithms, assign names, replace with placeholders."""
    if prompt_text is None:
        prompt_text = load_prompt(PROMPT_NAMES["special_blocks"])

    feedback = ""
    last_error = ""

    for _ in range(max_attempts):
        full_prompt = build_stage_prompt(prompt_text, problem_text, feedback)
        try:
            response = client.chat(
                prompt=full_prompt,
                max_tokens=max_tokens,
                call_type="preprocess_masking",
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

        validation_error = _validate_masking_output(candidate)
        if validation_error:
            last_error = validation_error
            feedback = validation_error
            continue

        placeholders: List[Placeholder] = []
        for block in candidate["blocks"]:
            pos = problem_text.find(block["original_text"][:80])
            if pos == -1:
                pos = problem_text.lower().find(
                    block["original_text"][:40].lower()
                )
            if pos == -1:
                pos = 0
            placeholders.append(Placeholder(
                token=block["token"],
                kind=block["kind"],
                original_text=block["original_text"],
                assigned_name=block["assigned_name"],
                source_position=pos,
            ))

        return MaskingResult(
            masked_text=candidate["masked_text"],
            placeholders=placeholders,
        )

    # Graceful degradation
    print(
        f"[preprocess] WARNING: masking stage failed for {exercise_label} "
        f"after {max_attempts} attempts: {last_error}; using original text.",
        file=sys.stderr,
    )
    return MaskingResult(masked_text=problem_text, placeholders=[])
