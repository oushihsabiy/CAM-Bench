"""Stage 3 (optional) — Normalization to standard mathematical English."""

from __future__ import annotations

import json
import sys
from typing import Dict, List

from ..config.api_client import APIClient, extract_json_value
from ..loader import load_prompt
from ._common import PROMPT_NAMES
from .models import FlatRecord
from .validators import _validate_normalize_output


def _run_normalization(
    client: APIClient,
    records: List[FlatRecord],
    exercise_label: str,
    *,
    max_tokens: int = 4096,
    max_attempts: int = 4,
    prompt_text: str | None = None,
    normalize_skip_thm: bool = False,
) -> List[FlatRecord]:
    """Optional pass: normalize all records to standard mathematical English.

    On failure, returns original records unchanged.
    
    If normalize_skip_thm is True, skips normalization for records with kind="thm".
    """
    if prompt_text is None:
        try:
            prompt_text = load_prompt(PROMPT_NAMES["normalize"])
        except FileNotFoundError:
            return records

    # If normalize_skip_thm is True, normalize only non-theorem records.
    other_records = []
    
    if normalize_skip_thm:
        for i, rec in enumerate(records):
            if rec.kind != "thm":
                other_records.append((i, rec))

        # If all records are theorems, there is nothing to normalize here.
        if not other_records:
            return records

        records_to_normalize = other_records
    else:
        records_to_normalize = [(i, rec) for i, rec in enumerate(records)]

    # Build input JSON for records that need normalization
    input_records = [r.to_dict() for _, r in records_to_normalize]
    input_json = json.dumps(input_records, ensure_ascii=False, indent=2)

    feedback = ""
    last_error = ""

    for _ in range(max_attempts):
        extra = ""
        if feedback:
            extra = (
                "\n\nThe previous output was invalid. Fix it strictly according to "
                "this validation feedback:\n" + feedback + "\n"
            )
        full_prompt = f"{prompt_text}{extra}\n\n{input_json}"

        try:
            response = client.chat(
                prompt=full_prompt,
                max_tokens=max_tokens,
                call_type="preprocess_normalize",
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

        validation_error = _validate_normalize_output(candidate, len(records_to_normalize))
        if validation_error:
            last_error = validation_error
            feedback = validation_error
            continue

        # Apply normalized content back to records that were normalized
        for (orig_idx, rec), norm in zip(records_to_normalize, candidate["records"]):
            rec.content = norm["content"]
            if "term" in norm:
                rec.term = norm["term"]

        return records

    print(
        f"[preprocess] WARNING: normalization failed for {exercise_label} "
        f"after {max_attempts} attempts: {last_error}; keeping originals.",
        file=sys.stderr,
    )
    return records
