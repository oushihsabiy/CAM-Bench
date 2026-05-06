"""Stage 0b — Technical-term extraction (optimization-domain terms, before special-block masking)."""

from __future__ import annotations

import sys
import re
from typing import Dict, List

from ..config.api_client import APIClient, extract_json_value
from ..loader import load_prompt
from ._common import PROMPT_NAMES, build_stage_prompt
from .validators import _validate_definition_output


_IGNORED_TERM_PATTERNS = [
    r"\bconvex set\b",
    r"\bpositive definite matrix\b",
    r"\bpositive semidefinite matrix\b",
    r"\bpositive semi-definite matrix\b",
    r"\bpsd matrix\b",
    r"\bpd matrix\b",
    r"\bhyperplane\b",
    r"\bhyperplanes\b",
    r"\bhyper-plan(e|es)\b",
    r"\bseparating hyperplane\b",
    r"\bsupporting hyperplane\b",
    r"\bboundary\b",
    r"\bboundaries\b",
    r"\bboundary point(s)?\b",
    r"\bboundary of\b",
    r"\bon the boundary\b",
    r"\bdisjoint\b",
    r"\bdisjoint sets?\b",
    r"\bpairwise disjoint\b",
    r"\bmutually disjoint\b",
    r"\bdisjointness\b",
    r"\bnon[- ]?overlapping\b",
    r"\bseparate(d)? sets?\b",
    r"凸集",
    r"正定矩阵",
    r"半正定矩阵",
    r"超平面",
    r"边界",
    r"不相交",
]


def _should_ignore_term(term: str) -> bool:
    t = str(term or "").strip().lower()
    if not t:
        return False
    return any(re.search(pat, t, flags=re.IGNORECASE) for pat in _IGNORED_TERM_PATTERNS)


def _run_definition_extraction(
    client: APIClient,
    problem_text: str,
    exercise_label: str,
    *,
    max_tokens: int = 4096,
    max_attempts: int = 4,
    prompt_text: str | None = None,
) -> List[Dict[str, str]]:
    """Extract optimization-domain technical term definitions.

    Returns a list of dicts with 'term' and 'definition' keys.
    Runs on hint-masked text (before special-block masking).
    """
    if prompt_text is None:
        prompt_text = load_prompt(PROMPT_NAMES["definition"])

    feedback = ""
    last_error = ""

    for _ in range(max_attempts):
        full_prompt = build_stage_prompt(prompt_text, problem_text, feedback)
        try:
            response = client.chat(
                prompt=full_prompt,
                max_tokens=max_tokens,
                call_type="preprocess_definition",
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

        validation_error = _validate_definition_output(candidate)
        if validation_error:
            last_error = validation_error
            feedback = validation_error
            continue

        items = [
            item for item in candidate["items"]
            if not _should_ignore_term(item.get("term", ""))
        ]
        return items

    # Graceful degradation
    print(
        f"[preprocess] WARNING: definition extraction failed for {exercise_label} "
        f"after {max_attempts} attempts: {last_error}; yielding no definitions.",
        file=sys.stderr,
    )
    return []
