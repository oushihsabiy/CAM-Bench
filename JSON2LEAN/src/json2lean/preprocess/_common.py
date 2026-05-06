"""Shared utilities for preprocessing stages."""

from __future__ import annotations

# Mapping from internal stage keys to prompt template names.
PROMPT_NAMES = {
    "hint":              "extract_hint",
    "special_blocks":    "identify_special_blocks",
    "definition":        "extract_technical_term",
    "construct_theorem": "construct_theorem",
    "normalize":         "normalize_record",
}


def build_stage_prompt(base_prompt: str, text: str, feedback: str = "") -> str:
    """Build a prompt with optional retry feedback."""
    extra = ""
    if feedback:
        extra = (
            "\n\nThe previous output was invalid. Fix it strictly according to "
            "this validation feedback:\n" + feedback + "\n"
        )
    return f"{base_prompt}{extra}\n{text}"
