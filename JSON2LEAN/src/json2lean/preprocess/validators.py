"""Validation functions for each preprocessing stage."""

from __future__ import annotations

from typing import Any


def _validate_hint_output(candidate: Any) -> str:
    """Validate hint extraction output with indexed markers."""
    if not isinstance(candidate, dict):
        return "Output must be a JSON object with 'items' and 'masked_text' fields."
    if "items" not in candidate:
        return "Output must contain an 'items' field."
    if "masked_text" not in candidate:
        return "Output must contain a 'masked_text' field."
    if not isinstance(candidate["items"], list):
        return "'items' must be a list."
    if not isinstance(candidate["masked_text"], str):
        return "'masked_text' must be a string."

    for i, item in enumerate(candidate["items"]):
        if not isinstance(item, dict):
            return f"Item at index {i} must be a JSON object."
        if "id" not in item or "text" not in item:
            return f"Item at index {i} must have 'id' and 'text' fields."
        if not isinstance(item["id"], str) or not isinstance(item["text"], str):
            return f"Item at index {i}: 'id' and 'text' must be strings."
        if not item["text"].strip():
            return f"Item at index {i} has empty text."

    # Check that indexed markers appear in masked_text for each hint
    for i in range(len(candidate["items"])):
        marker = f"[HINT{i+1}_EXTRACTED]"
        if marker not in candidate["masked_text"]:
            return (
                f"Expected indexed marker {marker} in masked_text for hint "
                f"item {i} (id={candidate['items'][i]['id']})."
            )

    return ""


def _validate_masking_output(candidate: Any) -> str:
    """Validate special-block masking output with assigned names."""
    if not isinstance(candidate, dict):
        return "Output must be a JSON object."
    if "blocks" not in candidate:
        return "Output must contain a 'blocks' field."
    if "masked_text" not in candidate:
        return "Output must contain a 'masked_text' field."
    if not isinstance(candidate["blocks"], list):
        return "'blocks' must be a list."
    if not isinstance(candidate["masked_text"], str):
        return "'masked_text' must be a string."

    for i, block in enumerate(candidate["blocks"]):
        if not isinstance(block, dict):
            return f"Block at index {i} must be a JSON object."
        for key in ("token", "kind", "original_text", "assigned_name"):
            if key not in block:
                return f"Block at index {i} must have a '{key}' field."
            if not isinstance(block[key], str):
                return f"Block at index {i}: '{key}' must be a string."
        if block["kind"] not in ("optimization_problem", "algorithm"):
            return (
                f"Block at index {i}: 'kind' must be "
                f"'optimization_problem' or 'algorithm'."
            )
        if not block["assigned_name"].strip():
            return f"Block at index {i}: 'assigned_name' must be non-empty."
        placeholder = f"<<{block['token']}>>"
        if placeholder not in candidate["masked_text"]:
            return f"Placeholder {placeholder} not found in masked_text."

    return ""


def _validate_definition_output(candidate: Any) -> str:
    """Validate definition extraction output (no masking)."""
    if not isinstance(candidate, dict):
        return "Output must be a JSON object with an 'items' field."
    if "items" not in candidate:
        return "Output must contain an 'items' field."
    if not isinstance(candidate["items"], list):
        return "'items' must be a list."

    for i, item in enumerate(candidate["items"]):
        if not isinstance(item, dict):
            return f"Item at index {i} must be a JSON object."
        if "term" not in item:
            return f"Item at index {i} must have a 'term' field."
        if "definition" not in item:
            return f"Item at index {i} must have a 'definition' field."
        if not isinstance(item["term"], str) or not item["term"].strip():
            return f"Item at index {i}: 'term' must be a non-empty string."
        if not isinstance(item["definition"], str) or not item["definition"].strip():
            return f"Item at index {i}: 'definition' must be a non-empty string."
        # 'source' is optional but if present must be "in_text" or "standard"
        src = item.get("source")
        if src is not None and src not in ("in_text", "standard"):
            return f"Item at index {i}: 'source' must be 'in_text' or 'standard' (got '{src}')."

    return ""


def _validate_theorem_output(candidate: Any) -> str:
    """Validate theorem construction output."""
    if not isinstance(candidate, dict):
        return "Output must be a JSON object with a 'theorems' field."
    if "theorems" not in candidate:
        return "Output must contain a 'theorems' field."
    if not isinstance(candidate["theorems"], list):
        return "'theorems' must be a list."
    if len(candidate["theorems"]) == 0:
        return "At least one theorem must be produced."

    for i, thm in enumerate(candidate["theorems"]):
        if not isinstance(thm, dict):
            return f"Theorem at index {i} must be a JSON object."
        if "content" not in thm:
            return f"Theorem at index {i} must have a 'content' field."
        if not isinstance(thm["content"], str) or not thm["content"].strip():
            return f"Theorem at index {i}: 'content' must be a non-empty string."

    return ""


def _validate_normalize_output(candidate: Any, expected_count: int) -> str:
    """Validate normalization output."""
    if not isinstance(candidate, dict):
        return "Output must be a JSON object with a 'records' field."
    if "records" not in candidate:
        return "Output must contain a 'records' field."
    if not isinstance(candidate["records"], list):
        return "'records' must be a list."
    if len(candidate["records"]) != expected_count:
        return (
            f"Expected {expected_count} records, got {len(candidate['records'])}."
        )

    for i, rec in enumerate(candidate["records"]):
        if not isinstance(rec, dict):
            return f"Record at index {i} must be a JSON object."
        if "content" not in rec:
            return f"Record at index {i} must have a 'content' field."
        if not isinstance(rec["content"], str) or not rec["content"].strip():
            return f"Record at index {i}: 'content' must be a non-empty string."

    return ""
