"""Fault-tolerance helpers for the json2lean pipeline.

Provides utilities to:
- Comment out unrecoverable sections in Lean files so downstream compilation
  is not broken.
- Annotate Lean output with failure markers.
- Record preprocessing failures into exercise JSON data.
"""

from __future__ import annotations

import re
import traceback
from pathlib import Path
from typing import Any, Dict, List

from json2lean.models import Exercise, ExerciseStatus


# ---------------------------------------------------------------------------
# Lean failure annotation
# ---------------------------------------------------------------------------

_LEAN_FAILURE_TEMPLATE = """\
/- ⚠️ PIPELINE FAILURE — {block_id}
   phase   : {phase}
   type    : {failure_type}
   message : {message}
   This block was skipped due to an unrecoverable error.
-/
-- [COMMENTED OUT: {block_id}]
{commented_code}
-- [END COMMENTED OUT: {block_id}]"""


def annotate_lean_failure(
    full_text: str,
    block_id: str,
    *,
    phase: str = "",
    failure_type: str = "",
    message: str = "",
) -> str:
    """Replace the code region of *block_id* with a failure annotation comment.

    The original code is commented out line-by-line (prefixed with ``-- ``)
    so the file remains syntactically valid.
    """
    from json2lean.block_parser import extract_block_by_id, replace_block_code

    code_data = extract_block_by_id(full_text, block_id)
    if code_data is None:
        return full_text

    original_code = code_data[0]
    commented_lines = "\n".join(
        f"-- {line}" if line.strip() else ""
        for line in original_code.splitlines()
    )
    annotation = _LEAN_FAILURE_TEMPLATE.format(
        block_id=block_id,
        phase=phase,
        failure_type=failure_type,
        message=_escape_lean_comment(message[:500]),
        commented_code=commented_lines,
    )
    updated, _ = replace_block_code(full_text, block_id, annotation)
    return updated


def comment_out_section(full_text: str, section_name: str) -> str:
    """Comment out the body of a named namespace in the Lean file.

    Preserves ``namespace X`` / ``end X`` markers but wraps the body in
    ``/- … -/`` so it does not cause downstream compilation errors.
    """
    open_pat = re.compile(
        rf"(?m)^(namespace\s+{re.escape(section_name)}\s*)$"
    )
    close_pat = re.compile(
        rf"(?m)^(end\s+{re.escape(section_name)}\s*)$"
    )
    open_m = open_pat.search(full_text)
    if open_m is None:
        return full_text
    body_start = open_m.end()
    close_m = close_pat.search(full_text, body_start)
    if close_m is None:
        return full_text

    body = full_text[body_start:close_m.start()]
    # Line-comment the body to avoid nested /- -/ issues
    commented_body = "\n".join(
        f"-- {line}" if line.strip() else ""
        for line in body.splitlines()
    )
    marker = (
        f"\n/- ⚠️ SECTION COMMENTED OUT: {section_name}\n"
        f"   Reason: unrecoverable compile errors in this section.\n-/\n"
    )
    return (
        full_text[:body_start]
        + marker
        + commented_body
        + "\n"
        + full_text[close_m.start():]
    )


def comment_out_block(full_text: str, block_id: str) -> str:
    """Comment out only the code region of a single block.

    The block comment header is preserved; the code body is replaced with
    line-commented version preceded by a failure marker.
    """
    from json2lean.block_parser import extract_block_by_id, replace_block_code

    code_data = extract_block_by_id(full_text, block_id)
    if code_data is None:
        return full_text

    original_code = code_data[0]
    commented_lines = "\n".join(
        f"-- {line}" if line.strip() else ""
        for line in original_code.splitlines()
    )
    replacement = (
        f"/- ⚠️ BLOCK UNRECOVERABLE: {block_id} -/\n"
        f"-- [COMMENTED OUT: {block_id}]\n"
        f"{commented_lines}\n"
        f"-- [END COMMENTED OUT: {block_id}]"
    )
    updated, _ = replace_block_code(full_text, block_id, replacement)
    return updated


# ---------------------------------------------------------------------------
# Preprocessing failure tagging
# ---------------------------------------------------------------------------

def tag_preprocess_failure(
    exercise: Exercise,
    error: Exception,
    *,
    phase: str = "preprocess",
) -> None:
    """Record a preprocessing failure directly in the exercise's metadata."""
    exercise.status = ExerciseStatus.ERROR
    exercise.failure_type = phase
    exercise.failure_phase = phase
    exercise.failure_message = str(error)
    exercise.failure_exception = traceback.format_exception_only(type(error), error)[-1].strip()
    exercise.errors.append({
        "line": 0,
        "column": 0,
        "message": f"[{phase}] {error}",
        "line_content": "",
        "char_at_column": "",
    })


def tag_translation_failure(
    exercise: Exercise,
    error: Exception,
) -> None:
    """Record a translation failure."""
    exercise.status = ExerciseStatus.ERROR
    exercise.failure_type = "translation"
    exercise.failure_phase = "translate_llm"
    exercise.failure_message = str(error)
    exercise.failure_exception = traceback.format_exception_only(type(error), error)[-1].strip()
    exercise.errors.append({
        "line": 0,
        "column": 0,
        "message": f"[translation] {error}",
        "line_content": "",
        "char_at_column": "",
    })


def tag_unrecoverable(
    exercise: Exercise,
    *,
    phase: str = "compile",
    message: str = "",
    errors: list | None = None,
) -> None:
    """Mark an exercise as unrecoverable with detailed context."""
    exercise.status = ExerciseStatus.UNRECOVERABLE
    exercise.failure_type = phase
    exercise.failure_phase = f"{phase}_repair_exhausted"
    exercise.failure_message = message or "Repair attempts exhausted"
    if errors:
        exercise.errors = list(errors)


def tag_semantic_not_usable(
    exercise: Exercise,
    *,
    passes: int,
    max_rounds: int,
    last_status: str = "",
    phase: str = "semantic_not_usable_after_max_rounds",
    message: str = "",
) -> None:
    """Record a semantic loop that exited without becoming usable."""
    status = last_status or "unknown"
    if not message:
        message = (
            f"semantic review remained {status!r} after {passes} pass(es) "
            f"(max_rounds={max_rounds})"
        )
    exercise.status = ExerciseStatus.REPAIR_FAILED
    exercise.failure_type = "semantic"
    exercise.failure_phase = phase
    exercise.failure_message = message
    exercise.failure_exception = ""
    exercise.repair_attempts = max(int(exercise.repair_attempts or 0), int(passes))
    synthetic_error = {
        "line": 0,
        "column": 0,
        "message": f"[semantic] {message}",
        "line_content": "",
        "char_at_column": "",
    }
    exercise.errors = [synthetic_error] + list(exercise.errors or [])[:9]


# ---------------------------------------------------------------------------
# Internal
# ---------------------------------------------------------------------------

def _escape_lean_comment(text: str) -> str:
    """Escape text for embedding inside a /- -/ Lean comment."""
    return text.replace("/-", "/ -").replace("-/", "- /")
