"""Preprocessing pipeline — flat-record extraction from raw math exercises.

Transforms raw math exercise JSON into per-input-file preprocessed JSON
under ``preprocessed_data/``, following a flat-record schema with kinds:
  ``thm``, ``defn``, ``opt_prob``, ``algo``, ``hints``.

Pipeline stages:
  Stage 0a: extract hints               → indexed hint-masked text
  Stage 0b: technical-term extraction    → optimization-domain terms (on hint-masked text)
  Stage 1:  special-block extraction     → opt_prob / algo with assigned names
  Stage 2:  theorem construction         → placeholder filling + NL repair
  Stage 3 (optional): normalization pass → standard mathematical English
"""

# Models
from .models import FlatRecord, MaskingResult, Placeholder, StageResult

# Validators
from .validators import (
    _validate_definition_output,
    _validate_hint_output,
    _validate_masking_output,
    _validate_normalize_output,
    _validate_theorem_output,
)

# Pipeline public API
from .pipeline import preprocess_all, preprocess_exercise, reindex_records

__all__ = [
    # Models
    "FlatRecord",
    "MaskingResult",
    "Placeholder",
    "StageResult",
    # Validators
    "_validate_hint_output",
    "_validate_masking_output",
    "_validate_definition_output",
    "_validate_theorem_output",
    "_validate_normalize_output",
    # Pipeline
    "preprocess_exercise",
    "preprocess_all",
    "reindex_records",
]
