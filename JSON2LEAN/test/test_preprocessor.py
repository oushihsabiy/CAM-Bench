"""Tests for the refactored preprocessor pipeline.

Tests cover:
  - indexed hint masking
  - opt_prob / algo extraction as standalone records (not definitions)
  - assigned naming for opt_prob / algo and placeholder replacement
  - defn extraction of only optimization-domain terms (no source text masking)
  - natural-language repair of theorem text
  - output written to preprocessed_data/<input_stem>.json in flat schema
  - downstream compatibility for new kind values (algo, hints, opt_prob)
"""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path
from typing import Any, Dict, List
from unittest.mock import MagicMock, patch

# Ensure local src/ is importable
_SRC = Path(__file__).resolve().parents[1] / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))

from json2lean.preprocess import (
    FlatRecord,
    MaskingResult,
    Placeholder,
    StageResult,
    _validate_hint_output,
    _validate_masking_output,
    _validate_definition_output,
    _validate_theorem_output,
    _validate_normalize_output,
    preprocess_exercise,
    preprocess_all,
    reindex_records,
)
from json2lean.models import Exercise, Block, StructuredExercise
from json2lean.semantic.declaration_policy import validate_top_level_contract
from json2lean.translater import _kind_hint


# =====================================================================
# 1. Indexed hint masking validation
# =====================================================================

class TestIndexedHintMasking:

    def test_valid_single_hint(self):
        candidate = {
            "items": [{"id": "1", "text": "Try using the triangle inequality"}],
            "masked_text": "Problem text [HINT1_EXTRACTED] remainder.",
        }
        assert _validate_hint_output(candidate) == ""

    def test_valid_multiple_hints(self):
        candidate = {
            "items": [
                {"id": "1", "text": "Hint one"},
                {"id": "2", "text": "Hint two"},
                {"id": "3", "text": "Hint three"},
            ],
            "masked_text": "A [HINT1_EXTRACTED] B [HINT2_EXTRACTED] C [HINT3_EXTRACTED]",
        }
        assert _validate_hint_output(candidate) == ""

    def test_missing_indexed_marker(self):
        candidate = {
            "items": [
                {"id": "1", "text": "Hint one"},
                {"id": "2", "text": "Hint two"},
            ],
            "masked_text": "A [HINT1_EXTRACTED] B",  # Missing HINT2
        }
        err = _validate_hint_output(candidate)
        assert "HINT2_EXTRACTED" in err

    def test_old_non_indexed_marker_rejected(self):
        """Old-style [HINT_EXTRACTED] should be rejected for indexed output."""
        candidate = {
            "items": [{"id": "1", "text": "Hint one"}],
            "masked_text": "A [HINT_EXTRACTED] B",  # Non-indexed marker
        }
        err = _validate_hint_output(candidate)
        assert "HINT1_EXTRACTED" in err

    def test_empty_hints_valid(self):
        candidate = {
            "items": [],
            "masked_text": "Unchanged text",
        }
        assert _validate_hint_output(candidate) == ""

    def test_empty_text_rejected(self):
        candidate = {
            "items": [{"id": "1", "text": ""}],
            "masked_text": "[HINT1_EXTRACTED]",
        }
        err = _validate_hint_output(candidate)
        assert "empty text" in err


# =====================================================================
# 2. Opt_prob / algo extraction as standalone records
# =====================================================================

class TestSpecialBlockExtraction:

    def test_valid_masking_output_with_names(self):
        candidate = {
            "blocks": [
                {
                    "token": "OPT_PROBLEM_1",
                    "kind": "optimization_problem",
                    "original_text": "minimize f(x) subject to g(x) <= 0",
                    "assigned_name": "constrained convex program",
                },
                {
                    "token": "ALGORITHM_1",
                    "kind": "algorithm",
                    "original_text": "Step 1: initialize x_0...",
                    "assigned_name": "projected gradient descent",
                },
            ],
            "masked_text": "Consider <<OPT_PROBLEM_1>> and <<ALGORITHM_1>>.",
        }
        assert _validate_masking_output(candidate) == ""

    def test_missing_assigned_name(self):
        candidate = {
            "blocks": [{
                "token": "OPT_PROBLEM_1",
                "kind": "optimization_problem",
                "original_text": "min f(x)",
                # missing assigned_name
            }],
            "masked_text": "<<OPT_PROBLEM_1>>",
        }
        err = _validate_masking_output(candidate)
        assert "assigned_name" in err

    def test_empty_assigned_name(self):
        candidate = {
            "blocks": [{
                "token": "OPT_PROBLEM_1",
                "kind": "optimization_problem",
                "original_text": "min f(x)",
                "assigned_name": "  ",
            }],
            "masked_text": "<<OPT_PROBLEM_1>>",
        }
        err = _validate_masking_output(candidate)
        assert "non-empty" in err

    def test_placeholder_position_tracking(self):
        ph = Placeholder(
            token="OPT_PROBLEM_1",
            kind="optimization_problem",
            original_text="minimize f(x)",
            assigned_name="convex program",
            source_position=42,
        )
        assert ph.assigned_name == "convex program"
        assert ph.source_position == 42


# =====================================================================
# 3. Assigned naming and placeholder replacement in theorem text
# =====================================================================

class TestAssignedNaming:

    def test_flat_record_with_term(self):
        rec = FlatRecord(
            index=0, source="test", source_idx="Ex 1",
            kind="opt_prob",
            content="minimize f(x) subject to g(x) <= 0",
            term="constrained convex program",
        )
        d = rec.to_dict()
        assert d["kind"] == "opt_prob"
        assert d["term"] == "constrained convex program"
        assert "content" in d

    def test_algo_record_with_term(self):
        rec = FlatRecord(
            index=1, source="test", source_idx="Ex 1",
            kind="algo",
            content="Step 1: initialize...",
            term="barrier method",
        )
        d = rec.to_dict()
        assert d["kind"] == "algo"
        assert d["term"] == "barrier method"

    def test_term_omitted_when_empty(self):
        rec = FlatRecord(
            index=0, source="test", source_idx="Ex 1",
            kind="thm", content="Let x ...", term="",
        )
        d = rec.to_dict()
        assert "term" not in d


# =====================================================================
# 4. Definition extraction: optimization-domain terms only
# =====================================================================

class TestDefinitionExtraction:

    def test_valid_definition_output(self):
        candidate = {
            "items": [
                {
                    "term": "strongly convex",
                    "definition": "A function f is strongly convex with parameter m > 0 if ...",
                },
            ],
        }
        assert _validate_definition_output(candidate) == ""

    def test_empty_term_rejected(self):
        candidate = {
            "items": [{"term": "", "definition": "some def"}],
        }
        err = _validate_definition_output(candidate)
        assert "non-empty" in err

    def test_empty_definition_rejected(self):
        candidate = {
            "items": [{"term": "convex", "definition": ""}],
        }
        err = _validate_definition_output(candidate)
        assert "non-empty" in err

    def test_missing_term_field(self):
        candidate = {
            "items": [{"definition": "some definition text"}],
        }
        err = _validate_definition_output(candidate)
        assert "term" in err

    def test_no_items_valid(self):
        candidate = {"items": []}
        assert _validate_definition_output(candidate) == ""


# =====================================================================
# 5. Theorem construction validation
# =====================================================================

class TestTheoremConstruction:

    def test_valid_single_theorem(self):
        candidate = {
            "theorems": [{"content": "Let x in R^n. Prove that f(x) >= 0."}],
        }
        assert _validate_theorem_output(candidate) == ""

    def test_valid_multi_part(self):
        candidate = {
            "theorems": [
                {"content": "Part a: Let ... Then ..."},
                {"content": "Part b: Let ... Prove ..."},
            ],
        }
        assert _validate_theorem_output(candidate) == ""

    def test_empty_theorems_rejected(self):
        candidate = {"theorems": []}
        err = _validate_theorem_output(candidate)
        assert "at least one" in err.lower()

    def test_empty_content_rejected(self):
        candidate = {"theorems": [{"content": ""}]}
        err = _validate_theorem_output(candidate)
        assert "non-empty" in err


# =====================================================================
# 6. Output format: flat schema in preprocessed_data/
# =====================================================================

class TestOutputFormat:

    def test_flat_record_schema(self):
        rec = FlatRecord(
            index=5, source="book/Test", source_idx="Exercise 3.1",
            kind="thm", content="Let x in R. Then x^2 >= 0.",
        )
        d = rec.to_dict()
        assert d == {
            "index": 5,
            "source": "book/Test",
            "source_idx": "Exercise 3.1",
            "kind": "thm",
            "content": "Let x in R. Then x^2 >= 0.",
        }

    def test_flat_record_with_term_schema(self):
        rec = FlatRecord(
            index=3, source="book/Test", source_idx="Exercise 3.1",
            kind="defn", content="A function is convex if ...",
            term="convex function",
        )
        d = rec.to_dict()
        assert d["term"] == "convex function"
        assert d["kind"] == "defn"

    def test_reindex(self):
        records = [
            FlatRecord(index=99, source="", source_idx="", kind="thm", content="A"),
            FlatRecord(index=99, source="", source_idx="", kind="defn", content="B"),
        ]
        reindex_records(records, start=10)
        assert records[0].index == 10
        assert records[1].index == 11

    def test_all_kinds_present(self):
        """Verify all five canonical kinds can be represented."""
        kinds = ["thm", "defn", "opt_prob", "algo", "hints"]
        for k in kinds:
            r = FlatRecord(index=0, source="", source_idx="", kind=k, content="x")
            assert r.to_dict()["kind"] == k


# =====================================================================
# 7. Downstream compatibility: kind values
# =====================================================================

class TestDownstreamCompatibility:

    def test_kind_hint_algo(self):
        """Translator must handle 'algo' kind."""
        hint = _kind_hint("algo")
        assert "structure" in hint.lower()

    def test_kind_hint_alg_backward_compat(self):
        """Translator must still handle legacy 'alg' kind."""
        hint = _kind_hint("alg")
        assert "structure" in hint.lower()

    def test_kind_hint_opt_prob(self):
        """Translator must handle 'opt_prob' kind."""
        hint = _kind_hint("opt_prob")
        assert "def" in hint.lower()

    def test_kind_hint_hints_empty(self):
        """Translator must return empty string for 'hints' kind (not translated)."""
        hint = _kind_hint("hints")
        assert hint == ""

    def test_kind_hint_defn(self):
        hint = _kind_hint("defn")
        assert "def" in hint.lower()

    def test_kind_hint_thm(self):
        hint = _kind_hint("thm")
        assert "theorem" in hint.lower()

    def test_declaration_policy_algo(self):
        code = "structure MyAlgo where\n  step : Nat → Nat"
        assert validate_top_level_contract("algo", code) == ""

    def test_declaration_policy_algo_missing_structure(self):
        code = "def MyAlgo := 42"
        err = validate_top_level_contract("algo", code)
        assert "structure" in err

    def test_declaration_policy_opt_prob(self):
        code = "def optProblem := sorry"
        assert validate_top_level_contract("opt_prob", code) == ""

    def test_declaration_policy_opt_prob_missing_def(self):
        code = "theorem foo : True := trivial"
        err = validate_top_level_contract("opt_prob", code)
        assert "def" in err.lower()

    def test_declaration_policy_hints(self):
        """Hints kind should pass validation (no Lean output expected)."""
        assert validate_top_level_contract("hints", "") == ""

    def test_declaration_policy_thm_unchanged(self):
        code = "theorem foo : True := by sorry"
        assert validate_top_level_contract("thm", code) == ""


# =====================================================================
# 8. Normalization validation
# =====================================================================

class TestNormalization:

    def test_valid_normalize_output(self):
        candidate = {
            "records": [
                {"content": "Normalized theorem text."},
                {"content": "Normalized definition.", "term": "convex"},
            ],
        }
        assert _validate_normalize_output(candidate, 2) == ""

    def test_wrong_count(self):
        candidate = {"records": [{"content": "A"}]}
        err = _validate_normalize_output(candidate, 3)
        assert "Expected 3" in err

    def test_empty_content(self):
        candidate = {"records": [{"content": ""}]}
        err = _validate_normalize_output(candidate, 1)
        assert "non-empty" in err


# =====================================================================
# 9. Integration: preprocess_exercise with mocked API
# =====================================================================

def _make_mock_client(responses: Dict[str, Any]) -> MagicMock:
    """Create a mock APIClient that returns predefined responses by call_type."""
    client = MagicMock()
    call_count: Dict[str, int] = {}

    def mock_chat(prompt, max_tokens=4096, call_type="", exercise_label="", json_mode=False):
        call_count.setdefault(call_type, 0)
        call_count[call_type] += 1
        resp = responses.get(call_type)
        if resp is None:
            raise RuntimeError(f"No mock response for call_type={call_type}")
        return json.dumps(resp)

    client.chat = mock_chat
    return client


class TestPreprocessExerciseIntegration:

    def test_full_pipeline(self):
        """End-to-end test with mocked LLM responses."""
        exercise = Exercise(
            raw={
                "source": "book/Test",
                "source_idx": "Exercise 1.1",
                "problem": (
                    "Hint: you may use convexity. "
                    "Consider the following problem: minimize f(x) subject to x >= 0. "
                    "Show that the optimal value is attained."
                ),
            },
            index=1,
        )

        mock_responses = {
            "preprocess_hint": {
                "items": [{"id": "1", "text": "you may use convexity"}],
                "masked_text": (
                    "Hint: [HINT1_EXTRACTED] "
                    "Consider the following problem: minimize f(x) subject to x >= 0. "
                    "Show that the optimal value is attained."
                ),
            },
            "preprocess_masking": {
                "blocks": [{
                    "token": "OPT_PROBLEM_1",
                    "kind": "optimization_problem",
                    "original_text": "minimize f(x) subject to x >= 0",
                    "assigned_name": "constrained minimization problem",
                }],
                "masked_text": (
                    "Hint: [HINT1_EXTRACTED] "
                    "Consider the following problem: <<OPT_PROBLEM_1>>. "
                    "Show that the optimal value is attained."
                ),
            },
            "preprocess_definition": {
                "items": [],
            },
            "preprocess_construct_theorem": {
                "theorems": [{
                    "content": (
                        "Consider the constrained minimization problem. "
                        "Prove that the optimal value is attained."
                    ),
                }],
            },
        }

        client = _make_mock_client(mock_responses)
        records = preprocess_exercise(
            client, exercise,
            max_tokens=4096,
            max_attempts=1,
            normalize=False,
        )

        # Check records
        assert len(records) >= 2  # At least hint + opt_prob + thm
        kinds = [r.kind for r in records]
        assert "hints" in kinds
        assert "opt_prob" in kinds
        assert "thm" in kinds

        # Check hint record
        hint_recs = [r for r in records if r.kind == "hints"]
        assert len(hint_recs) == 1
        assert "convexity" in hint_recs[0].content

        # Check opt_prob record has term
        opt_recs = [r for r in records if r.kind == "opt_prob"]
        assert len(opt_recs) == 1
        assert opt_recs[0].term == "constrained minimization problem"

        # Check thm record content
        thm_recs = [r for r in records if r.kind == "thm"]
        assert len(thm_recs) == 1
        assert "constrained minimization problem" in thm_recs[0].content

        # Check backward compatibility
        assert exercise.structured is not None
        assert exercise.preprocessed_problem != ""
        # Hints should not appear in preprocessed_problem
        assert "HINTS:" not in exercise.preprocessed_problem

    def test_pipeline_with_definitions(self):
        """Test that defn items have correct schema."""
        exercise = Exercise(
            raw={
                "source": "book/Test",
                "source_idx": "Exercise 2.1",
                "problem": "A function is strongly convex if ... Show that ...",
            },
            index=2,
        )

        mock_responses = {
            "preprocess_hint": {
                "items": [],
                "masked_text": "A function is strongly convex if ... Show that ...",
            },
            "preprocess_masking": {
                "blocks": [],
                "masked_text": "A function is strongly convex if ... Show that ...",
            },
            "preprocess_definition": {
                "items": [{
                    "term": "strongly convex",
                    "definition": "A function f is strongly convex with parameter m > 0 if f(y) >= f(x) + ...",
                }],
            },
            "preprocess_construct_theorem": {
                "theorems": [{"content": "Let f be strongly convex. Then ..."}],
            },
        }

        client = _make_mock_client(mock_responses)
        records = preprocess_exercise(
            client, exercise,
            max_tokens=4096,
            max_attempts=1,
            normalize=False,
        )

        defn_recs = [r for r in records if r.kind == "defn"]
        assert len(defn_recs) == 1
        assert defn_recs[0].term == "strongly convex"
        assert "parameter m" in defn_recs[0].content


class TestPreprocessAllOutput:

    def test_writes_to_preprocessed_data(self):
        """Verify output is written to preprocessed_data/<stem>.json."""
        exercise = Exercise(
            raw={
                "source": "test",
                "source_idx": "Ex 1",
                "problem": "Simple problem.",
            },
            index=1,
        )

        mock_responses = {
            "preprocess_hint": {
                "items": [],
                "masked_text": "Simple problem.",
            },
            "preprocess_masking": {
                "blocks": [],
                "masked_text": "Simple problem.",
            },
            "preprocess_definition": {"items": []},
            "preprocess_construct_theorem": {
                "theorems": [{"content": "Let x. Then x = x."}],
            },
        }

        client = _make_mock_client(mock_responses)

        with tempfile.TemporaryDirectory() as tmpdir:
            output_dir = Path(tmpdir) / "preprocessed_data"
            failed = preprocess_all(
                client, [exercise],
                max_tokens=4096,
                max_attempts=1,
                normalize=False,
                output_dir=output_dir,
                input_stem="test_input",
            )

            assert failed == []
            output_path = output_dir / "test_input.json"
            assert output_path.exists()

            data = json.loads(output_path.read_text())
            assert isinstance(data, list)
            assert len(data) >= 1
            # Check flat record schema
            for rec in data:
                assert "index" in rec
                assert "source" in rec
                assert "source_idx" in rec
                assert "kind" in rec
                assert "content" in rec
                assert rec["kind"] in ("thm", "defn", "opt_prob", "algo", "hints")

    def test_output_indices_are_global_contiguous(self):
        """Output JSON should be globally reindexed as 1..N."""
        ex1 = Exercise(
            raw={"source": "test", "source_idx": "Ex A", "problem": "Problem A."},
            index=1,
        )
        ex2 = Exercise(
            raw={"source": "test", "source_idx": "Ex B", "problem": "Problem B."},
            index=2,
        )

        mock_responses = {
            "preprocess_hint": {"items": [], "masked_text": "Simple problem."},
            "preprocess_masking": {"blocks": [], "masked_text": "Simple problem."},
            "preprocess_definition": {"items": []},
            "preprocess_construct_theorem": {"theorems": [{"content": "Let x. Then x = x."}]},
        }
        client = _make_mock_client(mock_responses)

        with tempfile.TemporaryDirectory() as tmpdir:
            output_dir = Path(tmpdir) / "preprocessed_data"
            failed = preprocess_all(
                client,
                [ex1, ex2],
                max_tokens=4096,
                max_attempts=1,
                normalize=False,
                output_dir=output_dir,
                input_stem="test_reindex",
            )
            assert failed == []
            data = json.loads((output_dir / "test_reindex.json").read_text())
            indices = [int(rec["index"]) for rec in data]
            assert indices == list(range(1, len(data) + 1))


# =====================================================================
# Run all tests
# =====================================================================

if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))
