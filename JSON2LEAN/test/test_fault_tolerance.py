"""Tests for fault-tolerance, failure reporting, and new pipeline behaviors."""
import sys
import json
import tempfile
from pathlib import Path

sys.path.insert(0, "src")

from json2lean.models import Exercise, ExerciseStatus
from postprocess.fault_tolerance import (
    annotate_lean_failure,
    comment_out_block,
    tag_preprocess_failure,
    tag_semantic_not_usable,
    tag_translation_failure,
    tag_unrecoverable,
)
from postprocess.failure_report import append_failure_event, export_failure_reports
from postprocess.redundancy_cleanup import cleanup_redundancies
from utils.compile_logger import log_compile_result, read_compile_logs
from utils.error_analyzer import normalize_error_message, analyze_errors


# ---------------------------------------------------------------------------
# Sample Lean file with blocks
# ---------------------------------------------------------------------------

SAMPLE_LEAN = """\
import Mathlib

noncomputable section

namespace Exercise_5_2

/- [BLOCK Exercise_5_2 | 1 | defn]
Some definition.
-/
def AConjugate (A : Matrix n n ℝ) (p q : n → ℝ) : Prop :=
  dotProduct p (A.mulVec q) = 0

/- [BLOCK Exercise_5_2 | 2 | thm]
Some theorem.
-/
theorem myThm : True := by trivial

end Exercise_5_2
"""


# ---------------------------------------------------------------------------
# Test: annotate_lean_failure
# ---------------------------------------------------------------------------

def test_annotate_lean_failure():
    result = annotate_lean_failure(
        SAMPLE_LEAN,
        "Exercise_5_2|2|thm",
        phase="compile",
        failure_type="repair_exhausted",
        message="Could not fix type mismatch after 8 attempts",
    )
    assert "⚠️ PIPELINE FAILURE" in result
    assert "repair_exhausted" in result
    assert "COMMENTED OUT" in result
    # Original code should be commented
    assert "-- theorem myThm" in result
    print("test_annotate_lean_failure: PASSED")


# ---------------------------------------------------------------------------
# Test: comment_out_block
# ---------------------------------------------------------------------------

def test_comment_out_block():
    result = comment_out_block(SAMPLE_LEAN, "Exercise_5_2|2|thm")
    assert "⚠️ BLOCK UNRECOVERABLE" in result
    assert "COMMENTED OUT" in result
    assert "-- theorem myThm" in result
    # Block header preserved
    assert "/- [BLOCK Exercise_5_2 | 2 | thm]" in result
    print("test_comment_out_block: PASSED")


# ---------------------------------------------------------------------------
# Test: preprocessing failure tagging
# ---------------------------------------------------------------------------

def test_tag_preprocess_failure():
    ex = Exercise(raw={"source_idx": "ch5", "index": 1}, index=1, label="ch5_1")
    err = ValueError("Invalid JSON structure in exercise")
    tag_preprocess_failure(ex, err, phase="preprocess")

    assert ex.status == ExerciseStatus.ERROR
    assert ex.failure_type == "preprocess"
    assert "Invalid JSON" in ex.failure_message
    assert len(ex.errors) == 1
    assert "[preprocess]" in ex.errors[0]["message"]
    print("test_tag_preprocess_failure: PASSED")


# ---------------------------------------------------------------------------
# Test: translation failure tagging
# ---------------------------------------------------------------------------

def test_tag_translation_failure():
    ex = Exercise(raw={"source_idx": "ch5", "index": 2}, index=2, label="ch5_2")
    err = RuntimeError("API timeout")
    tag_translation_failure(ex, err)

    assert ex.status == ExerciseStatus.ERROR
    assert ex.failure_type == "translation"
    assert "API timeout" in ex.failure_message
    print("test_tag_translation_failure: PASSED")


# ---------------------------------------------------------------------------
# Test: unrecoverable tagging
# ---------------------------------------------------------------------------

def test_tag_unrecoverable():
    ex = Exercise(raw={"source_idx": "ch5", "index": 3}, index=3, label="ch5_3")
    tag_unrecoverable(
        ex, phase="compile",
        message="8 attempts exhausted",
        errors=[{"line": 10, "column": 5, "message": "type mismatch"}],
    )

    assert ex.status == ExerciseStatus.UNRECOVERABLE
    assert ex.failure_type == "compile"
    assert "exhausted" in ex.failure_message
    assert len(ex.errors) == 1
    print("test_tag_unrecoverable: PASSED")


# ---------------------------------------------------------------------------
# Test: semantic max-round failure tagging + realtime event
# ---------------------------------------------------------------------------

def test_semantic_not_usable_realtime_event():
    ex = Exercise(
        raw={"source_idx": "Exercise 2.8-(d)", "index": 8, "kind": "thm"},
        index=8,
        label="Exercise 2.8-(d)_thm_8",
    )
    tag_semantic_not_usable(
        ex,
        passes=8,
        max_rounds=8,
        last_status="not_usable_yet",
    )

    assert ex.status == ExerciseStatus.REPAIR_FAILED
    assert ex.failure_type == "semantic"
    assert ex.failure_phase == "semantic_not_usable_after_max_rounds"
    assert ex.repair_attempts == 8
    assert "[semantic]" in ex.errors[0]["message"]

    with tempfile.TemporaryDirectory() as tmpdir:
        path = append_failure_event(
            ex,
            tmpdir,
            event="semantic_not_usable_after_max_rounds",
            lean_file="/tmp/out.lean",
            extra={"block_id": "Exercise 2.8-(d)|8|thm", "passes": 8, "max_rounds": 8},
        )
        assert path is not None
        row = json.loads(Path(path).read_text(encoding="utf-8").strip())
        assert row["event"] == "semantic_not_usable_after_max_rounds"
        assert row["lean_file"] == "/tmp/out.lean"
        assert row["exercise"]["failure_type"] == "semantic"
        assert row["exercise"]["source_idx"] == "Exercise 2.8-(d)"
        assert row["exercise"]["kind"] == "thm"
        assert row["extra"]["block_id"] == "Exercise 2.8-(d)|8|thm"
    print("test_semantic_not_usable_realtime_event: PASSED")


# ---------------------------------------------------------------------------
# Test: failure report export
# ---------------------------------------------------------------------------

def test_failure_report_export():
    exercises = [
        Exercise(raw={"source_idx": "ch5", "index": 1}, index=1, label="ch5_1"),
        Exercise(raw={"source_idx": "ch5", "index": 2}, index=2, label="ch5_2"),
        Exercise(raw={"source_idx": "ch5", "index": 3}, index=3, label="ch5_3"),
    ]
    exercises[0].status = ExerciseStatus.VALID
    exercises[1].status = ExerciseStatus.ERROR
    exercises[1].failure_type = "translation"
    exercises[1].failure_message = "API timeout"
    exercises[2].status = ExerciseStatus.UNRECOVERABLE
    exercises[2].failure_type = "compile"
    exercises[2].failure_message = "Exhausted retries"

    with tempfile.TemporaryDirectory() as tmpdir:
        paths = export_failure_reports(exercises, tmpdir, date_str="20260416")
        assert len(paths) >= 2  # at least one per type + summary

        # Check files exist and are valid JSON
        for p in paths:
            assert p.exists()
            data = json.loads(p.read_text())
            assert isinstance(data, dict)

        # Check type-specific files
        names = [p.name for p in paths]
        assert "20260416_translation.json" in names
        assert "20260416_compile.json" in names
        assert "20260416_summary.json" in names

        # Check summary content
        summary = json.loads((Path(tmpdir) / "20260416_summary.json").read_text())
        assert summary["total_failed"] == 2
        assert summary["by_type"]["translation"] == 1
        assert summary["by_type"]["compile"] == 1

    print("test_failure_report_export: PASSED")


# ---------------------------------------------------------------------------
# Test: redundancy cleanup
# ---------------------------------------------------------------------------

def test_redundancy_cleanup():
    text = """\
import Mathlib
import Mathlib
import Mathlib

noncomputable section

namespace ch5

open Finset
open Finset

variable (n : ℕ)
variable (n : ℕ)

def foo := 1

end ch5
"""
    cleaned, removals = cleanup_redundancies(text)
    assert removals >= 3  # 1 import + 1 open + 1 variable
    assert cleaned.count("import Mathlib") == 1
    assert cleaned.count("open Finset") == 1
    assert cleaned.count("variable (n : ℕ)") == 1
    print(f"test_redundancy_cleanup: PASSED (removed {removals})")


# ---------------------------------------------------------------------------
# Test: compile error logging
# ---------------------------------------------------------------------------

def test_compile_error_logging():
    with tempfile.TemporaryDirectory() as tmpdir:
        log_dir = Path(tmpdir)
        log_compile_result(
            lean_file="ch5.lean",
            returncode=1,
            errors=[{"line": 10, "column": 5, "message": "type mismatch"}],
            warnings=[],
            run_label="test_run",
            log_dir=str(log_dir),
        )
        log_compile_result(
            lean_file="ch5.lean",
            returncode=0,
            errors=[],
            warnings=[{"line": 5, "column": 0, "message": "unused variable"}],
            run_label="test_run_2",
            log_dir=str(log_dir),
        )

        entries = read_compile_logs(str(log_dir))
        assert len(entries) == 2
        assert entries[0]["returncode"] == 1
        assert entries[0]["num_errors"] == 1
        assert entries[1]["returncode"] == 0
    print("test_compile_error_logging: PASSED")


# ---------------------------------------------------------------------------
# Test: error normalization and clustering
# ---------------------------------------------------------------------------

def test_error_normalization():
    msg1 = "/path/to/ch5.lean:10:5: error: type mismatch"
    msg2 = "/other/path/ch7.lean:20:3: error: type mismatch"
    n1 = normalize_error_message(msg1)
    n2 = normalize_error_message(msg2)
    assert n1 == n2  # same after normalization
    print(f"test_error_normalization: PASSED ('{n1}')")


def test_error_analyzer_full():
    with tempfile.TemporaryDirectory() as tmpdir:
        log_dir = Path(tmpdir)
        # Log multiple errors
        for i in range(5):
            log_compile_result(
                lean_file="ch5.lean",
                returncode=1,
                errors=[{"line": 10 + i, "column": 5, "message": "type mismatch in application"}],
                warnings=[],
                log_dir=str(log_dir),
            )
        for i in range(3):
            log_compile_result(
                lean_file="ch7.lean",
                returncode=1,
                errors=[{"line": 20 + i, "column": 3, "message": "unknown identifier 'xyz'"}],
                warnings=[],
                log_dir=str(log_dir),
            )

        results = analyze_errors(str(log_dir), top_n=10)
        assert len(results) >= 1
        assert results[0]["total_count"] >= 3
        assert results[0]["rank"] == 1
        assert len(results[0]["examples"]) >= 1
    print(f"test_error_analyzer_full: PASSED ({len(results)} categories)")


# ---------------------------------------------------------------------------
# Test: non-stop execution simulation
# ---------------------------------------------------------------------------

def test_nonstop_execution():
    """Verify that the pipeline structure never sets halted=True."""
    main_py = Path("main.py").read_text(encoding="utf-8")
    assert "halted = True" not in main_py, "Pipeline still has halted=True breakpoints"
    assert "halted" not in main_py or "halted" in main_py.split("# ------------------------------------------------------------------")[0] == False
    print("test_nonstop_execution: PASSED (no halt breakpoints)")


# ---------------------------------------------------------------------------
# Run all tests
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    test_annotate_lean_failure()
    test_comment_out_block()
    test_tag_preprocess_failure()
    test_tag_translation_failure()
    test_tag_unrecoverable()
    test_semantic_not_usable_realtime_event()
    test_failure_report_export()
    test_redundancy_cleanup()
    test_compile_error_logging()
    test_error_normalization()
    test_error_analyzer_full()
    test_nonstop_execution()
    print("\n✅ All fault-tolerance tests PASSED!")
