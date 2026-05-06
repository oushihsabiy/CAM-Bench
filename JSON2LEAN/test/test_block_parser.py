"""Tests for src/json2lean/block_parser.py — the block-comment parser."""
import sys
sys.path.insert(0, "src")

from json2lean.block_parser import (
    generate_block_comment,
    block_id_for,
    parse_blocks,
    extract_block_by_id,
    dedupe_block_code_against_frozen,
    replace_block_code,
    frozen_context_before,
    frozen_context_in_section,
    insert_block_comment,
    insert_code_after_comment,
    extract_block_comment_and_code,
    BlockSpan,
)


# ── generate_block_comment / block_id_for ─────────────────────────────

def test_generate_block_comment_defn():
    raw = {"source_idx": "Chp2", "index": 3, "kind": "defn", "content": "Let f(x) = x^2."}
    comment = generate_block_comment(raw)
    assert comment.startswith("/- [BLOCK")
    assert "Chp2" in comment
    assert "3" in comment
    assert "defn" in comment
    assert "Let f(x) = x^2." in comment
    assert comment.endswith("-/")


def test_block_id_for():
    raw = {"source_idx": "Chp2", "index": 3, "kind": "defn"}
    bid = block_id_for(raw)
    assert bid == "Chp2|3|defn"


def test_block_id_for_defaults():
    raw = {}
    bid = block_id_for(raw)
    assert "|" in bid


# ── parse_blocks ──────────────────────────────────────────────────────

SAMPLE = """\
import Mathlib
noncomputable section

namespace Chp2

/- [BLOCK Chp2 | 1 | defn]
Definition of f.
-/
def f (x : ℝ) : ℝ := x ^ 2

/- [BLOCK Chp2 | 2 | thm]
Theorem about f.
-/
theorem f_nonneg (x : ℝ) : f x ≥ 0 := by sorry

end Chp2
"""


def test_parse_blocks_count():
    blocks = parse_blocks(SAMPLE)
    assert len(blocks) == 2
    assert blocks[0].block_id == "Chp2|1|defn"
    assert blocks[1].block_id == "Chp2|2|thm"


def test_parse_blocks_positions():
    blocks = parse_blocks(SAMPLE)
    b = blocks[0]
    assert SAMPLE[b.comment_start:b.comment_end].startswith("/- [BLOCK")
    assert SAMPLE[b.comment_start:b.comment_end].endswith("-/")


def test_parse_blocks_multiline_header():
    sample = """\
import Mathlib

namespace ChpX

/-
[BLOCK ChpX | 1 | defn]
First.
-/
def a : Prop := True

/-
[BLOCK ChpX | 2 | thm]
Second.
-/
theorem b : True := by
  trivial

end ChpX
"""
    blocks = parse_blocks(sample)
    assert len(blocks) == 2
    assert blocks[0].block_id == "ChpX|1|defn"
    assert blocks[1].block_id == "ChpX|2|thm"
    code1 = extract_block_by_id(sample, "ChpX|1|defn")
    code2 = extract_block_by_id(sample, "ChpX|2|thm")
    assert code1 is not None and "def a" in code1[0]
    assert code2 is not None and "theorem b" in code2[0]


def test_extract_block_by_id():
    result = extract_block_by_id(SAMPLE, "Chp2|1|defn")
    assert result is not None
    code, start, end = result
    assert "def f" in code


def test_extract_block_by_id_missing():
    result = extract_block_by_id(SAMPLE, "nonexistent")
    assert result is None


# ── replace_block_code ────────────────────────────────────────────────

def test_replace_block_code():
    new_code = "def f (x : ℝ) : ℝ := x ^ 3"
    updated, stats = replace_block_code(SAMPLE, "Chp2|1|defn", new_code)
    assert "x ^ 3" in updated
    assert "x ^ 2" not in updated
    # Second block should be untouched
    assert "f_nonneg" in updated
    assert stats["removed_declarations"] == 0
    assert stats["removed_lines"] == 0


def test_replace_block_code_with_dedup():
    """Test that replace_block_code dedups when frozen_context is provided."""
    new_code = "def f (x : ℝ) : ℝ := x ^ 3\ndef g (x : ℝ) := x + 1"
    # Provide the first block as frozen context (contains "def f")
    frozen = SAMPLE[:SAMPLE.find("-- Chp2|2|thm")]
    updated, stats = replace_block_code(
        SAMPLE, "Chp2|2|thm", new_code, frozen_context=frozen
    )
    # The "def f" in new_code should be removed by dedup
    assert stats["removed_declarations"] > 0
    # "def g" should remain
    assert "def g" in updated


def test_dedupe_guard_keeps_related_declaration():
    frozen = "def strongWolfe_armijo : Prop := True"
    current = "def strongWolfe_armijo : Prop := False\ndef helper : Prop := True"

    kept, stats = dedupe_block_code_against_frozen(
        current,
        frozen,
        keep_if_related=lambda kind, chunk: kind == "declaration" and "strongWolfe_armijo" in chunk,
    )

    assert "def strongWolfe_armijo" in kept
    assert "def helper" in kept
    assert stats["removed_declarations"] == 0


def test_dedupe_guard_allows_unrelated_declaration_removal():
    frozen = "def duplicatedDecl : Prop := True"
    current = "def duplicatedDecl : Prop := False\ndef helper : Prop := True"

    cleaned, stats = dedupe_block_code_against_frozen(
        current,
        frozen,
        keep_if_related=lambda kind, chunk: False,
    )

    assert "def duplicatedDecl" not in cleaned
    assert "def helper" in cleaned
    assert stats["removed_declarations"] == 1


def test_replace_block_code_keeps_same_name_in_other_namespace():
    """Integration: section-scoped context should not remove same name from another namespace."""
    text = """\
import Mathlib

namespace A

/- [BLOCK Chp4 | 1 | defn]
A block.
-/
def dual : Prop := True

end A

namespace B

/- [BLOCK Chp4 | 2 | defn]
B block.
-/
def old_name : Prop := True

end B
"""
    block_id = "Chp4|2|defn"
    section_ctx = frozen_context_in_section(text, block_id, "B")
    updated, stats = replace_block_code(
        text,
        block_id,
        "def dual : Prop := False",
        frozen_context=section_ctx,
    )
    assert "namespace B" in updated
    assert "def dual : Prop := False" in updated
    assert stats["removed_declarations"] == 0


def test_frozen_context_in_section_missing_namespace_returns_empty_context():
    """When namespace lookup fails, dedupe context should be empty (no cross-namespace fallback)."""
    text = """\
import Mathlib

namespace A

/- [BLOCK Chp2 | 1 | defn]
First block.
-/
def dual : Prop := True

end A
"""
    ctx = frozen_context_in_section(text, "Chp2|1|defn", "NonExistent")
    assert ctx == ""


def test_dedupe_same_namespace_duplicate_still_removed():
    """Regression: true duplicates in the same namespace should still be removed."""
    frozen = """\
namespace A
def helper : Prop := True
end A
"""
    current = """\
namespace A
def helper : Prop := False
def fresh : Prop := True
end A
"""
    cleaned, stats = dedupe_block_code_against_frozen(current, frozen)
    assert "def helper" not in cleaned
    assert "def fresh" in cleaned
    assert stats["removed_declarations"] == 1


# ── frozen_context_before ─────────────────────────────────────────────

def test_frozen_context_before():
    ctx = frozen_context_before(SAMPLE, "Chp2|2|thm")
    assert "def f" in ctx
    assert "f_nonneg" not in ctx


def test_frozen_context_before_first():
    ctx = frozen_context_before(SAMPLE, "Chp2|1|defn")
    # For the first block, frozen context is scoped to current namespace only
    assert "namespace Chp2" in ctx
    assert "import Mathlib" not in ctx
    assert "def f" not in ctx


# ── insert_block_comment / insert_code_after_comment ──────────────────

def test_insert_block_comment():
    base = "import Mathlib\n\nnamespace Chp2\n\nend Chp2\n"
    raw = {"source_idx": "Chp2", "index": 1, "kind": "defn", "content": "Test."}
    comment = generate_block_comment(raw)
    result = insert_block_comment(base, "Chp2", comment)
    assert "/- [BLOCK" in result
    assert "Test." in result


def test_insert_code_after_comment():
    text_with_comment = (
        "import Mathlib\n\n"
        "/- [BLOCK Chp2 | 1 | defn]\nTest.\n-/\n\n"
        "end Chp2\n"
    )
    bid = "Chp2|1|defn"
    code = "def foo := 42"
    result = insert_code_after_comment(text_with_comment, bid, code)
    assert "def foo := 42" in result


# ── extract_block_comment_and_code ────────────────────────────────────

def test_extract_block_comment_and_code():
    result = extract_block_comment_and_code(SAMPLE, "Chp2|1|defn")
    assert result is not None
    chunk, start, end = result
    assert "/- [BLOCK" in chunk
    assert "def f" in chunk


def test_extract_block_comment_and_code_missing():
    result = extract_block_comment_and_code(SAMPLE, "nonexistent")
    assert result is None


# ── Nested comment handling ───────────────────────────────────────────

NESTED = """\
/- [BLOCK A | 1 | defn]
Some /- nested -/ comment.
-/
def foo := 1
"""


def test_nested_comment_parse():
    blocks = parse_blocks(NESTED)
    assert len(blocks) == 1
    assert blocks[0].block_id == "A|1|defn"


# ── Run all ───────────────────────────────────────────────────────────

if __name__ == "__main__":
    import inspect
    tests = [
        (name, obj)
        for name, obj in sorted(globals().items())
        if name.startswith("test_") and inspect.isfunction(obj)
    ]
    passed = 0
    for name, fn in tests:
        try:
            fn()
            passed += 1
            print(f"  PASS  {name}")
        except Exception as e:
            print(f"  FAIL  {name}: {e}")
    print(f"\n{passed}/{len(tests)} tests passed")
