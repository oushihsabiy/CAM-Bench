"""Quick smoke test for the new repair_history and mcp_helper changes."""
import sys
sys.path.insert(0, "src")

from json2lean.repair_history import RepairHistory
from json2lean.compile.compiling_fixer import recover_all, recover_exercise
from json2lean.semantic.semantic_rewriter import rewrite_from_report
from json2lean.config.mcp_helper import _READ_ONLY_ALLOWLIST, _MUTATING_TOOLS

print("All imports OK")
print(f"Read-only allowlist: {len(_READ_ONLY_ALLOWLIST)} tools")
print(f"Mutating blocked: {len(_MUTATING_TOOLS)} tools")

# Verify mutating tools are blocked
for t in ["lean_build", "lean_apply_patch", "lean_run_code", "lean_multi_attempt"]:
    assert t in _MUTATING_TOOLS, f"{t} not in mutating set"
    assert t not in _READ_ONLY_ALLOWLIST, f"{t} should not be in allowlist"
print("Mutating tool blocking: PASSED")

# Test RepairHistory
h = RepairHistory(keep_recent=3, max_prompt_chars=12000)
h.record(
    attempt=1, loop="compile",
    lean_code="def x := 1",
    errors=[{"line": 1, "column": 0, "message": "type mismatch"}],
    error_signature="1:0:type mismatch",
)
h.record(
    attempt=2, loop="compile",
    lean_code="def x : Nat := 1",
    errors=[], error_signature="",
    rejection_reason="contract_violation: missing theorem",
)
h.record(
    attempt=3, loop="compile",
    lean_code="theorem x : True := trivial",
    errors=[], error_signature="",
)
block = h.format_for_prompt()
print(f"History block length: {len(block)} chars")
assert "Do NOT repeat" in block
assert "contract_violation" in block
assert "type mismatch" in block
assert h.size == 3
print("RepairHistory basic tests: PASSED")

# Test history with >3 entries (summarization)
for i in range(4, 8):
    h.record(
        attempt=i, loop="compile",
        lean_code=f"-- attempt {i}",
        errors=[{"line": i, "column": 0, "message": f"error {i}"}],
        error_signature=f"{i}:0:error {i}",
    )
block2 = h.format_for_prompt()
assert "Summarised older history" in block2 or "Recent history" in block2
print(f"History with {h.size} entries: {len(block2)} chars")
print("RepairHistory summarization: PASSED")

# Test empty history
h_empty = RepairHistory(keep_recent=5)
assert h_empty.format_for_prompt() == ""
print("Empty history: PASSED")

print("\nAll tests PASSED!")
