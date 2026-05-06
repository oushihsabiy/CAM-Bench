"""Lean 4 validator — compile files and parse compiler output.

Merges the logic from the top-level ``interact.py``.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Dict, List, Tuple

from ..models import CompileResult, Exercise, ExerciseStatus

# Number of parallel lean processes and within-process threads
_PARALLEL_JOBS = int(os.environ.get("LEAN_PARALLEL_JOBS", "4"))
_LEAN_THREADS = int(os.environ.get("LEAN_THREADS", "4"))

# Pattern to detect .olean missing errors
_OLEAN_MISSING_PATTERN = re.compile(r"\.olean['\"]?\s+does\s+not\s+exist")


def _stable_lake_env() -> dict[str, str]:
    """Build a stable environment for Lake subprocesses.

    Force local artifact generation to avoid cache/interface-only mismatches
    where ``Mathlib.ilean`` exists but ``Mathlib.olean`` is missing.
    """
    env = os.environ.copy()
    env["LAKE_ARTIFACT_CACHE"] = "false"
    return env


# ------------------------------------------------------------------
# Helper functions for cache recovery
# ------------------------------------------------------------------

def _check_olean_missing(errors: List[Dict]) -> bool:
    """Check if any error messages indicate missing .olean files."""
    for err in errors:
        msg = err.get("message", "")
        if _OLEAN_MISSING_PATTERN.search(msg):
            return True
    return False


def _run_cache_recovery(toolchain_dir: str | Path = "lean", timeout: int = 60) -> bool:
    """Run 'lake exe cache get!' to recover .olean files."""
    cwd = Path(toolchain_dir).resolve()
    try:
        print("[compile] Attempting cache recovery with 'lake exe cache get!'...", file=sys.stderr)
        r = subprocess.run(
            ["lake", "exe", "cache", "get!"],
            cwd=str(cwd),
            env=_stable_lake_env(),
            capture_output=True,
            text=True,
            encoding="utf-8",
            timeout=timeout,
        )
        if r.returncode == 0:
            print("[compile] Cache recovery successful", file=sys.stderr)
            return True
        else:
            print(f"[compile] Cache recovery failed: {r.stderr[:500]}", file=sys.stderr)
            return False
    except subprocess.TimeoutExpired:
        print("[compile] Cache recovery timed out", file=sys.stderr)
        return False
    except Exception as e:
        print(f"[compile] Cache recovery error: {e}", file=sys.stderr)
        return False


def _has_lakefile(dirpath: Path) -> bool:
    return (dirpath / "lakefile.lean").exists() or (dirpath / "lakefile.toml").exists()


def _resolve_lake_project_root(
    *,
    filepath: Path | None,
    toolchain_dir: str | Path,
) -> Path:
    """Pick a usable Lake project root.

    Priority:
    1) The provided toolchain_dir if it contains a lakefile.
    2) Nearest ancestor (from filepath upward) that contains a lakefile.
    3) Nearest ancestor (from toolchain_dir upward) that contains a lakefile.
    4) Fallback to the original toolchain_dir.
    """
    candidate = Path(toolchain_dir).resolve()
    if _has_lakefile(candidate):
        return candidate

    if filepath is not None:
        fp = filepath.resolve()
        for parent in [fp.parent, *fp.parents]:
            if _has_lakefile(parent):
                return parent

    for parent in [candidate, *candidate.parents]:
        if _has_lakefile(parent):
            return parent

    return candidate


# ------------------------------------------------------------------
# Low-level: compile a single .lean file
# ------------------------------------------------------------------

def compile_lean_file(
    filepath: str | Path,
    toolchain_dir: str | Path = "lean",
    timeout: int = 120,
    auto_cache_recovery: bool = True,
    use_lake_env: bool = True,
) -> CompileResult:
    """Run ``lake env lean <filepath>`` and return structured output."""
    filepath = Path(filepath).resolve()
    cwd = _resolve_lake_project_root(filepath=filepath, toolchain_dir=toolchain_dir)

    try:
        r = subprocess.run(
            ["lake", "env", "lean", f"--threads={_LEAN_THREADS}", str(filepath)],
            cwd=str(cwd),
            env=_stable_lake_env(),
            capture_output=True,
            text=True,
            encoding="utf-8",
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return CompileResult(
            filename=filepath.name,
            stdout="",
            returncode=1,
            errors=[{
                "line": 0, "column": 0,
                "message": f"Compilation timed out after {timeout}s",
                "line_content": "", "char_at_column": "",
            }],
        )

    combined_output = r.stdout + "\n" + r.stderr
    warnings, errors = _parse_output(combined_output, str(filepath))
    # Lean's exit code is authoritative: returncode=0 means success.
    # Any errors parsed while returncode==0 are false positives (e.g. "error:"
    # text inside elaboration context lines, or lake informational messages).
    if r.returncode == 0:
        errors = []
    if r.returncode != 0 and not errors:
        raw_lines = [ln for ln in combined_output.splitlines() if ln.strip()]
        snippet = "\n".join(raw_lines[:25])[:4000]
        errors = [{
            "line": 0,
            "column": 0,
            "message": (
                "Compilation failed but no positional diagnostics were parsed.\n"
                f"Raw output snippet:\n{snippet}"
            ),
            "line_content": "",
            "char_at_column": "",
        }]
    
    # Auto-recover if .olean missing
    if (
        auto_cache_recovery
        and r.returncode != 0
        and _check_olean_missing(errors)
    ):
        # Try cache download and re-run compile
        _run_cache_recovery(toolchain_dir, timeout=60)

        def _retry_compile():
            return subprocess.run(
                ["lake", "env", "lean", f"--threads={_LEAN_THREADS}", str(filepath)],
                cwd=str(cwd),
                env=_stable_lake_env(),
                capture_output=True,
                text=True,
                encoding="utf-8",
                timeout=timeout,
            )

        try:
            r = _retry_compile()
            combined_output = r.stdout + "\n" + r.stderr
            warnings, errors = _parse_output(combined_output, str(filepath))
            if r.returncode == 0:
                errors = []

            if r.returncode != 0 and not errors:
                raw_lines = [ln for ln in combined_output.splitlines() if ln.strip()]
                snippet = "\n".join(raw_lines[:25])[:4000]
                errors = [{
                    "line": 0,
                    "column": 0,
                    "message": (
                        "Compilation failed but no positional diagnostics were parsed.\n"
                        f"Raw output snippet:\n{snippet}"
                    ),
                    "line_content": "",
                    "char_at_column": "",
                }]
                errors.insert(0, {
                    "line": 0,
                    "column": 0,
                    "message": "[Note: Auto-recovery (cache get) was attempted but errors persist]",
                    "line_content": "",
                    "char_at_column": "",
                })
        except subprocess.TimeoutExpired:
            errors.append({
                "line": 0,
                "column": 0,
                "message": "Retry compilation timed out after recovery attempt",
                "line_content": "",
                "char_at_column": "",
            })
    
    return CompileResult(
        filename=filepath.name,
        stdout=combined_output,
        returncode=r.returncode,
        warnings=warnings,
        errors=errors,
    )


# ------------------------------------------------------------------
# Parse Lean compiler output (ported from interact.py)
# ------------------------------------------------------------------

_WARNING_RE = re.compile(r"(.+):(\d+):(\d+): warning(?:\([^)]+\))?: (.+)")
_ERROR_RE   = re.compile(r"(.+):(\d+):(\d+): error(?:\([^)]+\))?: (.+)")
_ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")
_GENERIC_ERROR_RE = re.compile(r"^error:\s*(.+)$", re.IGNORECASE)


def _parse_output(
    lean_output: str,
    source_path: str | None = None,
) -> Tuple[List[Dict], List[Dict]]:
    """Parse warnings and errors from Lean compiler stdout."""
    warnings_raw: List[Dict] = []
    errors_raw: List[Dict] = []
    current: Dict | None = None
    is_warning = False

    def flush() -> None:
        nonlocal current
        if current is None:
            return
        (warnings_raw if is_warning else errors_raw).append(current)
        current = None

    cleaned = _ANSI_RE.sub("", lean_output)
    for line in cleaned.splitlines():
        stripped = line.strip()
        wm = _WARNING_RE.match(line)
        em = _ERROR_RE.match(line)
        if wm or em:
            flush()
            fp, ln, col, msg = (wm or em).groups()  # type: ignore[union-attr]
            current = {
                "filepath": fp.strip(),
                "line": int(ln),
                "column": int(col),
                "message": msg.strip(),
                "line_content": "",
                "char_at_column": "",
            }
            is_warning = bool(wm)
        elif current is None and _GENERIC_ERROR_RE.match(stripped):
            # Only start a generic error when NOT inside an existing diagnostic.
            # Continuation lines that contain "error:" are appended to the
            # current message by the branch below, not promoted to new errors.
            flush()
            msg = _GENERIC_ERROR_RE.match(stripped).group(1)  # type: ignore[union-attr]
            current = {
                "filepath": source_path or "",
                "line": 0,
                "column": 0,
                "message": msg.strip(),
                "line_content": "",
                "char_at_column": "",
            }
            is_warning = False
        elif current is not None:
            current["message"] += "\n" + stripped

    flush()

    # Enrich with source-file context
    file_paths = {r["filepath"] for r in warnings_raw + errors_raw}
    contents: Dict[str, List[str] | None] = {}
    for fp in file_paths:
        fp_str = str(fp or "").strip()
        if not fp_str:
            contents[fp] = None
            continue
        p = Path(fp_str)
        # Skip directories and non-regular files (avoid IsADirectoryError)
        if not p.is_file():
            contents[fp] = None
            continue
        try:
            contents[fp] = p.read_text(encoding="utf-8").splitlines()
        except FileNotFoundError:
            contents[fp] = None

    for rec in warnings_raw + errors_raw:
        lines = contents.get(rec["filepath"])
        if lines is None:
            rec["line_content"] = f"[couldn't read file {rec['filepath']}]"
            continue
        idx = rec["line"] - 1
        if not (0 <= idx < len(lines)):
            rec["line_content"] = f"[couldn't read line {rec['line']}]"
            continue
        rec["line_content"] = lines[idx]
        # Lean columns are 1-based; convert to 0-based index for Python strings.
        col_idx = rec["column"] - 1
        if 0 <= col_idx < len(lines[idx]):
            rec["char_at_column"] = lines[idx][col_idx]

    # Strip filepath from public records (caller already knows it)
    def _clean(items: List[Dict]) -> List[Dict]:
        return [
            {k: v for k, v in r.items() if k != "filepath"}
            for r in items
        ]

    return _clean(warnings_raw), _clean(errors_raw)

# ------------------------------------------------------------------
# High-level: validate an Exercise
# ------------------------------------------------------------------

def validate_exercise(
    exercise: Exercise,
    lean_file: Path,
    toolchain_dir: str = "lean",
    timeout: int = 120,
) -> CompileResult:
    """Compile the Lean file for *exercise* and update its status."""
    result = compile_lean_file(lean_file, toolchain_dir, timeout)
    exercise.warnings = result.warnings
    exercise.errors = result.errors
    exercise.compile_returncode = result.returncode

    if exercise.is_valid:
        exercise.status = ExerciseStatus.VALID
    return result


def validate_exercise_with_mcp(
    exercise: Exercise,
    lean_file: Path,
    toolchain_dir: str = "lean",
    timeout: int = 120,
    mcp_enabled: bool = False,
    mcp_pool_size: int = 1,
    mcp_repo_path: str | None = None,
) -> CompileResult:
    """Validate one exercise and optionally append MCP diagnostics context."""
    result = validate_exercise(exercise, lean_file, toolchain_dir, timeout)
    if (
        mcp_enabled
        and not exercise.is_valid
        and _needs_mcp_diagnostics(exercise.errors, exercise.compile_returncode)
    ):
        _augment_with_mcp_diagnostics(
            ex=exercise,
            lean_file=lean_file,
            project_root=_resolve_lake_project_root(
                filepath=lean_file,
                toolchain_dir=toolchain_dir,
            ),
            pool_size=mcp_pool_size,
            mcp_repo_path=mcp_repo_path,
        )
    return result


def validate_all(
    exercises: List[Exercise],
    output_dir: Path,
    toolchain_dir: str = "lean",
    timeout: int = 120,
    parallel_jobs: int | None = None,
    mcp_enabled: bool = False,
    mcp_pool_size: int = 1,
    mcp_repo_path: str | None = None,
) -> Dict[str, CompileResult]:
    """Validate all exercises whose Lean files exist in *output_dir*.

    Exercises are compiled in parallel (up to *parallel_jobs* at once)
    to reduce total wall-clock time.
    """
    jobs = parallel_jobs if parallel_jobs is not None else _PARALLEL_JOBS
    results: Dict[str, CompileResult] = {}
    total = len(exercises)

    # Build the list of (exercise, lean_file) pairs that actually exist
    pending = []
    for ex in exercises:
        lean_file = output_dir / f"{_safe_label(ex.label)}.lean"
        if lean_file.exists():
            pending.append((ex, lean_file))
        else:
            print(f"[validator] SKIP {ex.label} (no file)", file=sys.stderr)

    def _compile_one(args):
        ex, lean_file = args
        return ex, lean_file, validate_exercise(ex, lean_file, toolchain_dir, timeout)

    completed = 0
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        futures = {pool.submit(_compile_one, item): item for item in pending}
        for future in as_completed(futures):
            ex, lean_file = futures[future]
            try:
                _, _, result = future.result()
            except Exception as err:
                ex.errors = [{
                    "line": 0,
                    "column": 0,
                    "message": f"Validation crashed: {err}",
                    "line_content": "",
                    "char_at_column": "",
                }]
                ex.compile_returncode = 1
                completed += 1
                print(
                    f"[validator] [{completed}/{len(pending)}] {ex.label} -> CRASH ({err})",
                    file=sys.stderr,
                )
                continue

            results[ex.label] = result
            completed += 1

            if (
                mcp_enabled
                and not ex.is_valid
                and _needs_mcp_diagnostics(ex.errors, ex.compile_returncode)
            ):
                _augment_with_mcp_diagnostics(
                    ex=ex,
                    lean_file=lean_file,
                    project_root=_resolve_lake_project_root(
                        filepath=lean_file,
                        toolchain_dir=toolchain_dir,
                    ),
                    pool_size=mcp_pool_size,
                    mcp_repo_path=mcp_repo_path,
                )

            status = "OK" if ex.is_valid else f"FAIL ({len(result.errors)} errors)"
            print(
                f"[validator] [{completed}/{len(pending)}] {ex.label} -> {status}",
                file=sys.stderr,
            )

    return results


def _safe_label(label: str) -> str:
    return re.sub(r"[^\w\-.]", "_", str(label)) or "exercise"


def _needs_mcp_diagnostics(errors: List[Dict], returncode: int) -> bool:
    if returncode == 0:
        return False
    if not errors:
        return True
    # If all parsed errors are non-positional (line=0), ask MCP for diagnostics.
    return all(int(err.get("line") or 0) <= 0 for err in errors)


def _augment_with_mcp_diagnostics(
    *,
    ex: Exercise,
    lean_file: Path,
    project_root: Path,
    pool_size: int,
    mcp_repo_path: str | None,
) -> None:
    if not lean_file.exists():
        return
    try:
        from ..config.mcp_helper import gather_recovery_context

        ctx = gather_recovery_context(
            file_path=lean_file.resolve(),
            project_root=project_root,
            lean_path="lean",
            pool_size=pool_size,
            focus_line=None,
            focus_column=None,
            mcp_repo_path=mcp_repo_path,
            tool_mode="focused",
        )
    except Exception as err:
        print(f"[validator] MCP diagnostics unavailable for {ex.label}: {err}", file=sys.stderr)
        return

    text = (ctx or "").strip()
    if not text:
        return
    snippet = text[:4000]
    ex.errors.append(
        {
            "line": 0,
            "column": 0,
            "message": f"MCP diagnostic context:\n{snippet}",
            "line_content": "",
            "char_at_column": "",
        }
    )


def print_compile_result(result: CompileResult, *, context: str = "") -> None:
    """Print compile diagnostics to stderr.

    By default only errors are expanded; warnings can be expanded by setting:
      JSON2LEAN_PRINT_WARNINGS=1
    """
    prefix = f"{context}: " if context else ""
    print(
        f"[compile] {prefix}returncode={result.returncode} "
        f"errors={len(result.errors)} warnings={len(result.warnings)}",
        file=sys.stderr,
    )

    show_warnings = os.environ.get("JSON2LEAN_PRINT_WARNINGS", "").strip() in {
        "1", "true", "yes", "on", "TRUE", "YES", "ON",
    }
    if show_warnings:
        for i, warn in enumerate(result.warnings, start=1):
            line = int(warn.get("line") or 0)
            col = int(warn.get("column") or 0)
            msg = str(warn.get("message", "") or "").strip()
            line_content = str(warn.get("line_content", "") or "")
            print(
                f"[compile][warning {i}] line {line}:{col}\n{msg}",
                file=sys.stderr,
            )
            if line_content:
                print(f"[compile][warning {i}] code: {line_content}", file=sys.stderr)

    for i, err in enumerate(result.errors, start=1):
        line = int(err.get("line") or 0)
        col = int(err.get("column") or 0)
        msg = str(err.get("message", "") or "").strip()
        line_content = str(err.get("line_content", "") or "")
        print(
            f"[compile][error {i}] line {line}:{col}\n{msg}",
            file=sys.stderr,
        )
        if line_content:
            print(f"[compile][error {i}] code: {line_content}", file=sys.stderr)
