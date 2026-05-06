#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""lean_verifier.py: 单文件 Lean CLI 验证器。"""

from __future__ import annotations

import re
import subprocess
import time
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class LeanError:
    """Lean 编译器报告的单条错误。"""
    file: str
    line: int
    col: int
    severity: str       # "error" | "warning" | "info"
    message: str

    def short(self) -> str:
        return f"L{self.line}:{self.col} [{self.severity}] {self.message[:120]}"


@dataclass
class VerifyResult:
    """Lean 验证结果。"""
    passed: bool
    returncode: int
    errors: list[LeanError] = field(default_factory=list)
    warnings: list[LeanError] = field(default_factory=list)
    elapsed_sec: float = 0.0
    stdout: str = ""
    stderr: str = ""

    @property
    def error_summary(self) -> str:
        """拼接所有错误信息（用于传给 LLM 做下一轮修复）。"""
        if self.errors:
            return "\n".join(e.short() for e in self.errors[:15])

        # 有些失败场景不会产出可解析的 Lean error 行，回退到进程级信息
        parts: list[str] = []
        if self.returncode != 0:
            parts.append(f"returncode={self.returncode}")
        # 合并 stderr + stdout，取最后 20 条非空行，避免仅展示 warning
        combined = (self.stderr + "\n" + self.stdout).strip()
        if combined:
            tail_lines = [l for l in combined.splitlines() if l.strip()][-20:]
            parts.append("\n".join(tail_lines))
        if parts:
            return " | ".join(parts)
        return "unknown verifier failure"

    @property
    def error_types(self) -> set[str]:
        """提取错误关键词类型集合（用于 error_diversity 指标）。"""
        types: set[str] = set()
        for e in self.errors:
            msg = e.message.lower()
            if "unknown identifier" in msg or "unknown constant" in msg:
                types.add("unknown_identifier")
            elif "type mismatch" in msg:
                types.add("type_mismatch")
            elif "unsolved goals" in msg:
                types.add("unsolved_goals")
            elif "unknown tactic" in msg:
                types.add("unknown_tactic")
            elif "timeout" in msg or "deterministic timeout" in msg:
                types.add("timeout")
            elif "expected" in msg:
                types.add("syntax_error")
            else:
                types.add("other")
        return types


# ---------------------------------------------------------------------------
# 解析 Lean stderr 中的报错
# ---------------------------------------------------------------------------

_ERR_RE = re.compile(
    r"^(.+?):(\d+):(\d+):\s*(error|warning|info)\s*:\s*(.*)",
    re.MULTILINE,
)


def _find_lake_root(start: Path) -> Path | None:
    """Find nearest parent containing lakefile.lean or lakefile.toml."""
    for p in [start, *start.parents]:
        if (p / "lakefile.lean").exists() or (p / "lakefile.toml").exists():
            return p
    return None


def _parse_lean_output(stderr: str) -> tuple[list[LeanError], list[LeanError]]:
    errors: list[LeanError] = []
    warnings: list[LeanError] = []
    for m in _ERR_RE.finditer(stderr):
        le = LeanError(
            file=m.group(1),
            line=int(m.group(2)),
            col=int(m.group(3)),
            severity=m.group(4),
            message=m.group(5).strip(),
        )
        if le.severity == "error":
            errors.append(le)
        elif le.severity == "warning":
            warnings.append(le)
    return errors, warnings


# ---------------------------------------------------------------------------
# 核心验证函数
# ---------------------------------------------------------------------------

def verify_lean_file(
    lean_file: Path,
    lean_cwd: str | Path | None = None,
    timeout: float | None = 120,
) -> VerifyResult:
    """
    用 lean CLI 编译单个 .lean 文件，返回验证结果。

    Parameters
    ----------
    lean_file : 要验证的 .lean 文件路径
    lean_cwd : lean 命令的工作目录（含 lakefile.lean 的项目根）
    timeout : 编译超时秒数（<=0 或 None 表示不设上限）
    """
    lean_file = Path(lean_file).resolve()
    cwd_path = Path(lean_cwd).resolve() if lean_cwd else _find_lake_root(lean_file.parent)
    cwd = str(cwd_path) if cwd_path else None

    # Always prefer lake-managed invocation so local and final verification are consistent.
    cmd = ["lake", "env", "lean", str(lean_file)]
    if cwd is None:
        # Last fallback when file is outside a Lake project.
        cmd = ["lean", str(lean_file)]

    # Treat non-positive timeout as unlimited to avoid immediate timeout on timeout=0.
    run_timeout: float | None
    if timeout is None:
        run_timeout = None
    else:
        run_timeout = float(timeout)
        if run_timeout <= 0:
            run_timeout = None

    t0 = time.monotonic()
    try:
        r = subprocess.run(
            cmd,
            cwd=cwd,
            capture_output=True,
            text=True,
            timeout=run_timeout,
        )
    except subprocess.TimeoutExpired:
        elapsed = time.monotonic() - t0
        return VerifyResult(
            passed=False,
            returncode=-1,
            errors=[LeanError("", 0, 0, "error", f"TIMEOUT after {elapsed:.1f}s")],
            elapsed_sec=elapsed,
        )
    except FileNotFoundError:
        return VerifyResult(
            passed=False,
            returncode=-2,
            errors=[
                LeanError(
                    "", 0, 0, "error",
                    "lean/lake executable not found in PATH",
                )
            ],
        )

    elapsed = time.monotonic() - t0
    errors, warnings = _parse_lean_output(r.stderr)

    # 有时 lean 返回 0 但 stderr 含 error（import 缓存场景），以 error list 为准
    passed = r.returncode == 0 and len(errors) == 0

    return VerifyResult(
        passed=passed,
        returncode=r.returncode,
        errors=errors,
        warnings=warnings,
        elapsed_sec=elapsed,
        stdout=r.stdout,
        stderr=r.stderr,
    )


def verify_lean_string(
    code: str,
    tmp_dir: Path,
    filename: str = "check.lean",
    lean_cwd: str | Path | None = None,
    timeout: float | None = 120,
) -> VerifyResult:
    """
    将 code 写入临时文件后验证，方便在 solver 中反复调用。
    """
    tmp_dir = Path(tmp_dir)
    tmp_dir.mkdir(parents=True, exist_ok=True)
    tmp_file = tmp_dir / filename
    tmp_file.write_text(code, encoding="utf-8")
    return verify_lean_file(tmp_file, lean_cwd=lean_cwd, timeout=timeout)


# ---------------------------------------------------------------------------
# 代码完整性检查（借鉴 judge/check_cheating.py 的检测逻辑）
# ---------------------------------------------------------------------------

_CHEAT_PATTERNS: list[tuple[re.Pattern, str]] = [
    (re.compile(r"\bsorry\b"), "contains_sorry"),
    (re.compile(r"\baxiom\b"), "contains_axiom"),
    (re.compile(r"\badmit\b"), "contains_admit"),
    (re.compile(r"\bnative_decide\b"), "uses_native_decide"),
]


def check_proof_integrity(code: str) -> list[str]:
    """
    检查生成的证明代码是否包含可疑关键字。

    Returns
    -------
    问题列表；空列表表示通过。
    """
    issues: list[str] = []
    for line in code.splitlines():
        stripped = line.lstrip()
        if stripped.startswith("--"):
            continue
        # 去掉行内注释
        code_part = line.split("--")[0]
        for pat, label in _CHEAT_PATTERNS:
            if pat.search(code_part):
                issues.append(label)
    return sorted(set(issues))
