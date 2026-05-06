"""Data models for the json2lean pipeline."""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Dict, List, Optional


class ExerciseStatus(Enum):
    PENDING = "pending"
    PREPROCESSED = "preprocessed"
    TRANSLATED = "translated"
    VALID = "valid"
    REPAIR_FAILED = "repair_failed"
    UNRECOVERABLE = "unrecoverable"
    ERROR = "error"


@dataclass
class Exercise:
    """One exercise extracted from the input JSON."""

    raw: Dict[str, Any]
    index: int
    label: str = ""
    problem: str = ""
    status: ExerciseStatus = ExerciseStatus.PENDING

    # Populated after preprocessing
    preprocessed_problem: str = ""
    structured: Optional[StructuredExercise] = None

    # Populated after translation
    lean_code: str = ""

    # Populated after validation
    warnings: List[Dict[str, Any]] = field(default_factory=list)
    errors: List[Dict[str, Any]] = field(default_factory=list)
    compile_returncode: int = -1

    # Tracking
    repair_attempts: int = 0

    # Failure metadata (populated for ERROR / UNRECOVERABLE / REPAIR_FAILED)
    failure_type: str = ""          # e.g. "preprocess", "translation", "compile", "semantic"
    failure_phase: str = ""         # finer grain: "translate_llm", "compile_repair_loop", etc.
    failure_message: str = ""       # human-readable description
    failure_exception: str = ""     # repr of the exception if any

    def __post_init__(self) -> None:
        if not self.label:
            self.label = str(
                self.raw.get("source_idx")
                or self.raw.get("题目ID")
                or self.raw.get("index")
                or self.index
            )
        if not self.problem:
            self.problem = (
                self.raw.get("problem")
                or self.raw.get("题目内容")
                or ""
            )

    @property
    def is_valid(self) -> bool:
        return self.compile_returncode == 0 and len(self.errors) == 0


@dataclass
class Block:
    """A single content block within a structured exercise."""

    id: str
    kind: str  # "definition", "assumption", "goal", "hint", etc.
    text: str

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "Block":
        return cls(
            id=str(data["id"]),
            kind=data["kind"],
            text=data["text"],
        )


@dataclass
class StructuredExercise:
    """A structured exercise with typed content blocks loaded from JSON."""

    index: str
    source_document: str
    blocks: List[Block] = field(default_factory=list)

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "StructuredExercise":
        return cls(
            index=str(data["index"]),
            source_document=data["source_document"],
            blocks=[Block.from_dict(b) for b in data.get("blocks", [])],
        )

    def get_blocks_by_kind(self, kind: str) -> List[Block]:
        return [b for b in self.blocks if b.kind == kind]


@dataclass
class CompileResult:
    """Result of compiling a single Lean file."""

    filename: str
    stdout: str
    returncode: int
    warnings: List[Dict[str, Any]] = field(default_factory=list)
    errors: List[Dict[str, Any]] = field(default_factory=list)


@dataclass
class TokenUsage:
    """Token usage for a single API call."""

    prompt_tokens: int = 0
    completion_tokens: int = 0
    total_tokens: int = 0
    call_type: str = ""  # "preprocess", "translate", "recover"
    exercise_label: str = ""
    usage_source: str = "none"  # "api", "api_stream", "estimated", "none"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "prompt_tokens": self.prompt_tokens,
            "completion_tokens": self.completion_tokens,
            "total_tokens": self.total_tokens,
            "call_type": self.call_type,
            "exercise_label": self.exercise_label,
            "usage_source": self.usage_source,
        }


@dataclass
class PipelineConfig:
    """Parsed configuration for the pipeline."""

    api_key: str
    base_url: str
    model: str
    timeout_seconds: float = 180.0
    llm_backend: str = "api"
    codex_bin: str = "bin/codex"
    codex_workdir: str = "lean"
    codex_model: str | None = None
    codex_reasoning_effort: str | None = None
    codex_disable_plugins: bool = True
    codex_max_retries: int = 3
    codex_retry_backoff_base_seconds: float = 1.0
    codex_retry_backoff_max_seconds: float = 8.0
    codex_call_log_dir: str | None = None
    codex_extra_args: list[str] | None = None
    codex_stages: list[str] | None = None

    # Preprocessing (off by default — input data is already preprocessed)
    preprocessing_enabled: bool = True
    preprocessing_max_tokens: int = 4096
    preprocessing_max_attempts: int = 8
    preprocessing_exclude_hints: bool = False
    preprocessing_normalize_skip_thm: bool = False

    # Translation
    translation_max_tokens: int = 4096
    translation_max_attempts: int = 3
    translation_mcp_enabled: bool = False
    translation_mcp_pool_size: int = 1
    translation_mcp_repo_path: str | None = None
    translation_mcp_tool_mode: str = "targeted"
    translation_mcp_tools: list[str] | None = None

    # Recovery
    recovery_max_tokens: int = 4096
    recovery_max_retries: int = 8
    recovery_mcp_enabled: bool = False
    recovery_mcp_pool_size: int = 1
    recovery_mcp_repo_path: str | None = None
    recovery_mcp_tool_mode: str = "focused"
    recovery_mcp_tools: list[str] | None = None
    recovery_use_common_errors: bool = True
    recovery_api_first_rounds: int = 2
    recovery_api_first_mcp_enabled: bool = True

    # Semantic review / rewrite (off by default)
    semantic_enabled: bool = False
    semantic_max_rounds: int = 8
    semantic_review_max_tokens: int = 4096
    semantic_review_max_attempts: int = 2
    semantic_rewrite_max_tokens: int = 4096
    semantic_rewrite_max_attempts: int = 2

    # Lean
    lean_toolchain_dir: str = "lean"
    lean_timeout_seconds: int = 120

    # Compile mode
    compile_use_lake_env: bool = True
    compile_auto_cache_recovery: bool = True

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> PipelineConfig:
        pre = data.get("preprocessing", {})
        trans = data.get("translation", {})
        rec = data.get("recovery", {})
        sem = data.get("semantic", {})
        lean = data.get("lean", {})
        cmp = data.get("compile", {})
        codex = data.get("codex_cli", {})

        return cls(
            api_key=data["api_key"],
            base_url=data["base_url"],
            model=data["model"],
            timeout_seconds=data.get("timeout_seconds", 180.0),
            llm_backend=data.get("llm_backend", "api"),
            codex_bin=codex.get("bin", "bin/codex"),
            codex_workdir=codex.get("workdir", "lean"),
            codex_model=codex.get("model"),
            codex_reasoning_effort=codex.get("reasoning_effort"),
            codex_disable_plugins=codex.get("disable_plugins", True),
            codex_max_retries=codex.get("max_retries", 3),
            codex_retry_backoff_base_seconds=codex.get("retry_backoff_base_seconds", 1.0),
            codex_retry_backoff_max_seconds=codex.get("retry_backoff_max_seconds", 8.0),
            codex_call_log_dir=codex.get("call_log_dir"),
            codex_extra_args=codex.get("extra_args"),
            codex_stages=codex.get("stages", ["recovery"]),
            preprocessing_enabled=pre.get("enabled", True),
            preprocessing_max_tokens=pre.get("max_tokens", 4096),
            preprocessing_max_attempts=pre.get("max_attempts", 8),
            preprocessing_exclude_hints=pre.get("exclude_hints", False),
            preprocessing_normalize_skip_thm=pre.get("normalize_skip_thm", False),
            translation_max_tokens=trans.get("max_tokens", 4096),
            translation_max_attempts=trans.get("max_attempts", 3),
            translation_mcp_enabled=trans.get("mcp_enabled", False),
            translation_mcp_pool_size=trans.get("mcp_pool_size", 1),
            translation_mcp_repo_path=trans.get("mcp_repo_path"),
            translation_mcp_tool_mode=trans.get("mcp_tool_mode", "targeted"),
            translation_mcp_tools=trans.get("mcp_tools"),
            recovery_max_tokens=rec.get("max_tokens", 4096),
            recovery_max_retries=rec.get("max_retries", 8),
            recovery_mcp_enabled=rec.get("mcp_enabled", False),
            recovery_mcp_pool_size=rec.get("mcp_pool_size", 1),
            recovery_mcp_repo_path=rec.get("mcp_repo_path"),
            recovery_mcp_tool_mode=rec.get("mcp_tool_mode", "focused"),
            recovery_mcp_tools=rec.get("mcp_tools"),
            recovery_use_common_errors=rec.get("use_common_errors", True),
            recovery_api_first_rounds=rec.get("api_first_rounds", 2),
            recovery_api_first_mcp_enabled=rec.get("api_first_mcp_enabled", True),
            semantic_enabled=sem.get("enabled", False),
            semantic_max_rounds=sem.get("max_rounds", 8),
            semantic_review_max_tokens=sem.get("review_max_tokens", 4096),
            semantic_review_max_attempts=sem.get("review_max_attempts", 2),
            semantic_rewrite_max_tokens=sem.get("rewrite_max_tokens", 4096),
            semantic_rewrite_max_attempts=sem.get("rewrite_max_attempts", 2),
            lean_toolchain_dir=lean.get("toolchain_dir", "lean"),
            lean_timeout_seconds=lean.get("timeout_seconds", 120),
            compile_use_lake_env=cmp.get("use_lake_env", True),
            compile_auto_cache_recovery=cmp.get("auto_cache_recovery", True),
        )

    def overlay_settings(self, settings: Dict[str, Any]) -> "PipelineConfig":
        """Merge runtime settings on top of the current config in-place.

        Accepted top-level keys mirror the nested groups used by
        ``from_dict``: ``preprocessing``, ``translation``, ``recovery``,
        ``semantic``, ``lean``, ``compile``.  Scalar keys at the top level
        (e.g. ``timeout_seconds``) are also accepted.

        Returns *self* to allow ``cfg = cfg.overlay_settings(settings)``.
        """
        if not settings:
            return self
        _MAP = {
            "preprocessing": {
                "enabled": "preprocessing_enabled",
                "max_tokens": "preprocessing_max_tokens",
                "max_attempts": "preprocessing_max_attempts",
                "exclude_hints": "preprocessing_exclude_hints",
                "normalize_skip_thm": "preprocessing_normalize_skip_thm",
            },
            "translation": {
                "max_tokens": "translation_max_tokens",
                "max_attempts": "translation_max_attempts",
                "mcp_enabled": "translation_mcp_enabled",
                "mcp_pool_size": "translation_mcp_pool_size",
                "mcp_repo_path": "translation_mcp_repo_path",
                "mcp_tool_mode": "translation_mcp_tool_mode",
                "mcp_tools": "translation_mcp_tools",
            },
            "recovery": {
                "max_tokens": "recovery_max_tokens",
                "max_retries": "recovery_max_retries",
                "mcp_enabled": "recovery_mcp_enabled",
                "mcp_pool_size": "recovery_mcp_pool_size",
                "mcp_repo_path": "recovery_mcp_repo_path",
                "mcp_tool_mode": "recovery_mcp_tool_mode",
                "mcp_tools": "recovery_mcp_tools",
                "api_first_rounds": "recovery_api_first_rounds",
                "api_first_mcp_enabled": "recovery_api_first_mcp_enabled",
            },
            "semantic": {
                "enabled": "semantic_enabled",
                "max_rounds": "semantic_max_rounds",
                "review_max_tokens": "semantic_review_max_tokens",
                "review_max_attempts": "semantic_review_max_attempts",
                "rewrite_max_tokens": "semantic_rewrite_max_tokens",
                "rewrite_max_attempts": "semantic_rewrite_max_attempts",
            },
            "lean": {
                "toolchain_dir": "lean_toolchain_dir",
                "timeout_seconds": "lean_timeout_seconds",
            },
            "compile": {
                "use_lake_env": "compile_use_lake_env",
                "auto_cache_recovery": "compile_auto_cache_recovery",
            },
            "codex_cli": {
                "bin": "codex_bin",
                "workdir": "codex_workdir",
                "model": "codex_model",
                "reasoning_effort": "codex_reasoning_effort",
                "disable_plugins": "codex_disable_plugins",
                "max_retries": "codex_max_retries",
                "retry_backoff_base_seconds": "codex_retry_backoff_base_seconds",
                "retry_backoff_max_seconds": "codex_retry_backoff_max_seconds",
                "call_log_dir": "codex_call_log_dir",
                "extra_args": "codex_extra_args",
                "stages": "codex_stages",
            },
        }
        # Top-level scalars
        for key in ("timeout_seconds", "llm_backend"):
            if key in settings:
                setattr(self, key, settings[key])
        # Nested groups
        for group, mapping in _MAP.items():
            sub = settings.get(group, {})
            if not isinstance(sub, dict):
                continue
            for json_key, attr_name in mapping.items():
                if json_key in sub:
                    setattr(self, attr_name, sub[json_key])
        return self
