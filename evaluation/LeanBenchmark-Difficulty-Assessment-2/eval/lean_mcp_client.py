#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""lean_mcp_client.py: Lean MCP 适配层（可选启用）。"""

from __future__ import annotations

import json
import os
import subprocess
import tempfile
import urllib.error
import urllib.request
from dataclasses import dataclass, field
from pathlib import Path


def _default_tools() -> dict[str, dict[str, object]]:
    return {
        "analyze_prefix": {"enabled": True, "method": "analyze_prefix", "extra_params": {}},
        "search": {"enabled": False, "method": "search", "extra_params": {}},
        "suggest_tactics": {"enabled": False, "method": "suggest_tactics", "extra_params": {}},
        "verify_proof": {"enabled": False, "method": "verify_proof", "extra_params": {}},
    }


@dataclass
class LeanMCPConfig:
    """Lean MCP 连接配置。"""

    enabled: bool = False
    transport: str = "http"  # http | stdio | python
    endpoint: str = ""
    command: str = ""
    timeout_sec: float = 5.0
    tools: object = field(default_factory=_default_tools)
    tool_selection_strategy: str = "single"
    tool_mode: str = "targeted"      # focused | targeted | all
    pool_size: int = 1
    mcp_repo_path: str = ""
    env_vars: dict[str, str] = field(default_factory=dict)


@dataclass
class LeanMCPContext:
    """Lean MCP 返回的结构化上下文。"""

    goals: str = ""            # analyze_prefix: 当前证明状态
    diagnostics: str = ""      # analyze_prefix: 额外诊断信息
    search_results: str = ""   # search: 含签名的定理列表
    tactics: str = ""          # suggest_tactics: 可用 tactic 建议
    raw: str = ""              # 兜底：无结构化字段时的原始文本

    def has_content(self) -> bool:
        return bool(self.goals or self.diagnostics or self.search_results or self.tactics or self.raw)

    def to_prompt_text(self, max_chars: int = 2000) -> str:
        parts: list[str] = []
        if self.goals:
            parts.append(f"### Proof State\n{self.goals}")
        if self.search_results:
            parts.append(f"### Relevant Theorems\n{self.search_results}")
        if self.tactics:
            parts.append(f"### Suggested Tactics\n{self.tactics}")
        if self.diagnostics:
            parts.append(f"### Diagnostics\n{self.diagnostics}")
        if self.raw:
            parts.append(f"### Raw Output\n{self.raw}")
        text = "\n\n".join(parts).strip()
        if len(text) > max_chars:
            return text[:max_chars] + "\n...[truncated]"
        return text


@dataclass
class LeanMCPQueryResult:
    """一次失败分析中 MCP 调用的聚合结果。"""

    context: LeanMCPContext = field(default_factory=LeanMCPContext)
    call_count: int = 0
    failure_count: int = 0
    used_tools: list[str] = field(default_factory=list)
    failed_tools: list[str] = field(default_factory=list)


class LeanMCPClient:
    """Lean MCP 客户端。默认协议为 method=params 风格 JSON 请求。"""

    def __init__(self, cfg: LeanMCPConfig):
        self.cfg = cfg
        self.cfg.tools = self._normalize_tools(cfg.tools)

    def gather_failure_context(
        self,
        prefix_text: str,
        *,
        problem_path: str | None,
        block_name: str,
        line_no: int,
        col_no: int,
        error_summary: str = "",
    ) -> LeanMCPQueryResult:
        if (self.cfg.transport or "").strip().lower() == "python":
            return self._gather_failure_context_python(
                prefix_text,
                problem_path=problem_path,
                block_name=block_name,
                line_no=line_no,
                col_no=col_no,
                error_summary=error_summary,
            )

        search_query = self._build_search_query(error_summary, block_name, prefix_text)
        base_params = {
            "prefix_text": prefix_text,
            "problem_path": problem_path,
            "block_name": block_name,
            "line_no": line_no,
            "col_no": col_no,
            "error_summary": error_summary,
            "proof_text": prefix_text,
            "query": search_query,
            "search_query": search_query,
        }
        selected_tools = self._select_tools(error_summary)
        result = LeanMCPQueryResult()

        for tool_name in selected_tools:
            result.call_count += 1
            try:
                ctx = self._call_named_tool(tool_name, base_params)
                result.used_tools.append(tool_name)
                result.context = self._merge_context(result.context, tool_name, ctx)
                if self.cfg.tool_selection_strategy == "fallback" and ctx.has_content():
                    break
            except Exception:
                result.failure_count += 1
                result.failed_tools.append(tool_name)
                if self.cfg.tool_selection_strategy == "single":
                    break

        return result

    def _gather_failure_context_python(
        self,
        prefix_text: str,
        *,
        problem_path: str | None,
        block_name: str,
        line_no: int,
        col_no: int,
        error_summary: str = "",
    ) -> LeanMCPQueryResult:
        from .mcp_helper import gather_recovery_context

        enabled_tools = self._select_python_tools()
        errors = [{"line": line_no, "column": col_no, "message": error_summary or block_name}]

        if problem_path:
            p = Path(problem_path).resolve()
            project_root = self._resolve_lake_project_root(p)
            temp_dir = p.parent
        else:
            p = None
            project_root = Path.cwd()
            temp_dir = Path.cwd()

        # Feed current prefix snapshot to MCP tools by writing a temp Lean file.
        with tempfile.NamedTemporaryFile(
            mode="w",
            suffix=".lean",
            prefix="mcp_prefix_",
            dir=str(temp_dir),
            encoding="utf-8",
            delete=False,
        ) as tf:
            tf.write(prefix_text)
            tmp_path = Path(tf.name)

        try:
            mcp_result = gather_recovery_context(
                file_path=tmp_path,
                project_root=project_root,
                lean_path="lean",
                pool_size=max(1, int(self.cfg.pool_size or 1)),
                focus_line=max(1, int(line_no or 1)),
                focus_column=max(1, int(col_no or 1)),
                mcp_repo_path=(self.cfg.mcp_repo_path or "").strip() or None,
                tool_mode=str(self.cfg.tool_mode or "targeted"),
                errors=errors,
                enabled_tools=enabled_tools,
                query_seed=(block_name or "").strip() or tmp_path.stem,
                codex_home_env_vars=self.cfg.env_vars,
            )
        finally:
            try:
                tmp_path.unlink(missing_ok=True)
            except Exception:
                pass

        parsed_ctx = self._parse_python_context_text(mcp_result.context_text)

        return LeanMCPQueryResult(
            context=parsed_ctx,
            call_count=mcp_result.call_count,
            failure_count=mcp_result.failure_count,
            used_tools=mcp_result.used_tools,
            failed_tools=mcp_result.failed_tools,
        )

    @staticmethod
    def _parse_python_context_text(text: str) -> LeanMCPContext:
        """Parse mcp_helper aggregated text into structured MCP fields.

        mcp_helper returns sectioned text like:
          == MCP unified-search ==
          ...
          == MCP lean_leansearch_0 ==
          ...
        This parser extracts likely theorem content into `search_results`,
        extracts backend/tool errors into `diagnostics`, and keeps full text in `raw`.
        """
        raw = (text or "").strip()
        if not raw:
            return LeanMCPContext()

        sections: list[tuple[str, str]] = []
        cur_title: str | None = None
        cur_lines: list[str] = []

        for line in raw.splitlines():
            stripped = line.strip()
            if stripped.startswith("== ") and stripped.endswith(" =="):
                if cur_title is not None:
                    sections.append((cur_title, "\n".join(cur_lines).strip()))
                cur_title = stripped[3:-3].strip()
                cur_lines = []
            else:
                cur_lines.append(line)

        if cur_title is not None:
            sections.append((cur_title, "\n".join(cur_lines).strip()))

        if not sections:
            return LeanMCPContext(raw=raw)

        search_parts: list[str] = []
        diagnostics_parts: list[str] = []
        other_parts: list[str] = []

        for title, body in sections:
            if not body:
                continue
            t = title.lower()
            body_lines = body.splitlines()
            is_search = (
                "search" in t
                or "unified" in t
                or "leansearch" in t
                or "loogle" in t
                or "leanfinder" in t
            )
            has_backend_err = (
                "backend errors:" in body.lower()
                or "[loogle] error:" in body.lower()
                or "[leansearch] error:" in body.lower()
                or "[leanfinder] error:" in body.lower()
                or "timed out" in body.lower()
                or "http error" in body.lower()
            )

            # Strip backend-error preamble from search payload so theorem list stays clean.
            cleaned_body = body
            if is_search and body_lines and body_lines[0].strip().lower() == "backend errors:":
                idx = 1
                while idx < len(body_lines) and body_lines[idx].startswith("  -"):
                    idx += 1
                while idx < len(body_lines) and not body_lines[idx].strip():
                    idx += 1
                cleaned_body = "\n".join(body_lines[idx:]).strip()

            if is_search:
                if cleaned_body:
                    search_parts.append(cleaned_body)
            else:
                other_parts.append(f"[{title}]\n{body}")

            if has_backend_err:
                diag_body = body
                if body_lines and body_lines[0].strip().lower() == "backend errors:":
                    # Drop pure "unknown identifier" provider noise; keep actionable backend errors.
                    backend_lines: list[str] = []
                    idx = 1
                    while idx < len(body_lines) and body_lines[idx].startswith("  -"):
                        backend_lines.append(body_lines[idx])
                        idx += 1
                    kept_lines = [ln for ln in backend_lines if "unknown identifier" not in ln.lower()]
                    if kept_lines:
                        diag_body = "Backend errors:\n" + "\n".join(kept_lines)
                    else:
                        diag_body = ""
                if diag_body:
                    diagnostics_parts.append(f"[{title}]\n{diag_body}")

        return LeanMCPContext(
            search_results="\n\n".join(search_parts).strip(),
            diagnostics="\n\n".join(diagnostics_parts).strip(),
            raw=raw if not (search_parts or diagnostics_parts or other_parts) else "\n\n".join(other_parts).strip(),
        )

    def _select_python_tools(self) -> list[str] | None:
        tools_cfg = self.cfg.tools
        if isinstance(tools_cfg, list):
            names = [str(t).strip() for t in tools_cfg if str(t).strip()]
            return names or None

        if isinstance(tools_cfg, dict):
            selected: list[str] = []
            for tool_name, tool_cfg in tools_cfg.items():
                if not isinstance(tool_cfg, dict):
                    continue
                if not bool(tool_cfg.get("enabled", False)):
                    continue
                method = str(tool_cfg.get("method") or "").strip()
                # Prefer explicit method when it already points to lean-tools-mcp tool names.
                if method.startswith("lean_"):
                    selected.append(method)
                elif str(tool_name).startswith("lean_"):
                    selected.append(str(tool_name))
            return selected or None

        return None

    @staticmethod
    def _resolve_lake_project_root(file_path: Path) -> Path:
        if file_path.is_file():
            start = file_path.parent
        else:
            start = file_path
        for parent in [start, *start.parents]:
            if (parent / "lakefile.lean").exists() or (parent / "lakefile.toml").exists():
                return parent
        return start

    def analyze_prefix(
        self,
        prefix_text: str,
        *,
        problem_path: str | None,
        block_name: str,
        line_no: int,
        col_no: int,
    ) -> LeanMCPContext:
        return self._call_named_tool(
            "analyze_prefix",
            {
                "prefix_text": prefix_text,
                "problem_path": problem_path,
                "block_name": block_name,
                "line_no": line_no,
                "col_no": col_no,
                "proof_text": prefix_text,
            },
        )

    def _call_named_tool(self, tool_name: str, base_params: dict[str, object]) -> LeanMCPContext:
        tool_cfg = self.cfg.tools.get(tool_name)
        if not tool_cfg or not bool(tool_cfg.get("enabled", False)):
            raise RuntimeError(f"Lean MCP tool is disabled or missing: {tool_name}")
        method = str(tool_cfg.get("method") or tool_name)
        params = dict(base_params)
        extra_params = tool_cfg.get("extra_params", {})
        if isinstance(extra_params, dict):
            params.update(extra_params)
        req = {"method": method, "params": params}

        transport = (self.cfg.transport or "").strip().lower()
        if transport == "http":
            return self._call_http(req, tool_name=tool_name)
        if transport == "stdio":
            return self._call_stdio(req, tool_name=tool_name)
        raise RuntimeError(f"Unsupported Lean MCP transport: {self.cfg.transport}")

    @staticmethod
    def _normalize_tools(tools: object) -> dict[str, dict[str, object]]:
        normalized = _default_tools()
        if not isinstance(tools, dict):
            return normalized
        for tool_name, raw_cfg in tools.items():
            if not isinstance(raw_cfg, dict):
                continue
            base = normalized.get(tool_name, {"enabled": True, "method": tool_name, "extra_params": {}})
            base = dict(base)
            base["enabled"] = bool(raw_cfg.get("enabled", base.get("enabled", True)))
            base["method"] = str(raw_cfg.get("method") or base.get("method") or tool_name)
            extra_params = raw_cfg.get("extra_params", base.get("extra_params", {}))
            base["extra_params"] = extra_params if isinstance(extra_params, dict) else {}
            normalized[tool_name] = base
        return normalized

    def _select_tools(self, error_summary: str) -> list[str]:
        enabled_tools = [
            tool_name
            for tool_name, tool_cfg in self.cfg.tools.items()
            if bool(tool_cfg.get("enabled", False))
        ]
        if not enabled_tools:
            raise RuntimeError("Lean MCP enabled but no tools are enabled in lean_mcp_tools")

        strategy = (self.cfg.tool_selection_strategy or "single").strip().lower()
        if strategy == "single":
            return enabled_tools[:1]
        if strategy in {"sequential", "all"}:
            return enabled_tools
        if strategy == "fallback":
            return enabled_tools
        if strategy == "error_based":
            err = error_summary.lower()
            preferred: list[str] = []
            if any(token in err for token in ["unknown constant", "unknown identifier", "unsolved constraints", "failed to synthesize"]):
                preferred = ["search", "analyze_prefix", "verify_proof", "suggest_tactics"]
            elif any(token in err for token in ["unsolved goals", "tactic", "goal"]):
                preferred = ["suggest_tactics", "search", "analyze_prefix", "verify_proof"]
            elif any(token in err for token in ["type mismatch", "application type mismatch"]):
                preferred = ["analyze_prefix", "search", "verify_proof", "suggest_tactics"]
            else:
                preferred = ["analyze_prefix", "search", "suggest_tactics", "verify_proof"]
            selected = [tool_name for tool_name in preferred if tool_name in enabled_tools]
            selected.extend(tool_name for tool_name in enabled_tools if tool_name not in selected)
            return selected
        raise RuntimeError(f"Unsupported Lean MCP tool selection strategy: {self.cfg.tool_selection_strategy}")

    @staticmethod
    def _build_search_query(error_summary: str, block_name: str, prefix_text: str) -> str:
        summary = (error_summary or "").strip()
        if summary:
            lines = [line.strip() for line in summary.splitlines() if line.strip()]
            return " | ".join(lines[:3])[:400]
        prefix_lines = [line.strip() for line in prefix_text.splitlines() if line.strip()]
        tail = prefix_lines[-5:]
        if tail:
            return f"{block_name}: {' '.join(tail)}"[:400]
        return block_name[:400]

    @staticmethod
    def _merge_context(base: LeanMCPContext, tool_name: str, new_ctx: LeanMCPContext) -> LeanMCPContext:
        def join(a: str, b: str) -> str:
            return "\n\n".join(x for x in [a, b] if x)

        raw_new = new_ctx.raw
        if (new_ctx.has_content()
                and not (new_ctx.goals or new_ctx.diagnostics or new_ctx.search_results or new_ctx.tactics)
                and raw_new):
            raw_new = f"[{tool_name}]\n{raw_new}"
        return LeanMCPContext(
            goals=join(base.goals, new_ctx.goals),
            diagnostics=join(base.diagnostics, new_ctx.diagnostics),
            search_results=join(base.search_results, new_ctx.search_results),
            tactics=join(base.tactics, new_ctx.tactics),
            raw=join(base.raw, raw_new),
        )

    def _call_http(self, payload: dict, *, tool_name: str = "") -> LeanMCPContext:
        if not self.cfg.endpoint:
            raise RuntimeError("Lean MCP endpoint is empty")

        data = json.dumps(payload).encode("utf-8")
        headers = {
            "Content-Type": "application/json",
            "User-Agent": "lean-benchmark-mcp-client/1.0",
        }
        req = urllib.request.Request(self.cfg.endpoint, data=data, headers=headers, method="POST")
        try:
            with urllib.request.urlopen(req, timeout=self.cfg.timeout_sec) as resp:
                raw = resp.read().decode("utf-8", errors="replace")
        except urllib.error.HTTPError as e:
            detail = e.read().decode("utf-8", errors="replace")
            raise RuntimeError(f"Lean MCP HTTP error {e.code}: {detail[:300]}") from e
        except urllib.error.URLError as e:
            raise RuntimeError(f"Lean MCP connection error: {e.reason}") from e

        return self._parse_response(raw, tool_name=tool_name)

    def _call_stdio(self, payload: dict, *, tool_name: str = "") -> LeanMCPContext:
        if not self.cfg.command:
            raise RuntimeError("Lean MCP command is empty")

        run_env = os.environ.copy()
        for k, v in (self.cfg.env_vars or {}).items():
            key = str(k or "").strip()
            if key and key not in run_env:
                run_env[key] = str(v)

        proc = subprocess.run(
            self.cfg.command,
            input=json.dumps(payload),
            text=True,
            shell=True,
            capture_output=True,
            timeout=self.cfg.timeout_sec,
            check=False,
            env=run_env,
        )
        if proc.returncode != 0:
            msg = (proc.stderr or proc.stdout or "").strip()
            raise RuntimeError(f"Lean MCP stdio exit {proc.returncode}: {msg[:300]}")

        return self._parse_response(proc.stdout, tool_name=tool_name)

    @staticmethod
    def _parse_response(raw: str, *, tool_name: str = "") -> LeanMCPContext:
        raw = (raw or "").strip()
        if not raw:
            return LeanMCPContext()
        try:
            obj = json.loads(raw)
        except json.JSONDecodeError:
            return LeanMCPContext(raw=raw)

        # 兼容两种结构：{"result": {...}} 或直接对象
        body = obj.get("result", obj) if isinstance(obj, dict) else {}
        if not isinstance(body, dict):
            return LeanMCPContext(raw=raw)

        # 按工具类型分派解析
        if tool_name in {"search", "search_mathlib", "mathlib_search"}:
            return LeanMCPClient._parse_search_response(body)
        if tool_name in {"suggest_tactics", "tactic_suggest"}:
            return LeanMCPClient._parse_tactics_response(body)

        # 默认：analyze_prefix / verify_proof 风格
        goals = str(body.get("goals", "") or "")
        diagnostics = str(body.get("diagnostics", "") or "")

        if not goals and not diagnostics:
            # 回退：把结构化内容压成字符串，至少给模型一点可读上下文
            safe_raw = json.dumps(body, ensure_ascii=False)
            return LeanMCPContext(raw=safe_raw)
        return LeanMCPContext(goals=goals, diagnostics=diagnostics)

    @staticmethod
    def _parse_search_response(body: dict) -> LeanMCPContext:
        """解析 search 工具响应，提取含签名的定理列表。"""
        theorem_list = (
            body.get("theorems")
            or body.get("results")
            or body.get("matches")
            or body.get("items")
            or []
        )
        if isinstance(theorem_list, list) and theorem_list:
            lines: list[str] = []
            for i, item in enumerate(theorem_list[:10]):
                if isinstance(item, str):
                    lines.append(f"- `{item}`")
                elif isinstance(item, dict):
                    name = item.get("name") or item.get("id") or f"result_{i}"
                    sig = (
                        item.get("signature")
                        or item.get("type")
                        or item.get("statement")
                        or ""
                    )
                    module = item.get("module") or item.get("source") or ""
                    doc = (item.get("docstring") or item.get("doc") or "")[:100]
                    entry = f"- `{name}`"
                    if module:
                        entry += f" ({module})"
                    if sig:
                        entry += f"\n  ```lean\n  {sig}\n  ```"
                    if doc:
                        entry += f"\n  {doc}"
                    lines.append(entry)
            if lines:
                return LeanMCPContext(search_results="\n".join(lines))
        # 回退：goals/diagnostics 或 raw
        goals = str(body.get("goals", "") or "")
        diagnostics = str(body.get("diagnostics", "") or "")
        if goals or diagnostics:
            return LeanMCPContext(goals=goals, diagnostics=diagnostics)
        return LeanMCPContext(raw=json.dumps(body, ensure_ascii=False))

    @staticmethod
    def _parse_tactics_response(body: dict) -> LeanMCPContext:
        """解析 suggest_tactics 工具响应，提取 tactic 列表。"""
        tactics_list = (
            body.get("tactics")
            or body.get("suggestions")
            or body.get("results")
            or []
        )
        if isinstance(tactics_list, list) and tactics_list:
            lines: list[str] = []
            for item in tactics_list[:10]:
                if isinstance(item, str):
                    lines.append(f"- `{item}`")
                elif isinstance(item, dict):
                    tactic = item.get("tactic") or item.get("name") or str(item)
                    score = item.get("score") or item.get("confidence") or ""
                    entry = f"- `{tactic}`"
                    if score:
                        entry += f" (score: {score})"
                    lines.append(entry)
            if lines:
                return LeanMCPContext(tactics="\n".join(lines))
        # 回退
        goals = str(body.get("goals", "") or "")
        diagnostics = str(body.get("diagnostics", "") or "")
        if goals or diagnostics:
            return LeanMCPContext(goals=goals, diagnostics=diagnostics)
        return LeanMCPContext(raw=json.dumps(body, ensure_ascii=False))
