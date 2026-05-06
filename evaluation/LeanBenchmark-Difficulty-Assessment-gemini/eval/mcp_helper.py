#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""json2lean-style Lean MCP helper for read-only context gathering.

This module mirrors the json2lean approach:
- Prefer direct Python calls into lean-tools-mcp.
- Keep a strict read-only tool allowlist.
- Build staged recovery context using search + local file tools.
"""

from __future__ import annotations

import asyncio
import importlib
import os
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


_READ_ONLY_ALLOWLIST: frozenset[str] = frozenset({
    "lean_goal",
    "lean_term_goal",
    "lean_diagnostic_messages",
    "lean_hover_info",
    "lean_hover",
    "lean_completions",
    "lean_file_outline",
    "lean_file_contents",
    "lean_declaration_file",
    "lean_local_search",
    "lean_leansearch",
    "lean_search",
    "lean_loogle",
    "lean_leanfinder",
    "lean_state_search",
    "lean_hammer_premise",
    "lean_unified_search",
    "lean_llm_query",
    "lean_havelet_extract",
    "lean_analyze_deps",
    "lean_export_decls",
    "lean_code_actions",
})

_MUTATING_TOOLS: frozenset[str] = frozenset({
    "lean_build",
    "lean_apply_patch",
    "lean_run_code",
    "lean_multi_attempt",
})

_LSP_BOUND_TOOLS: frozenset[str] = frozenset({
    "lean_goal",
    "lean_term_goal",
    "lean_diagnostic_messages",
    "lean_hover_info",
    "lean_hover",
    "lean_completions",
    "lean_file_outline",
    "lean_declaration_file",
    "lean_state_search",
    "lean_hammer_premise",
    "lean_local_search",
})

_PROJECT_MANAGER_TOOLS: frozenset[str] = frozenset({"lean_code_actions"})

_MODULE_PATHS: dict[str, str] = {
    "goal": "lean_tools_mcp.tools.goal",
    "diagnostics": "lean_tools_mcp.tools.diagnostics",
    "hover": "lean_tools_mcp.tools.hover",
    "completions": "lean_tools_mcp.tools.completions",
    "code_actions": "lean_tools_mcp.tools.code_actions",
    "file_ops": "lean_tools_mcp.tools.file_ops",
    "search": "lean_tools_mcp.tools.search",
    "unified_search": "lean_tools_mcp.tools.unified_search",
    "llm_tools": "lean_tools_mcp.tools.llm_tools",
    "lean_meta": "lean_tools_mcp.tools.lean_meta",
}

_ALL_TOOL_DEFS: list[tuple[str, str, str]] = [
    ("lean_goal", "goal", "lean_goal"),
    ("lean_term_goal", "goal", "lean_term_goal"),
    ("lean_diagnostic_messages", "diagnostics", "lean_diagnostic_messages"),
    ("lean_hover_info", "hover", "lean_hover_info"),
    ("lean_hover", "hover", "lean_hover_info"),
    ("lean_completions", "completions", "lean_completions"),
    ("lean_code_actions", "code_actions", "lean_code_actions"),
    ("lean_file_outline", "file_ops", "lean_file_outline"),
    ("lean_file_contents", "file_ops", "lean_file_contents"),
    ("lean_declaration_file", "file_ops", "lean_declaration_file"),
    ("lean_local_search", "file_ops", "lean_local_search"),
    ("lean_leansearch", "search", "lean_leansearch"),
    ("lean_search", "search", "lean_leansearch"),
    ("lean_loogle", "search", "lean_loogle"),
    ("lean_leanfinder", "search", "lean_leanfinder"),
    ("lean_state_search", "search", "lean_state_search"),
    ("lean_hammer_premise", "search", "lean_hammer_premise"),
    ("lean_unified_search", "unified_search", "lean_unified_search"),
    ("lean_llm_query", "llm_tools", "lean_llm_query"),
    ("lean_havelet_extract", "lean_meta", "lean_havelet_extract"),
    ("lean_analyze_deps", "lean_meta", "lean_analyze_deps"),
    ("lean_export_decls", "lean_meta", "lean_export_decls"),
]


@dataclass
class MCPGatherResult:
    context_text: str = ""
    call_count: int = 0
    failure_count: int = 0
    used_tools: list[str] = field(default_factory=list)
    failed_tools: list[str] = field(default_factory=list)


def _resolve_local_mcp_repo(mcp_repo_path: str | None) -> Path | None:
    if mcp_repo_path:
        p = Path(mcp_repo_path).expanduser().resolve()
        if p.exists():
            return p
        return None

    here = Path(__file__).resolve()
    candidates = [
        here.parents[2] / "lean-tools-mcp",
        here.parents[1] / "lean-tools-mcp",
    ]
    for p in candidates:
        if p.exists():
            return p.resolve()
    return None


def _load_module(path: str):
    return importlib.import_module(path)


def _normalize_proxy_url(url: str) -> str:
    u = (url or "").strip()
    if not u:
        return u
    if u.lower().startswith("socks://"):
        return "socks5://" + u[len("socks://") :]
    return u


def _apply_proxy_env_overrides() -> None:
    def _set_pair(lower: str, upper: str, value: str) -> None:
        os.environ[lower] = value
        os.environ[upper] = value

    if os.getenv("MCP_USE_ALL_PROXY", "0").strip() != "1":
        os.environ.pop("all_proxy", None)
        os.environ.pop("ALL_PROXY", None)

    for lower, upper in (("http_proxy", "HTTP_PROXY"), ("https_proxy", "HTTPS_PROXY")):
        cur = os.getenv(lower) or os.getenv(upper) or ""
        norm = _normalize_proxy_url(cur)
        if norm:
            _set_pair(lower, upper, norm)


class MCPHelper:
    """Runtime wrapper around lean-tools-mcp read-only tools."""

    def __init__(
        self,
        *,
        project_root: Path,
        lean_path: str = "lean",
        pool_size: int = 1,
        mcp_repo_path: str | None = None,
        enabled_tools: list[str] | None = None,
        codex_home_env_vars: dict[str, str] | None = None,
    ) -> None:
        _apply_proxy_env_overrides()
        if codex_home_env_vars:
            for k, v in codex_home_env_vars.items():
                key = str(k or "").strip()
                if key and key not in os.environ:
                    os.environ[key] = str(v)
        self.project_root = Path(project_root).resolve()
        self.lean_path = lean_path
        self.pool_size = max(1, int(pool_size))

        local_repo = _resolve_local_mcp_repo(mcp_repo_path)
        if local_repo is not None and str(local_repo) not in sys.path:
            sys.path.insert(0, str(local_repo))

        try:
            pool_mod = _load_module("lean_tools_mcp.lsp.pool")
            limiter_mod = _load_module("lean_tools_mcp.clients.rate_limiter")
            project_mod = _load_module("lean_tools_mcp.project.manager")
            llm_mod = _load_module("lean_tools_mcp.llm.client")
            config_mod = _load_module("lean_tools_mcp.config")
        except Exception as err:
            raise RuntimeError(
                "lean-tools-mcp import failed. Install lean-tools-mcp in current env. "
                f"details: {err}"
            ) from err

        self._LSPPool = getattr(pool_mod, "LSPPool")
        self._create_default_limiter = getattr(limiter_mod, "create_default_limiter")
        self._LeanProjectManager = getattr(project_mod, "LeanProjectManager")
        self._LLMClient = getattr(llm_mod, "LLMClient")
        self._load_config = getattr(config_mod, "load_config")

        self._limiter = self._create_default_limiter()
        self._lsp_pool = None
        self._project_manager = None
        self._llm_client = None
        self._tools = self._load_tools(enabled_tools)

    def _load_tools(self, enabled_tools: list[str] | None) -> dict[str, Any]:
        if enabled_tools is not None:
            wanted = frozenset(str(t).strip() for t in enabled_tools if str(t).strip())
            tool_defs = [(n, mk, attr) for (n, mk, attr) in _ALL_TOOL_DEFS if n in wanted]
        else:
            tool_defs = list(_ALL_TOOL_DEFS)

        needed_mod_keys = {mk for (_, mk, _) in tool_defs}
        loaded_mods: dict[str, Any] = {}
        for mk in needed_mod_keys:
            try:
                loaded_mods[mk] = _load_module(_MODULE_PATHS[mk])
            except Exception:
                pass

        result: dict[str, Any] = {}
        for (name, mk, attr) in tool_defs:
            mod = loaded_mods.get(mk)
            if mod is not None:
                fn = getattr(mod, attr, None)
                if fn is not None:
                    result[name] = fn
        return result

    def _ensure_lsp_pool(self):
        if self._lsp_pool is None:
            self._lsp_pool = self._LSPPool(
                project_root=self.project_root,
                pool_size=self.pool_size,
                lean_path=self.lean_path,
            )
        return self._lsp_pool

    def _ensure_project_manager(self):
        if self._project_manager is None:
            self._project_manager = self._LeanProjectManager(
                project_root=self.project_root,
                lsp_pool=self._ensure_lsp_pool(),
                lean_path=self.lean_path,
            )
        return self._project_manager

    def _ensure_llm_client(self):
        if self._llm_client is None:
            cfg = self._load_config(self.project_root, None)
            self._llm_client = self._LLMClient(cfg.llm)
        return self._llm_client

    async def start(self) -> None:
        if self._lsp_pool is not None:
            await self._lsp_pool.start()

    async def shutdown(self) -> None:
        if self._lsp_pool is not None:
            await self._lsp_pool.shutdown()

    async def call_tool(self, name: str, **kwargs: Any) -> str:
        if name in _MUTATING_TOOLS:
            return f"[mcp_helper] BLOCKED mutating tool: {name}"
        if name not in _READ_ONLY_ALLOWLIST:
            return f"[mcp_helper] BLOCKED unknown/unsupported tool: {name}"

        fn = self._tools.get(name)
        if fn is None:
            raise ValueError(f"Unsupported MCP tool: {name}")

        if name == "lean_hover":
            name = "lean_hover_info"
        elif name == "lean_search":
            name = "lean_leansearch"

        if name in {
            "lean_leansearch",
            "lean_unified_search",
            "lean_loogle",
            "lean_leanfinder",
            "lean_state_search",
            "lean_hammer_premise",
        }:
            if "num_results" not in kwargs and "max_results" in kwargs:
                kwargs["num_results"] = kwargs["max_results"]
            kwargs.pop("max_results", None)

        if name in _LSP_BOUND_TOOLS:
            return await fn(self._ensure_lsp_pool(), **kwargs)
        if name in _PROJECT_MANAGER_TOOLS:
            return await fn(self._ensure_project_manager(), **kwargs)
        if name in {"lean_leansearch", "lean_search", "lean_loogle", "lean_leanfinder"}:
            return await fn(self._limiter, **kwargs)
        if name in {"lean_state_search", "lean_hammer_premise"}:
            return await fn(self._limiter, self._ensure_lsp_pool(), **kwargs)
        if name == "lean_unified_search":
            return await fn(self._limiter, **kwargs)
        if name == "lean_llm_query":
            return await fn(self._ensure_llm_client(), **kwargs)
        if name in {"lean_havelet_extract", "lean_analyze_deps", "lean_export_decls"}:
            if "user_project_root" not in kwargs or kwargs.get("user_project_root") is None:
                kwargs["user_project_root"] = str(self.project_root)
            return await fn(**kwargs)
        return await fn(**kwargs)


def _extract_search_queries_from_errors(errors: list[dict[str, Any]], fallback_seed: str) -> list[str]:
    """Extract and rank Lean identifiers from compile errors for MCP searches.

    Ranking policy (high -> low):
    1) Type/goal-shape identifiers from "has type" / "expected to have type"
    2) Backtick-quoted identifiers that usually come from concrete declarations
    3) Generic CamelCase/dotted identifiers
    4) Unknown-identifier names (kept as fallback only)
    """
    seen: set[str] = set()
    type_names: list[str] = []
    lemma_names: list[str] = []
    generic_names: list[str] = []
    unknown_ids: list[str] = []
    unknown_seen: set[str] = set()

    _SKIP_WORDS = frozenset({
        "True", "False", "None", "Some", "Type", "Prop", "Sort",
        "After", "Found", "Error", "Invalid", "Unknown", "Cannot",
        "Lean", "Nat", "Int", "Real", "Bool", "String", "List",
        "Array", "Fin", "Set", "And", "Not", "Iff", "With",
        "For", "The", "All", "Any", "Has", "Get", "Put",
    })

    def _looks_generated_name(q: str) -> bool:
        # Long snake_case names are frequently hallucinated by the model.
        return bool(re.match(r"^[a-z][A-Za-z0-9]*(?:_[A-Za-z0-9]+){2,}$", q)) and len(q) >= 20

    def _normalize(q: str) -> str:
        return q.strip()

    def _add(bucket: list[str], q: str, *, allow_skip_words: bool = True) -> None:
        q = _normalize(q)
        q = q.strip()
        if not q or len(q) < 3:
            return
        # Ignore temp-file artifacts like mcp_prefix_xxxxx that hurt search quality.
        if re.match(r"^mcp_prefix_[A-Za-z0-9_]+$", q):
            return
        if allow_skip_words and q in _SKIP_WORDS:
            return
        if q not in seen:
            seen.add(q)
            bucket.append(q)

    def _add_unknown(q: str) -> None:
        q = _normalize(q)
        if not q or len(q) < 3:
            return
        if re.match(r"^mcp_prefix_[A-Za-z0-9_]+$", q):
            return
        # Extremely likely hallucinated aliases are still retained but at fallback level.
        if q in unknown_seen:
            return
        unknown_seen.add(q)
        unknown_ids.append(q)

    for err in (errors or [])[:5]:
        # Normalize multi-line whitespace so regexes don't need re.DOTALL
        msg = re.sub(r"\s+", " ", str(err.get("message", "")))

        # 1. unknown identifier / constant  'Foo.bar'
        for m in re.finditer(r"unknown (?:identifier|constant) ['\"\`]([A-Za-z0-9_.]+)['\"\`]", msg, re.IGNORECASE):
            _add_unknown(m.group(1))

        # 2. backtick-quoted Lean identifiers  `convexHull_min`
        for m in re.finditer(r"`([A-Za-z][A-Za-z0-9_.]{3,})`", msg):
            q = m.group(1)
            if q not in unknown_seen:
                _add(lemma_names, q)

        # 3. "has type  (ConcreteType ..." — extract the first identifier after optional paren
        for m in re.finditer(r"has type\s+\(?([A-Za-z][A-Za-z0-9_.]+)", msg):
            _add(type_names, m.group(1))

        # 4. "expected to have type  (ConcreteType ..."
        for m in re.finditer(r"expected to have type\s+\(?([A-Za-z][A-Za-z0-9_.]+)", msg):
            _add(type_names, m.group(1))

        # 5. CamelCase / dotted names — Lean type or namespace identifiers (e.g. ConvexHull, Finset.sum)
        for m in re.finditer(r"\b([A-Z][A-Za-z0-9]{3,}(?:\.[A-Za-z][A-Za-z0-9]*)*)\b", msg):
            _add(generic_names, m.group(1))

        # 6. snake_case lemma-style names with at least 2 underscores (e.g. convex_hull_min)
        for m in re.finditer(r"\b([a-z][a-zA-Z0-9]*(?:_[a-zA-Z][a-zA-Z0-9]*){2,})\b", msg):
            name = m.group(1)
            if len(name) > 8 and name not in unknown_seen:
                _add(lemma_names, name)

    # Demote likely hallucinated unknown names to the end of the unknown bucket.
    unknown_ids_sorted = sorted(unknown_ids, key=lambda q: (1 if _looks_generated_name(q) else 0, len(q)))

    queries: list[str] = []
    for q in [*type_names, *lemma_names, *generic_names, *unknown_ids_sorted, _normalize(fallback_seed)]:
        q = _normalize(q)
        if not q or q in queries:
            continue
        queries.append(q)

    return queries[:8]


def gather_recovery_context(
    *,
    file_path: Path,
    project_root: Path,
    lean_path: str = "lean",
    pool_size: int = 1,
    focus_line: int | None = None,
    focus_column: int | None = None,
    mcp_repo_path: str | None = None,
    tool_mode: str = "targeted",
    errors: list[dict[str, Any]] | None = None,
    enabled_tools: list[str] | None = None,
    query_seed: str | None = None,
    codex_home_env_vars: dict[str, str] | None = None,
) -> MCPGatherResult:
    mode = (tool_mode or "").strip().lower()
    if mode not in {"focused", "targeted", "all"}:
        mode = "targeted"

    # Prefer semantic seed (e.g. block name) over temp file stem.
    search_queries = _extract_search_queries_from_errors(
        errors or [],
        (query_seed or "").strip() or file_path.stem,
    )

    def _is_low_priority_primary(q: str) -> bool:
        # Avoid using probable hallucinated unknown names as the top unified search query.
        if len(q) >= 20 and "_" in q:
            return True
        return bool(re.match(r"^[a-z][A-Za-z0-9]*(?:_[A-Za-z0-9]+){2,}$", q))

    primary_query = file_path.stem
    if search_queries:
        primary_query = next((q for q in search_queries if not _is_low_priority_primary(q)), search_queries[0])
    col_arg = int(focus_column) if (focus_column and focus_column > 0) else 1

    calls: list[dict[str, Any]] = []
    if enabled_tools:
        for name in enabled_tools:
            name = str(name or "").strip()
            if not name:
                continue
            if name == "lean_unified_search":
                calls.append({"key": "unified_search", "name": name, "args": {"query": primary_query, "max_results": 10}})
            elif name in {"lean_leansearch", "lean_search", "lean_loogle", "lean_leanfinder"}:
                # Search providers are noisy when over-queried; keep at most 2 focused queries.
                for qi, q in enumerate(search_queries[:2]):
                    calls.append({"key": f"{name}_{qi}", "name": name, "args": {"query": q, "max_results": 10}})
            elif name == "lean_file_contents":
                calls.append({"key": "file_contents", "name": name, "args": {"file_path": str(file_path)}})
            elif name == "lean_local_search" and focus_line and focus_line > 0:
                calls.append({
                    "key": "local_search",
                    "name": name,
                    "args": {"file_path": str(file_path), "line": int(focus_line), "column": col_arg, "max_results": 10},
                })
            elif name in {"lean_hover", "lean_hover_info"} and focus_line and focus_line > 0:
                calls.append({
                    "key": "hover",
                    "name": name,
                    "args": {"file_path": str(file_path), "line": int(focus_line), "column": col_arg},
                })
    else:
        calls.append({"key": "unified_search", "name": "lean_unified_search", "args": {"query": primary_query, "max_results": 10}})
        if mode in {"targeted", "all"}:
            for provider in ["lean_leansearch", "lean_loogle", "lean_leanfinder"]:
                for qi, q in enumerate(search_queries[:2]):
                    calls.append({"key": f"{provider}_{qi}", "name": provider, "args": {"query": q, "max_results": 10}})
        if mode == "all":
            calls.append({"key": "file_contents", "name": "lean_file_contents", "args": {"file_path": str(file_path)}})
            if focus_line and focus_line > 0:
                calls.append({
                    "key": "local_search",
                    "name": "lean_local_search",
                    "args": {"file_path": str(file_path), "line": int(focus_line), "column": col_arg, "max_results": 10},
                })

    calls = calls[:20]
    tool_names = {
        str(call.get("name", "")).strip()
        for call in calls
        if str(call.get("name", "")).strip()
    }
    needs_lsp = bool(tool_names & (_LSP_BOUND_TOOLS | _PROJECT_MANAGER_TOOLS))

    async def _run() -> dict[str, str]:
        helper = MCPHelper(
            project_root=project_root,
            lean_path=lean_path,
            pool_size=pool_size,
            mcp_repo_path=mcp_repo_path,
            enabled_tools=enabled_tools,
            codex_home_env_vars=codex_home_env_vars,
        )
        out: dict[str, str] = {}
        if needs_lsp:
            await helper.start()
        try:
            for i, call in enumerate(calls, 1):
                name = str(call.get("name", "")).strip()
                args = call.get("args", {}) or {}
                key = str(call.get("key") or f"{i}:{name}")
                try:
                    out[key] = await helper.call_tool(name, **args)
                except Exception as err:
                    out[key] = f"[error] {name}: {err}"
            return out
        finally:
            if needs_lsp:
                await helper.shutdown()

    result = asyncio.run(_run())

    sections: list[str] = []
    for key, heading in [
        ("file_contents", "MCP file-contents"),
        ("local_search", "MCP local-search"),
        ("unified_search", "MCP unified-search"),
    ]:
        if key in result and result[key].strip() and not result[key].startswith("[error]"):
            sections.extend([f"== {heading} ==", result[key].strip(), ""])

    for key, value in sorted(result.items()):
        if key in {"file_contents", "local_search", "unified_search"}:
            continue
        if value.strip() and not value.startswith("[error]") and "[Loogle] Error:" not in value:
            sections.extend([f"== MCP {key} ==", value.strip(), ""])

    failed_tools: list[str] = []
    used_tools: list[str] = []
    for call in calls:
        cname = str(call.get("name", "")).strip()
        ckey = str(call.get("key") or "")
        if not cname or not ckey:
            continue
        val = result.get(ckey, "")
        is_failed = isinstance(val, str) and (
            val.startswith("[error]")
            or "[Loogle] Error:" in val
            or "[LeanSearch] Error:" in val
            or "[LeanFinder] Error:" in val
        )
        if is_failed:
            failed_tools.append(cname)
        else:
            used_tools.append(cname)

    return MCPGatherResult(
        context_text="\n".join(sections).strip(),
        call_count=len(calls),
        failure_count=len(failed_tools),
        used_tools=sorted(set(used_tools)),
        failed_tools=sorted(set(failed_tools)),
    )
