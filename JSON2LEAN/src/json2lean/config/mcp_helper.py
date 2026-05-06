"""Lean Tools MCP helper utilities.

This module provides:
- A reusable runtime that can call lean-tools-mcp tools from Python directly.
- A compatibility helper ``gather_recovery_context`` used by recover.py.
- Strict read-only safety: mutating tools are blocked by code path.
- Staged fallback search strategy with caching/de-duplication.

Resolution strategy for lean-tools-mcp:
1) Prefer local repo path (explicit ``mcp_repo_path`` or auto-detected sibling).
2) Fallback to installed package in current Python environment.
"""

from __future__ import annotations

import asyncio
import importlib
import os
import re
import stat
import sys
from pathlib import Path
from typing import Any


# ---------------------------------------------------------------------------
# Read-only safety: allowlist of non-mutating tools
# ---------------------------------------------------------------------------

_READ_ONLY_ALLOWLIST: frozenset[str] = frozenset({
    # LSP query tools
    "lean_goal",
    "lean_term_goal",
    "lean_diagnostic_messages",
    "lean_hover_info",
    "lean_hover",           # alias used by newer lean-tools-mcp versions
    "lean_completions",
    # File inspection (read-only)
    "lean_file_outline",
    "lean_file_contents",
    "lean_declaration_file",
    "lean_local_search",
    # Search tools
    "lean_leansearch",
    "lean_search",          # alias for lean_leansearch
    "lean_loogle",
    "lean_leanfinder",
    "lean_state_search",
    "lean_hammer_premise",
    "lean_unified_search",
    # Meta / analysis (read-only)
    "lean_havelet_extract",
    "lean_analyze_deps",
    "lean_export_decls",
    # LLM query (read-only)
    "lean_llm_query",
    # Code actions (read-only inspection)
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
})

_PROJECT_MANAGER_TOOLS: frozenset[str] = frozenset({
    "lean_code_actions",
    "lean_build",
})

_SEARCH_ONLY_TOOLS: frozenset[str] = frozenset({
    "lean_unified_search",
    "lean_leansearch",
    "lean_loogle",
    "lean_leanfinder",
    "lean_file_contents",
    "lean_local_search",
    "lean_llm_query",
})

_LEAN_DIR_SEGMENTS = {"lean", ".lake"}

# ---------------------------------------------------------------------------
# Module-to-tool definitions: used for selective, per-tool module loading.
# ---------------------------------------------------------------------------

# Module key -> importable path inside lean_tools_mcp
_MODULE_PATHS: dict[str, str] = {
    "goal":          "lean_tools_mcp.tools.goal",
    "diagnostics":   "lean_tools_mcp.tools.diagnostics",
    "hover":         "lean_tools_mcp.tools.hover",
    "completions":   "lean_tools_mcp.tools.completions",
    "code_actions":  "lean_tools_mcp.tools.code_actions",
    "file_ops":      "lean_tools_mcp.tools.file_ops",
    "build":         "lean_tools_mcp.tools.build",
    "patch":         "lean_tools_mcp.tools.patch",
    "run_code":      "lean_tools_mcp.tools.run_code",
    "multi_attempt": "lean_tools_mcp.tools.multi_attempt",
    "search":        "lean_tools_mcp.tools.search",
    "unified_search":"lean_tools_mcp.tools.unified_search",
    "llm_tools":     "lean_tools_mcp.tools.llm_tools",
    "lean_meta":     "lean_tools_mcp.tools.lean_meta",
}

# (tool_name, module_key, attr_name) — canonical registry of every supported tool
_ALL_TOOL_DEFS: list[tuple[str, str, str]] = [
    ("lean_goal",                "goal",          "lean_goal"),
    ("lean_term_goal",           "goal",          "lean_term_goal"),
    ("lean_diagnostic_messages", "diagnostics",   "lean_diagnostic_messages"),
    ("lean_hover_info",          "hover",         "lean_hover_info"),
    # lean_hover: alias for lean_hover_info (newer lean-tools-mcp versions use this name;
    #             the installed version only exports lean_hover_info)
    ("lean_hover",               "hover",         "lean_hover_info"),
    ("lean_completions",         "completions",   "lean_completions"),
    ("lean_code_actions",        "code_actions",  "lean_code_actions"),
    ("lean_file_outline",        "file_ops",      "lean_file_outline"),
    ("lean_file_contents",       "file_ops",      "lean_file_contents"),
    ("lean_declaration_file",    "file_ops",      "lean_declaration_file"),
    ("lean_local_search",        "file_ops",      "lean_local_search"),
    ("lean_build",               "build",         "lean_build"),
    ("lean_apply_patch",         "patch",         "lean_apply_patch"),
    ("lean_run_code",            "run_code",      "lean_run_code"),
    ("lean_multi_attempt",       "multi_attempt", "lean_multi_attempt"),
    ("lean_leansearch",          "search",        "lean_leansearch"),
    # lean_search: alias for lean_leansearch (the installed package exports lean_leansearch)
    ("lean_search",              "search",        "lean_leansearch"),
    ("lean_loogle",              "search",        "lean_loogle"),
    ("lean_leanfinder",          "search",        "lean_leanfinder"),
    ("lean_state_search",        "search",        "lean_state_search"),
    ("lean_hammer_premise",      "search",        "lean_hammer_premise"),
    ("lean_unified_search",      "unified_search","lean_unified_search"),
    ("lean_llm_query",           "llm_tools",     "lean_llm_query"),
    ("lean_havelet_extract",     "lean_meta",     "lean_havelet_extract"),
    ("lean_analyze_deps",        "lean_meta",     "lean_analyze_deps"),
    ("lean_export_decls",        "lean_meta",     "lean_export_decls"),
]


def _resolve_local_mcp_repo(mcp_repo_path: str | None) -> Path | None:
    """Return a usable local lean-tools-mcp repo path, if available."""
    if mcp_repo_path:
        p = Path(mcp_repo_path).expanduser().resolve()
        if p.exists():
            return p
        return None

    here = Path(__file__).resolve()
    candidates = [
        here.parents[3] / "lean-tools-mcp",  # sibling of JSON2LEAN
        here.parents[2] / "lean-tools-mcp",  # nested under JSON2LEAN
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
    # Some lean-tools-mcp/httpx call paths reject "socks://", but accept "socks5://".
    if u.lower().startswith("socks://"):
        return "socks5://" + u[len("socks://") :]
    return u


def _apply_mcp_proxy_env_overrides() -> None:
    """Apply MCP-specific proxy env and normalize incompatible schemes.

    Priority:
    1) MCP_*_PROXY / MCP_NO_PROXY when present.
    2) Existing system proxy env, with socks:// normalized to socks5://.
    """

    def _set_pair(lower: str, upper: str, value: str) -> None:
        os.environ[lower] = value
        os.environ[upper] = value

    # Explicit MCP-specific overrides (when provided).
    mcp_http = _normalize_proxy_url(os.getenv("MCP_HTTP_PROXY", ""))
    mcp_https = _normalize_proxy_url(os.getenv("MCP_HTTPS_PROXY", ""))
    mcp_all = _normalize_proxy_url(os.getenv("MCP_ALL_PROXY", ""))
    mcp_no = os.getenv("MCP_NO_PROXY", "").strip()
    use_all_proxy = os.getenv("MCP_USE_ALL_PROXY", "0").strip() == "1"

    if mcp_http:
        _set_pair("http_proxy", "HTTP_PROXY", mcp_http)
    if mcp_https:
        _set_pair("https_proxy", "HTTPS_PROXY", mcp_https)
    if mcp_all:
        _set_pair("all_proxy", "ALL_PROXY", mcp_all)
    if mcp_no:
        _set_pair("no_proxy", "NO_PROXY", mcp_no)

    # In many user envs ALL_PROXY is set to a SOCKS endpoint that search backends
    # cannot use reliably. Prefer HTTP(S) proxies unless explicitly requested.
    if not mcp_all and not use_all_proxy:
        os.environ.pop("all_proxy", None)
        os.environ.pop("ALL_PROXY", None)

    # Fallback normalization for existing env vars.
    for lower, upper in (
        ("http_proxy", "HTTP_PROXY"),
        ("https_proxy", "HTTPS_PROXY"),
        *((("all_proxy", "ALL_PROXY"),) if (mcp_all or use_all_proxy) else ()),
    ):
        cur = os.getenv(lower) or os.getenv(upper) or ""
        norm = _normalize_proxy_url(cur)
        if norm:
            _set_pair(lower, upper, norm)


class MCPHelper:
    """Runtime wrapper around lean-tools-mcp tools."""

    def __init__(
        self,
        *,
        project_root: Path,
        lean_path: str = "lean",
        pool_size: int = 1,
        mcp_repo_path: str | None = None,
        llm_config_path: str | None = None,
        enabled_tools: list[str] | None = None,
    ) -> None:
        _apply_mcp_proxy_env_overrides()

        self.project_root = Path(project_root).resolve()
        self.lean_path = lean_path
        self.pool_size = max(1, int(pool_size))
        self.llm_config_path = llm_config_path

        local_repo = _resolve_local_mcp_repo(mcp_repo_path)
        if local_repo is not None and str(local_repo) not in sys.path:
            sys.path.insert(0, str(local_repo))

        try:
            pool_mod = _load_module("lean_tools_mcp.lsp.pool")
            limiter_mod = _load_module("lean_tools_mcp.clients.rate_limiter")
            project_mod = _load_module("lean_tools_mcp.project.manager")
            config_mod = _load_module("lean_tools_mcp.config")
            llm_mod = _load_module("lean_tools_mcp.llm.client")
        except Exception as err:  # pragma: no cover
            raise RuntimeError(
                "lean-tools-mcp import failed. Install lean-tools-mcp in current env. "
                f"details: {err}"
            ) from err

        self._LSPPool = getattr(pool_mod, "LSPPool")
        self._create_default_limiter = getattr(limiter_mod, "create_default_limiter")
        self._LeanProjectManager = getattr(project_mod, "LeanProjectManager")
        self._load_mcp_config = getattr(config_mod, "load_config")
        self._LLMClient = getattr(llm_mod, "LLMClient")

        self._limiter = self._create_default_limiter()
        self._lsp_pool = None
        self._project_manager = None
        self._llm_client = None
        self._tools = self._load_tools(enabled_tools)

    def _build_llm_client(self):
        cfg = self._load_mcp_config(self.project_root, self.llm_config_path)
        return self._LLMClient(cfg.llm)

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
            self._llm_client = self._build_llm_client()
        return self._llm_client

    def _load_tools(self, enabled_tools: list[str] | None) -> dict[str, Any]:
        """Import only the tool modules needed for *enabled_tools*.

        If *enabled_tools* is ``None`` all tools are attempted.
        Modules that fail to import are skipped gracefully (their tools are
        simply absent from the returned dict).  A single log line reports
        exactly which tools were successfully loaded.
        """
        # Decide which (tool_name, module_key, attr) triples are wanted
        if enabled_tools is not None:
            wanted: frozenset[str] = frozenset(enabled_tools)
            tool_defs = [(n, mk, attr) for (n, mk, attr) in _ALL_TOOL_DEFS if n in wanted]
        else:
            tool_defs = list(_ALL_TOOL_DEFS)

        # Collect the unique module keys we actually need
        needed_mod_keys = {mk for (_, mk, _) in tool_defs}

        # Import each required module; skip gracefully on failure
        loaded_mods: dict[str, Any] = {}
        for mk in needed_mod_keys:
            try:
                loaded_mods[mk] = _load_module(_MODULE_PATHS[mk])
            except Exception:
                pass  # tool entries for this module will be absent

        # Build the tool function dict from successfully-loaded modules
        result: dict[str, Any] = {}
        for (name, mk, attr) in tool_defs:
            mod = loaded_mods.get(mk)
            if mod is not None:
                fn = getattr(mod, attr, None)
                if fn is not None:
                    result[name] = fn

        # Report exactly what was loaded
        if result:
            names_str = ", ".join(sorted(result))
            print(
                f"[mcp_helper] Loaded tools ({len(result)}): {names_str}",
                file=sys.stderr,
            )
        else:
            print("[mcp_helper] WARNING: no MCP tools loaded", file=sys.stderr)

        return result

    async def start(self) -> None:
        if self._lsp_pool is not None:
            await self._lsp_pool.start()

    async def shutdown(self) -> None:
        if self._lsp_pool is not None:
            await self._lsp_pool.shutdown()

    async def call_tool(self, name: str, **kwargs: Any) -> str:
        if name == "ask_math_oracle":
            return (
                "ask_math_oracle is a companion MCP service and is not bundled in "
                "lean-tools-mcp Python package. Install/run ask-math-oracle-mcp separately."
            )

        # --- Read-only safety gate ---
        if name in _MUTATING_TOOLS:
            msg = f"[mcp_helper] BLOCKED mutating tool: {name}"
            print(msg, file=sys.stderr)
            return msg
        if name not in _READ_ONLY_ALLOWLIST:
            msg = f"[mcp_helper] BLOCKED unknown/unsupported tool: {name}"
            print(msg, file=sys.stderr)
            return msg
        # Block any tool call whose file_path targets lean/ or .lake
        file_arg = str(kwargs.get("file_path", "") or "")
        if file_arg:
            resolved = Path(file_arg).resolve()
            parts_lower = [p.lower() for p in resolved.parts]
            # Allow operations inside our own lean project, but block writes
            # (handled by the allowlist above — only read tools reach here)

        fn = self._tools.get(name)
        if fn is None:
            raise ValueError(f"Unsupported MCP tool: {name}")

        # lean-tools-mcp version compatibility shim:
        # - Some versions reject `max_results`; use `num_results`.
        # - lean_hover / lean_search: name aliases — remap to canonical names for dispatch.
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
        if name in {
            "lean_goal",
            "lean_term_goal",
            "lean_diagnostic_messages",
            "lean_hover_info",
            "lean_hover",
            "lean_completions",
            "lean_file_outline",
            "lean_declaration_file",
            "lean_run_code",
            "lean_multi_attempt",
        }:
            return await fn(self._ensure_lsp_pool(), **kwargs)

        if name in {"lean_code_actions", "lean_build"}:
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


# ---------------------------------------------------------------------------
# .lake write-protection: prevent LSP-triggered lake builds from deleting
# pre-cached package .olean files (e.g. Mathlib) during MCP operations.
# ---------------------------------------------------------------------------

def _collect_lake_package_lib_dirs(project_root: Path) -> list[tuple[Path, int]]:
    """Return (dir, original_mode) for every directory inside package
    .lake/build/lib trees under project_root/.lake/packages/.

    Only package (dependency) lib dirs are protected, NOT the project's own
    .lake/build tree, so the Lean LSP can still write its own build artefacts.
    """
    packages_dir = (project_root / ".lake" / "packages").resolve()
    if not packages_dir.is_dir():
        return []

    targets: list[Path] = []
    try:
        for pkg in sorted(packages_dir.iterdir()):
            if not pkg.is_dir():
                continue
            lib_dir = pkg / ".lake" / "build" / "lib"
            if lib_dir.is_dir():
                targets.append(lib_dir.resolve())
    except OSError:
        return []

    all_dirs: list[tuple[Path, int]] = []
    seen: set[Path] = set()
    _MAX_DIRS = 5_000
    for target in targets:
        try:
            for p in [target, *target.rglob("*")]:
                if len(all_dirs) >= _MAX_DIRS:
                    break
                if p.is_dir() and p not in seen:
                    seen.add(p)
                    try:
                        all_dirs.append((p, p.stat().st_mode))
                    except OSError:
                        pass
        except OSError:
            pass
    return all_dirs


def _apply_lake_write_protection(dirs: list[tuple[Path, int]]) -> None:
    """Remove write bits from directories so files inside cannot be deleted."""
    count = 0
    for d, mode in dirs:
        try:
            d.chmod(mode & ~(stat.S_IWRITE | stat.S_IWGRP | stat.S_IWOTH))
            count += 1
        except OSError:
            pass
    if count:
        print(
            f"[mcp_helper] .lake write-protect: locked {count} package lib dir(s) read-only",
            file=sys.stderr,
        )


def _restore_lake_write_protection(dirs: list[tuple[Path, int]]) -> None:
    """Restore original write permissions after MCP operations complete."""
    restored = 0
    for d, mode in dirs:
        try:
            if d.exists():
                d.chmod(mode)
                restored += 1
        except OSError:
            pass
    if dirs:
        print(
            f"[mcp_helper] .lake write-protect: restored {restored}/{len(dirs)} dir(s)",
            file=sys.stderr,
        )


async def call_all_tools_async(
    *,
    project_root: Path,
    tool_calls: list[dict[str, Any]],
    lean_path: str = "lean",
    pool_size: int = 1,
    mcp_repo_path: str | None = None,
    llm_config_path: str | None = None,
    enabled_tools: list[str] | None = None,
) -> dict[str, str]:
    # Protect package .olean artefacts before starting the Lean LSP server.
    # The LSP (started via LSPPool.start()) runs `lake env lean --server` which
    # can trigger incremental builds that delete pre-cached dependency .olean
    # files (e.g. Mathlib).  Making the package lib directories non-writable at
    # the OS level prevents deletion/creation inside them while still allowing
    # the LSP to READ the existing .olean files for diagnostics.
    tool_names = {
        str(call.get("name", "")).strip()
        for call in tool_calls
        if str(call.get("name", "")).strip()
    }
    needs_lsp = bool(tool_names & (_LSP_BOUND_TOOLS | _PROJECT_MANAGER_TOOLS))
    _lake_dirs = _collect_lake_package_lib_dirs(project_root) if needs_lsp else []
    if needs_lsp:
        _apply_lake_write_protection(_lake_dirs)
    try:
        helper = MCPHelper(
            project_root=project_root,
            lean_path=lean_path,
            pool_size=pool_size,
            mcp_repo_path=mcp_repo_path,
            llm_config_path=llm_config_path,
            enabled_tools=enabled_tools,
        )

        # If caller supplied an enabled_tools whitelist, filter tool_calls
        # to only include calls whose tool name is permitted (including
        # alias mapping). This prevents invoking tools that user didn't
        # intend to allow via settings.
        if enabled_tools is not None:
            enabled_set = set(enabled_tools)
            # Build name->attr mapping from _ALL_TOOL_DEFS for alias resolution
            name_to_attr: dict[str, str] = {n: attr for (n, _mk, attr) in _ALL_TOOL_DEFS}
            filtered_calls: list[dict[str, Any]] = []
            skipped: list[str] = []
            for call in tool_calls:
                cname = str(call.get("name", "")).strip()
                keep = False
                if cname in enabled_set:
                    keep = True
                else:
                    # If cname maps to an attr, allow if any enabled name maps
                    # to the same attr (alias match).
                    attr = name_to_attr.get(cname)
                    if attr is not None:
                        for en in enabled_set:
                            if name_to_attr.get(en) == attr:
                                keep = True
                                break
                if keep:
                    filtered_calls.append(call)
                else:
                    skipped.append(cname)
            if skipped:
                print(f"[mcp_helper] Skipping MCP calls not in enabled_tools: {', '.join(sorted(set(skipped)))}", file=sys.stderr)
            tool_calls = filtered_calls

        out: dict[str, str] = {}
        if needs_lsp:
            await helper.start()
        try:
            for i, call in enumerate(tool_calls, 1):
                name = str(call.get("name", "")).strip()
                args = call.get("args", {}) or {}
                key = call.get("key") or f"{i}:{name}"
                try:
                    out[str(key)] = await helper.call_tool(name, **args)
                except Exception as err:
                    out[str(key)] = f"[error] {name}: {err}"
            return out
        finally:
            if needs_lsp:
                await helper.shutdown()
    finally:
        if needs_lsp:
            _restore_lake_write_protection(_lake_dirs)


def call_all_tools(
    *,
    project_root: Path,
    tool_calls: list[dict[str, Any]],
    lean_path: str = "lean",
    pool_size: int = 1,
    mcp_repo_path: str | None = None,
    llm_config_path: str | None = None,
    enabled_tools: list[str] | None = None,
) -> dict[str, str]:
    return asyncio.run(
        call_all_tools_async(
            project_root=project_root,
            tool_calls=tool_calls,
            lean_path=lean_path,
            pool_size=pool_size,
            mcp_repo_path=mcp_repo_path,
            llm_config_path=llm_config_path,
            enabled_tools=enabled_tools,
        )
    )


def _extract_search_queries_from_errors(errors: list[dict[str, Any]], file_stem: str) -> list[str]:
    """Derive search queries from compiler error messages and declaration names."""
    queries: list[str] = []
    seen: set[str] = set()

    def _add(q: str) -> None:
        q = q.strip()
        if q and q not in seen:
            seen.add(q)
            queries.append(q)

    for err in (errors or [])[:5]:
        msg = str(err.get("message", ""))
        # Extract unknown identifier names
        for m in re.finditer(r"unknown (?:identifier|constant) ['\"`]([A-Za-z0-9_.]+)['\"`]", msg):
            _add(m.group(1))
        # Extract "expected X, got Y" type hints
        for m in re.finditer(r"expected\s+['\"`]?([A-Za-z][A-Za-z0-9_.]+)", msg):
            _add(m.group(1))
        # Extract "has type X but is expected to have type Y"
        for m in re.finditer(r"has type\s+([A-Za-z][A-Za-z0-9_.]+)", msg):
            _add(m.group(1))
        # Declaration names from "already declared"
        for m in re.finditer(r"([A-Za-z_][A-Za-z0-9_']*)\s+has already been declared", msg):
            _add(m.group(1))

    # Always include file stem as fallback
    _add(file_stem)
    return queries[:6]  # Cap to avoid excessive calls


class _SearchCache:
    """Lightweight per-recovery-attempt cache for search query deduplication."""

    def __init__(self) -> None:
        self._cache: dict[str, str] = {}

    def get(self, key: str) -> str | None:
        return self._cache.get(key)

    def put(self, key: str, value: str) -> None:
        self._cache[key] = value

    def has(self, key: str) -> bool:
        return key in self._cache


def gather_recovery_context(
    *,
    file_path: Path,
    project_root: Path,
    lean_path: str = "lean",
    pool_size: int = 1,
    focus_line: int | None = None,
    focus_column: int | None = None,
    mcp_repo_path: str | None = None,
    tool_mode: str = "focused",
    errors: list[dict[str, Any]] | None = None,
    enabled_tools: list[str] | None = None,
) -> str:
    """Gather recovery/translation context from MCP tools.

    Behavior:
    - If ``enabled_tools`` is provided, treat it as an ordered execution list.
    - Otherwise use mode defaults:
      - ``targeted``: unified + search providers.
      - ``all``: targeted + file/local context.
      - ``focused``: unified only.
    """
    mode = (tool_mode or "").strip().lower()
    cache = _SearchCache()

    search_queries = _extract_search_queries_from_errors(errors or [], file_path.stem)
    primary_query = search_queries[0] if search_queries else file_path.stem
    col_arg = int(focus_column) if (focus_column and focus_column > 0) else 1

    def _add_query_tool_calls(name: str, key_prefix: str) -> None:
        for qi, q in enumerate(search_queries[:3]):
            cache_key = f"{name}:{q}"
            if cache.has(cache_key):
                continue
            cache.put(cache_key, "__pending__")
            calls.append({
                "key": f"{key_prefix}_{qi}",
                "name": name,
                "args": {"query": q, "max_results": 10},
            })

    calls: list[dict[str, Any]] = []
    configured_tools: list[str] | None = None
    if enabled_tools is not None:
        seen: set[str] = set()
        configured_tools = []
        for name in enabled_tools:
            n = str(name or "").strip()
            if n and n not in seen:
                seen.add(n)
                configured_tools.append(n)

    if configured_tools is not None:
        for name in configured_tools:
            if name == "lean_unified_search":
                cache_key = f"unified_search:{primary_query}"
                if not cache.has(cache_key):
                    cache.put(cache_key, "__pending__")
                    calls.append({
                        "key": "unified_search",
                        "name": "lean_unified_search",
                        "args": {"query": primary_query, "max_results": 10},
                    })
                continue
            if name in {"lean_leansearch", "lean_search"}:
                _add_query_tool_calls(name, "leansearch")
                continue
            if name == "lean_loogle":
                _add_query_tool_calls(name, "loogle")
                continue
            if name == "lean_leanfinder":
                _add_query_tool_calls(name, "leanfinder")
                continue
            if name == "lean_file_contents":
                calls.append({
                    "key": "file_contents",
                    "name": "lean_file_contents",
                    "args": {"file_path": str(file_path)},
                })
                continue
            if name == "lean_local_search" and focus_line and focus_line > 0:
                calls.append({
                    "key": "local_search",
                    "name": "lean_local_search",
                    "args": {
                        "file_path": str(file_path),
                        "line": int(focus_line),
                        "column": col_arg,
                        "max_results": 10,
                    },
                })
                continue
            if name in {"lean_hover", "lean_hover_info"} and focus_line and focus_line > 0:
                calls.append({
                    "key": "hover",
                    "name": name,
                    "args": {
                        "file_path": str(file_path),
                        "line": int(focus_line),
                        "column": col_arg,
                    },
                })
                continue
    else:
        calls.append({
            "key": "unified_search",
            "name": "lean_unified_search",
            "args": {"query": primary_query, "max_results": 10},
        })
        cache.put(f"unified_search:{primary_query}", "__pending__")

        if mode in {"targeted", "all"}:
            for provider in ["lean_leansearch", "lean_loogle", "lean_leanfinder"]:
                _add_query_tool_calls(provider, provider.replace("lean_", ""))

        if mode == "all":
            calls.append({
                "key": "file_contents",
                "name": "lean_file_contents",
                "args": {"file_path": str(file_path)},
            })
            if focus_line and focus_line > 0:
                calls.append({
                    "key": "local_search",
                    "name": "lean_local_search",
                    "args": {
                        "file_path": str(file_path),
                        "line": int(focus_line),
                        "column": col_arg,
                        "max_results": 10,
                    },
                })
    # Apply early-exit limit: cap total calls
    _MAX_CALLS_PER_ATTEMPT = 20
    if len(calls) > _MAX_CALLS_PER_ATTEMPT:
        print(
            f"[mcp_helper] Capping tool calls from {len(calls)} to {_MAX_CALLS_PER_ATTEMPT}",
            file=sys.stderr,
        )
        calls = calls[:_MAX_CALLS_PER_ATTEMPT]

    result = call_all_tools(
        project_root=project_root,
        tool_calls=calls,
        lean_path=lean_path,
        pool_size=pool_size,
        mcp_repo_path=mcp_repo_path,
        enabled_tools=enabled_tools,
    )

    sections: list[str] = []
    _ordered_keys = [
        ("file_contents", "MCP file-contents"),
        ("local_search", "MCP local-search"),
        ("unified_search", "MCP unified-search"),
    ]
    for key, heading in _ordered_keys:
        if key in result and result[key].strip():
            sections.extend([f"== {heading} ==", result[key].strip(), ""])

    # Collect all search results (including numbered duplicates)
    for key, value in sorted(result.items()):
        if key in {k for k, _ in _ordered_keys}:
            continue
        if value.strip():
            heading = key.replace("_", " ").replace("0", "").replace("1", "").replace("2", "").strip()
            sections.extend([f"== MCP {heading} ==", value.strip(), ""])

    return "\n".join(sections).strip()
