"""Per-entry repair history tracker.

Tracks previous Lean code versions, errors, rejection reasons, and error
signatures for each exercise entry across compile-fix and semantic-fix loops.
Provides formatted history blocks for LLM prompts with token-budget-safe
summarisation of old attempts.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional


@dataclass
class HistoryEntry:
    """One recorded attempt for an exercise entry."""

    attempt: int
    loop: str  # "compile" or "semantic"
    pass_idx: int = 0  # semantic pass index (0 for compile loop)
    lean_code: str = ""
    errors: List[Dict[str, Any]] = field(default_factory=list)
    error_signature: str = ""
    rejection_reason: str = ""  # e.g. "empty_output", "contract_violation", "semantic_weakening"
    semantic_report_summary: str = ""  # condensed semantic report text


# Default: never drop the most recent N attempts
_DEFAULT_KEEP_RECENT = 5
# Rough char budget per summarised old attempt (controls prompt inflation)
_SUMMARY_CHAR_BUDGET = 400


class RepairHistory:
    """Per-entry history accumulator.

    Usage::

        history = RepairHistory(keep_recent=3, max_prompt_chars=12000)
        history.record(attempt=1, loop="compile", lean_code=code, errors=errs, ...)
        prompt_block = history.format_for_prompt()
    """

    def __init__(
        self,
        *,
        keep_recent: int = _DEFAULT_KEEP_RECENT,
        max_prompt_chars: int = 12_000,
    ) -> None:
        self.keep_recent = max(1, keep_recent)
        self.max_prompt_chars = max(2000, max_prompt_chars)
        self._entries: List[HistoryEntry] = []

    # ------------------------------------------------------------------
    # Recording
    # ------------------------------------------------------------------

    def record(
        self,
        *,
        attempt: int,
        loop: str,
        pass_idx: int = 0,
        lean_code: str = "",
        errors: Optional[List[Dict[str, Any]]] = None,
        error_signature: str = "",
        rejection_reason: str = "",
        semantic_report_summary: str = "",
    ) -> None:
        self._entries.append(
            HistoryEntry(
                attempt=attempt,
                loop=loop,
                pass_idx=pass_idx,
                lean_code=lean_code,
                errors=list(errors or []),
                error_signature=error_signature,
                rejection_reason=rejection_reason,
                semantic_report_summary=semantic_report_summary,
            )
        )

    @property
    def size(self) -> int:
        return len(self._entries)

    @property
    def entries(self) -> List[HistoryEntry]:
        return list(self._entries)

    # ------------------------------------------------------------------
    # Formatting
    # ------------------------------------------------------------------

    def format_for_prompt(self) -> str:
        """Return the history block ready for injection into a prompt.

        Only keeps the most recent N entries (controlled by keep_recent).
        Older entries are discarded entirely (not summarised).
        Includes a summary of failed patterns from all recorded history.
        """
        if not self._entries:
            return ""

        # Keep only the most recent N entries; discard older ones entirely
        recent_cutoff = max(0, len(self._entries) - self.keep_recent)
        recent = self._entries[recent_cutoff:]

        parts: List[str] = []

        # Anti-repeat instructions (always present when history exists)
        parts.append(
            "== IMPORTANT: Anti-repeat policy ==\n"
            "- Do NOT repeat previously failed fixes.\n"
            "- Do NOT reintroduce previously observed errors.\n"
            "- If a strategy failed before, switch to a fundamentally different strategy.\n"
            "- Review the history below and avoid every pattern that already failed.\n"
        )

        # Full recent entries (only)
        parts.append("== Recent history (last {} attempts) ==".format(len(recent)))
        for entry in recent:
            parts.append(self._format_entry_full(entry))
        parts.append("")

        # Failed patterns summary (derived from all historical attempts)
        failed_patterns = self._collect_failed_patterns()
        if failed_patterns:
            parts.append("== Previously failed fix patterns (do NOT repeat) ==")
            for pat in failed_patterns:
                parts.append(f"- {pat}")
            parts.append("")

        result = "\n".join(parts)
        return result

    def _summarise_entry(self, entry: HistoryEntry) -> str:
        parts = [f"  [attempt {entry.attempt}, {entry.loop}"]
        if entry.pass_idx:
            parts[0] += f" pass {entry.pass_idx}"
        parts[0] += "]"
        if entry.rejection_reason:
            parts.append(f"    Rejected: {entry.rejection_reason}")
        if entry.error_signature:
            parts.append(f"    Error sig: {entry.error_signature[:200]}")
        if entry.errors:
            first_msg = str(entry.errors[0].get("message", ""))[:150]
            parts.append(f"    First error: {first_msg}")
        if entry.semantic_report_summary:
            parts.append(f"    Semantic: {entry.semantic_report_summary[:150]}")
        text = "\n".join(parts)
        if len(text) > _SUMMARY_CHAR_BUDGET:
            text = text[:_SUMMARY_CHAR_BUDGET] + "…"
        return text

    def _format_entry_full(self, entry: HistoryEntry) -> str:
        parts = [f"  --- attempt {entry.attempt}, {entry.loop}"]
        if entry.pass_idx:
            parts[0] += f" pass {entry.pass_idx}"
        parts[0] += " ---"
        if entry.rejection_reason:
            parts.append(f"  Rejection reason: {entry.rejection_reason}")
        if entry.error_signature:
            parts.append(f"  Error signature: {entry.error_signature}")
        if entry.errors:
            parts.append("  Errors:")
            for err in entry.errors[:5]:
                loc = f"line {err.get('line', '?')}:{err.get('column', '?')}"
                parts.append(f"    {loc}: {err.get('message', '')}")
        if entry.semantic_report_summary:
            parts.append(f"  Semantic report: {entry.semantic_report_summary}")
        if entry.lean_code.strip():
            code = entry.lean_code.strip()
            # Limit code display in prompt to avoid bloat
            if len(code) > 2000:
                code = code[:2000] + "\n… (truncated)"
            parts.append(f"  Lean code:\n```lean\n{code}\n```")
        return "\n".join(parts)

    def _collect_failed_patterns(self) -> List[str]:
        """Collect human-readable descriptions of failed fix patterns."""
        patterns: List[str] = []
        seen_sigs: Dict[str, int] = {}
        for entry in self._entries:
            if entry.rejection_reason:
                desc = f"Attempt {entry.attempt}: {entry.rejection_reason}"
                if desc not in patterns:
                    patterns.append(desc)
            if entry.error_signature:
                seen_sigs[entry.error_signature] = seen_sigs.get(entry.error_signature, 0) + 1
        for sig, count in seen_sigs.items():
            if count >= 2:
                desc = f"Repeated error ({count}x): {sig[:200]}"
                if desc not in patterns:
                    patterns.append(desc)
        return patterns

    def _unique_signatures(self, entries: List[HistoryEntry]) -> List[str]:
        seen: List[str] = []
        for e in entries:
            if e.error_signature and e.error_signature not in seen:
                seen.append(e.error_signature[:100])
        return seen
