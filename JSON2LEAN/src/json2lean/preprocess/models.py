"""Data models for the preprocessing pipeline."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List


@dataclass
class StageResult:
    """Output of a single extraction stage."""
    items: List[Dict[str, str]] = field(default_factory=list)
    masked_text: str = ""


@dataclass
class Placeholder:
    """A placeholder that replaced a special block in the problem text."""
    token: str            # e.g., "OPT_PROBLEM_1", "ALGORITHM_1"
    kind: str             # "optimization_problem" or "algorithm"
    original_text: str    # the original text that was masked
    assigned_name: str    # concise mathematical name assigned to the block
    source_position: int  # character offset in original text


@dataclass
class MaskingResult:
    """Output of the pre-masking stage."""
    masked_text: str
    placeholders: List[Placeholder] = field(default_factory=list)


@dataclass
class FlatRecord:
    """A single record in the flat output format."""
    index: int
    source: str
    source_idx: str
    kind: str             # "thm", "defn", "opt_prob", "algo", "hints"
    content: str
    term: str = ""

    def to_dict(self) -> Dict[str, Any]:
        d: Dict[str, Any] = {
            "index": self.index,
            "source": self.source,
            "source_idx": self.source_idx,
            "kind": self.kind,
            "content": self.content,
        }
        if self.term:
            d["term"] = self.term
        return d
