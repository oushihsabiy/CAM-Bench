"""Math comment rendering — convert TeX-like formulas to Lean-style syntax.

Uses an LLM-based converter when a client is provided, otherwise falls back to
deterministic rule-based substitutions from postprocess_lean.py.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Callable, Optional

from json2lean.block_parser import parse_blocks, extract_block_comment_text


def render_math_comments(
    text: str,
    *,
    get_client: Optional[Callable] = None,
    exercise_label: str = "",
) -> str:
    """Convert TeX math in block comments to Lean-style formatting.

    If *get_client* is provided, uses LLM for conversion with a deterministic
    prompt.  Otherwise, applies rule-based substitutions only.
    """
    blocks = parse_blocks(text)
    if not blocks:
        return text

    result = text
    for block in reversed(blocks):  # reverse to preserve offsets
        comment = result[block.comment_start:block.comment_end]
        if not _has_tex_math(comment):
            continue

        if get_client is not None:
            try:
                converted = _llm_convert_comment(
                    comment,
                    get_client=get_client,
                    exercise_label=exercise_label,
                )
                if converted and converted.strip():
                    result = result[:block.comment_start] + converted + result[block.comment_end:]
                    continue
            except Exception:
                pass  # fall through to rule-based

        converted = _rule_based_convert(comment)
        result = result[:block.comment_start] + converted + result[block.comment_end:]

    return result


def render_math_comments_file(
    filepath: str | Path,
    *,
    get_client: Optional[Callable] = None,
) -> bool:
    """Convert math comments in a Lean file in-place.  Returns True if changed."""
    path = Path(filepath)
    text = path.read_text(encoding="utf-8")
    result = render_math_comments(text, get_client=get_client)
    if result != text:
        path.write_text(result, encoding="utf-8")
        return True
    return False


# ---------------------------------------------------------------------------
# Detection
# ---------------------------------------------------------------------------

_TEX_INDICATORS = re.compile(
    r"\\(?:frac|sqrt|sum|prod|int|lim|inf|sup|mathbb|mathcal|mathbf|"
    r"forall|exists|in|notin|subset|subseteq|cup|cap|times|cdot|"
    r"leq|geq|neq|approx|equiv|rightarrow|Rightarrow|leftarrow|"
    r"alpha|beta|gamma|delta|epsilon|lambda|mu|sigma|theta|omega|"
    r"ell|nabla|partial|left|right|bigl|bigr|tfrac)\b"
    r"|(?:\$[^$]+\$)"
    r"|(?:\\\[)"
    r"|(?:\\\()"
)


def _has_tex_math(text: str) -> bool:
    return bool(_TEX_INDICATORS.search(text))


# ---------------------------------------------------------------------------
# Rule-based conversion
# ---------------------------------------------------------------------------

_RULE_MAP = [
    (r"\\mathbb\{R\}", "ℝ"),
    (r"\\mathbb\{N\}", "ℕ"),
    (r"\\mathbb\{Z\}", "ℤ"),
    (r"\\mathbb\{Q\}", "ℚ"),
    (r"\\mathbb\{C\}", "ℂ"),
    (r"\\forall", "∀"),
    (r"\\exists", "∃"),
    (r"\\in\b", "∈"),
    (r"\\notin", "∉"),
    (r"\\subset\b", "⊂"),
    (r"\\subseteq", "⊆"),
    (r"\\cup", "∪"),
    (r"\\cap", "∩"),
    (r"\\times", "×"),
    (r"\\cdot", "·"),
    (r"\\leq", "≤"),
    (r"\\geq", "≥"),
    (r"\\neq", "≠"),
    (r"\\approx", "≈"),
    (r"\\equiv", "≡"),
    (r"\\rightarrow", "→"),
    (r"\\Rightarrow", "⇒"),
    (r"\\leftarrow", "←"),
    (r"\\alpha", "α"),
    (r"\\beta", "β"),
    (r"\\gamma", "γ"),
    (r"\\delta", "δ"),
    (r"\\epsilon", "ε"),
    (r"\\lambda", "λ"),
    (r"\\mu", "μ"),
    (r"\\sigma", "σ"),
    (r"\\theta", "θ"),
    (r"\\omega", "ω"),
    (r"\\ell", "ℓ"),
    (r"\\nabla", "∇"),
    (r"\\partial", "∂"),
    (r"\\infty", "∞"),
    (r"\\ldots", "…"),
    (r"\\cdots", "⋯"),
    (r"\\pi", "π"),
    (r"\\sum", "∑"),
    (r"\\prod", "∏"),
    (r"\\int", "∫"),
    # Remove TeX delimiters
    (r"\\\[", ""),
    (r"\\\]", ""),
    (r"\\\(", ""),
    (r"\\\)", ""),
    (r"\\left\(", "("),
    (r"\\right\)", ")"),
    (r"\\left\[", "["),
    (r"\\right\]", "]"),
    (r"\\left\\{", "{"),
    (r"\\right\\}", "}"),
    (r"\\bigl\(", "("),
    (r"\\bigr\)", ")"),
    # Inline dollar signs
    (r"\$([^$]+)\$", r"\1"),
    # \frac{a}{b} → a / b
    (r"\\frac\{([^}]+)\}\{([^}]+)\}", r"(\1) / (\2)"),
    (r"\\tfrac\{([^}]+)\}\{([^}]+)\}", r"(\1) / (\2)"),
    # Subscript x_{i} → xᵢ (keep as-is for readability in comments)
    (r"_\{([^}]+)\}", r"_\1"),
    # Superscript ^{n} → ^n
    (r"\^\{([^}]+)\}", r"^\1"),
]


def _rule_based_convert(text: str) -> str:
    result = text
    for pattern, replacement in _RULE_MAP:
        result = re.sub(pattern, replacement, result)
    return result


# ---------------------------------------------------------------------------
# LLM-based conversion
# ---------------------------------------------------------------------------

_LLM_PROMPT = """\
Convert the TeX math formulas in this Lean block comment to Lean-style Unicode
syntax.  Rules:
- Replace TeX commands with Unicode equivalents (\\forall → ∀, \\mathbb{R} → ℝ, etc.)
- Replace \\frac{a}{b} with (a) / (b)
- Remove $ delimiters
- Keep the /- [BLOCK ...] header line EXACTLY as-is
- Keep the -/ closing EXACTLY as-is
- Do NOT add or remove any non-math text
- Output ONLY the converted comment, nothing else

[comment]
{comment}
"""


def _llm_convert_comment(
    comment: str,
    *,
    get_client: Callable,
    exercise_label: str = "",
) -> str:
    client = get_client()
    prompt = _LLM_PROMPT.format(comment=comment)
    result = client.chat(
        prompt=prompt,
        max_tokens=2048,
        call_type="math_comment_render",
        exercise_label=exercise_label,
    )
    # Validate: result must start with /- and end with -/
    result = result.strip()
    if result.startswith("```"):
        # Strip markdown fence
        lines = result.split("\n")
        lines = [l for l in lines if not l.strip().startswith("```")]
        result = "\n".join(lines).strip()
    if not result.startswith("/-") or not result.endswith("-/"):
        return ""
    return result
