"""Post-process generated Lean files.

Current passes:
1) Normalize common TeX-like tokens inside Lean block comments.
2) Wrap overlong comment lines.
3) Normalize leading top-level section directives:
   deduplicate repeated `open` / `open scoped` / `variable`.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Callable, Protocol


_SECTION_RE = re.compile(r"^namespace\s+([A-Za-z0-9_']+)\s*$")
_END_RE = re.compile(r"^end\s+([A-Za-z0-9_']+)\s*$")
_COMMENT_WRAP_COL = 100


class _ChatClient(Protocol):
    def chat(
        self,
        *,
        prompt: str,
        max_tokens: int = 4096,
        call_type: str = "",
        exercise_label: str = "",
        json_mode: bool = False,
    ) -> str: ...


def _unicode_subscript(num: str) -> str:
    table = str.maketrans("0123456789+-=()n", "₀₁₂₃₄₅₆₇₈₉₊₋₌₍₎ₙ")
    return num.translate(table)


def _unicode_subscript_token(tok: str) -> str:
    table = str.maketrans(
        "0123456789+-=()nijkm",
        "₀₁₂₃₄₅₆₇₈₉₊₋₌₍₎ₙᵢⱼₖₘ",
    )
    return tok.translate(table)


def _find_block_comment_spans(text: str) -> list[tuple[int, int]]:
    """Return spans for Lean block comments, including nested comments.

    To avoid mutating Lean code literals, comment markers appearing inside
    double-quoted string literals are ignored.
    """
    spans: list[tuple[int, int]] = []
    depth = 0
    start = -1
    i = 0
    n = len(text)
    in_string = False

    while i + 1 < n:
        ch = text[i]
        if in_string:
            if ch == "\\":
                i += 2
                continue
            if ch == '"':
                in_string = False
                i += 1
                continue
            i += 1
            continue
        if ch == '"':
            in_string = True
            i += 1
            continue

        tok = text[i : i + 2]
        if tok == "/-":
            if depth == 0:
                start = i
            depth += 1
            i += 2
            continue
        if tok == "-/" and depth > 0:
            depth -= 1
            i += 2
            if depth == 0 and start >= 0:
                spans.append((start, i))
                start = -1
            continue
        i += 1

    return spans


def _normalize_comment_tex(comment: str) -> str:
    s = comment

    # Display/inline math delimiters
    s = s.replace(r"\[", "").replace(r"\]", "")
    s = s.replace(r"\(", "").replace(r"\)", "")
    s = s.replace("$$", "")

    # Basic symbol and set replacements
    basic_repls = [
        (r"\mathbf{R}", "ℝ"),
        (r"\mathbb{R}", "ℝ"),
        (r"\mathbb{N}", "ℕ"),
        (r"\mathbb{Z}", "ℤ"),
        (r"\mathbb{Q}", "ℚ"),
        (r"\mathbb{C}", "ℂ"),
        (r"\to", "→"),
        (r"\in", "∈"),
        (r"\subseteq", "⊆"),
        (r"\subset", "⊂"),
        (r"\forall", "∀"),
        (r"\exists", "∃"),
        (r"\mid", "|"),
        (r"\nabla", "∇"),
        (r"\partial", "∂"),
        (r"\cdot", "·"),
        (r"\times", "×"),
        (r"\ge", "≥"),
        (r"\le", "≤"),
        (r"\|", "‖"),
        (r"\alpha", "α"),
        (r"\beta", "β"),
        (r"\gamma", "γ"),
        (r"\delta", "δ"),
        (r"\epsilon", "ε"),
        (r"\theta", "θ"),
        (r"\lambda", "λ"),
        (r"\mu", "μ"),
        (r"\pi", "π"),
        (r"\rho", "ρ"),
        (r"\sigma", "σ"),
        (r"\tau", "τ"),
        (r"\phi", "φ"),
        (r"\omega", "ω"),
        (r"\left", ""),
        (r"\right", ""),
        (r"\bigl", ""),
        (r"\bigr", ""),
        (r"\Bigl", ""),
        (r"\Bigr", ""),
        (r"\qquad", ""),
        (r"\,", ""),
        (r"\;", ""),
        (r"\!", ""),
        (r"\{", "{"),
        (r"\}", "}"),
    ]
    for a, b in basic_repls:
        s = s.replace(a, b)

    # Fractions and powers
    s = re.sub(r"\\frac\s*\{([^{}]+)\}\s*\{([^{}]+)\}", r"(\1)/(\2)", s)
    s = s.replace(r"\infty", "∞")

    # Matrix environments: keep compact textual matrix brackets
    s = s.replace(r"\begin{bmatrix}", "[")
    s = s.replace(r"\end{bmatrix}", "]")
    s = s.replace(r"\begin{pmatrix}", "(")
    s = s.replace(r"\end{pmatrix}", ")")
    s = s.replace(r"\\", "; ")

    # Common index/mark patterns
    s = s.replace("x^*", "x*")
    s = s.replace("y^*", "y*")
    s = s.replace("r_0", "r₀")
    s = re.sub(r"x_(\d)", lambda m: "x" + _unicode_subscript(m.group(1)), s)
    s = re.sub(r"y_(\d)", lambda m: "y" + _unicode_subscript(m.group(1)), s)
    s = re.sub(r"\{x_k\}_\{k=0\}\^\{∞\}", "{x_k}_(k=0)^∞", s)
    s = s.replace(r"\{x_k\}_{k=0}^{\infty}", "{x_k}_(k=0)^∞")

    # Fallback: unwrap unknown TeX commands like \foo{...} -> ...
    s = re.sub(r"\\[A-Za-z]+\{([^{}]*)\}", r"\1", s)
    # For remaining bare TeX commands, drop backslash but keep token text.
    s = re.sub(r"\\([A-Za-z]+)", r"\1", s)

    # Final cleanup
    s = re.sub(r"\s+\n", "\n", s)
    s = re.sub(r"[ \t]{2,}", " ", s)
    s = re.sub(r"\n{3,}", "\n\n", s)
    return s


def _normalize_math_style(comment: str) -> str:
    """Lightweight style normalization for awkward ASCII math prose.

    This pass is intentionally conservative and only rewrites clear formatting
    artifacts without changing mathematical content.
    """
    s = comment
    repls = [
        ("R^(n x n)", "ℝ^{n×n}"),
        ("R^(n × n)", "ℝ^{n×n}"),
        ("R^n", "ℝ^n"),
        ("-> R", "→ ℝ"),
        ("->R", "→ ℝ"),
        ("Q^(-1)", "Q^{-1}"),
        ("x^star", "x*"),
        ("lambda_1", "λ_1"),
        ("lambda_n", "λ_n"),
        ("grad f_k", "∇f_k"),
        (" in N", " ∈ ℕ"),
        (" in R", " ∈ ℝ"),
        (" in ℝ", " ∈ ℝ"),
        (" in ℕ", " ∈ ℕ"),
        (" x ", " x "),
        ("||", "‖"),
        ("iteration，", "iteration,"),
        ("transpose", "ᵀ"),
        ("varphi", "φ"),
        ("∈fty", "∞"),
        (" ne ", " ≠ "),
    ]
    for a, b in repls:
        s = s.replace(a, b)

    # Common set-style fragments
    s = s.replace("k in N", "k ∈ ℕ")
    s = s.replace("n in N", "n ∈ ℕ")
    s = s.replace("x in ℝ^n", "x ∈ ℝ^n")
    s = s.replace("x in R^n", "x ∈ ℝ^n")
    s = s.replace("for x in ℝ^n", "for x ∈ ℝ^n")
    s = s.replace("for x in R^n", "for x ∈ ℝ^n")
    s = re.sub(r"([a-zA-Z])\s*∈\s*N\b", r"\1 ∈ ℕ", s)
    s = s.replace("ℝ^{n x n}", "ℝ^{n×n}")
    s = s.replace("ℝ^{n x  n}", "ℝ^{n×n}")
    s = s.replace("ℝ^{n× n}", "ℝ^{n×n}")
    s = s.replace("tilde f", "f̃")
    s = s.replace("tilde B", "B̃")
    s = s.replace("tilde p", "p̃")
    s = s.replace("tilde s", "s̃")
    s = s.replace("tilde y", "ỹ")
    s = s.replace("∇tilde f", "∇f̃")
    s = s.replace("S transpose", "Sᵀ")
    s = s.replace("be ∈", "be in")

    # Normalize spacing around multiplication sign in dimensions.
    s = s.replace("ℝ^{n × n}", "ℝ^{n×n}")

    # Gradient word -> symbol
    s = re.sub(r"\bgradient\s+([A-Za-z][A-Za-z0-9_]*\s*\([^)]*\))", r"∇\1", s)
    s = re.sub(r"\bgradient\s+([A-Za-z][A-Za-z0-9_]*)", r"∇\1", s)
    s = s.replace("\\ne", "≠")
    # Greek-letter slash artifacts like \alpha or \α.
    s = s.replace("\\alpha", "α").replace("\\beta", "β").replace("\\gamma", "γ")
    s = s.replace("\\delta", "δ").replace("\\theta", "θ").replace("\\lambda", "λ")
    s = s.replace("\\kappa", "κ").replace("\\phi", "φ").replace("\\varphi", "φ")
    s = s.replace("\\α", "α").replace("\\β", "β").replace("\\γ", "γ")
    s = s.replace("\\δ", "δ").replace("\\θ", "θ").replace("\\λ", "λ")
    s = s.replace("\\κ", "κ").replace("\\φ", "φ")
    # Star/escape artifacts from TeX, e.g. x^\*, x^*
    s = s.replace("^\\*", "*")
    s = re.sub(r"([A-Za-z])\^\*", r"\1*", s)
    # Norm delimiter artifacts from TeX lVert/rVert.
    s = s.replace("\\lVert", "‖").replace("\\rVert", "‖")
    s = s.replace("lVert", "‖").replace("rVert", "‖")
    # Transpose artifacts from TeX like ^{\\mathsf T}, ^{mathsf T}, etc.
    s = s.replace("^{\\mathsf T}", "ᵀ")
    s = s.replace("^{mathsf T}", "ᵀ")
    s = s.replace("^\\mathsf T", "ᵀ")
    s = s.replace("^mathsf T", "ᵀ")
    s = s.replace("{mathsf T}", "ᵀ")
    s = s.replace("\\mathsf{T}", "ᵀ")
    s = s.replace("^T", "ᵀ")
    # TeX spacing commands only (avoid removing words like "quadratic").
    s = re.sub(r"\\quad\b", "", s)
    s = re.sub(r"\\qquad\b", "", s)

    # Force common greek-letter words into mathematical symbols.
    greek_map = {
        "alpha": "α",
        "beta": "β",
        "gamma": "γ",
        "delta": "δ",
        "epsilon": "ε",
        "theta": "θ",
        "lambda": "λ",
        "mu": "μ",
        "pi": "π",
        "rho": "ρ",
        "sigma": "σ",
        "tau": "τ",
        "phi": "φ",
        "omega": "ω",
        "kappa": "κ",
    }
    for name, sym in greek_map.items():
        s = re.sub(rf"\b{name}\b", sym, s, flags=re.IGNORECASE)

    # Subscript normalization:
    # 1) keep compound indices in brace form, e.g. x_k+1 -> x_{k+1}
    s = re.sub(r"\b([A-Za-z])_([A-Za-z0-9]+(?:[+\-][A-Za-z0-9]+)+)\b", r"\1_{\2}", s)
    # 2) convert simple single-token indices to unicode subscripts, e.g. x_k -> xₖ, B_0 -> B₀
    s = re.sub(
        r"\b([A-Za-z])_([0-9]+|[nijkm])\b",
        lambda m: m.group(1) + _unicode_subscript_token(m.group(2)),
        s,
    )

    # Recover common broken piecewise artifacts produced by malformed TeX dumps.
    if "cases" in s:
        s = s.replace("≤ft", "")
        s = s.replace("dfrac", "")
        s = s.replace("frac", "")
        s = s.replace("{x_{k-1}}{k}", "x_{k-1}/k")
        s = s.replace("1{4}", "1/4")
        s = s.replace("fracx_{k-1}/k", "x_{k-1}/k")
        s = re.sub(r"\(1/4\)\^\{2\^k,\s*if k is even;?", "(1/4)^{2^k}, if k is even;", s)

    return s


def _wrap_line(line: str, width: int) -> list[str]:
    if len(line) <= width:
        return [line]
    words = line.split()
    if not words:
        return [line]
    out: list[str] = []
    cur = words[0]
    for w in words[1:]:
        if len(cur) + 1 + len(w) <= width:
            cur += " " + w
        else:
            out.append(cur)
            cur = w
    out.append(cur)
    return out


def _wrap_comment_lines(comment: str) -> str:
    lines = comment.splitlines()
    out: list[str] = []
    for line in lines:
        stripped = line.strip()
        if stripped in {"/-", "-/"} or not stripped:
            out.append(line)
            continue
        wrapped = _wrap_line(stripped, _COMMENT_WRAP_COL)
        out.extend(wrapped)
    return "\n".join(out)


def _extract_comment_body(comment: str) -> str:
    s = comment.strip()
    if s.startswith("/-"):
        s = s[2:]
    if s.endswith("-/"):
        s = s[:-2]
    return s.strip()


def _compose_comment_block(body: str) -> str:
    return "/-\n" + body.strip() + "\n-/"


def _needs_llm_cleanup(comment: str) -> bool:
    # Gate LLM usage to comments that still look TeX-heavy.
    return bool(
        "\\" in comment
        or re.search(r"\$|\\begin\{|\\end\{|\\frac|\\mathbf|\\mathbb|\\nabla|\\to|\\subset", comment)
    )


def _safe_llm_rewrite_comment(comment: str, client: _ChatClient, label: str) -> str:
    original_body = _extract_comment_body(comment)
    prompt = (
        "Rewrite the following Lean block comment into standardized mathematical writing.\n"
        "Hard constraints:\n"
        "1) Preserve mathematical meaning EXACTLY.\n"
        "2) Do NOT add, remove, weaken, or strengthen any assumption, quantifier, condition, or conclusion.\n"
        "3) Keep all symbols/variables (names and roles) consistent with the original text.\n"
        "4) Remove raw TeX commands/syntax and output rendered mathematical notation only.\n"
        "5) Do NOT output Lean code, proof text, code fences, or comment delimiters.\n"
        "6) Do NOT paraphrase logical content; only normalize mathematical notation and typography.\n"
        "Mandatory normalization:\n"
        "7) Use Unicode arrows/relations only: '→', '≤', '≥' (never '->', '<=', '>=').\n"
        "8) Use '∈' for membership and standard sets/spaces like 'ℝ', 'ℕ'.\n"
        "9) Prefer 'ℝ²' for fixed small dimensions, and 'ℝ^{n×n}' for matrix spaces.\n"
        "10) Normalize transpose notation to 'ᵀ' (not '^T', 'mathsf T', or 'transpose').\n"
        "11) Normalize gradient notation to '∇f(...)' (not word forms like 'gradient f').\n"
        "12) Normalize decorated symbols: prefer 'f̃', 'B̃', 'p̃', 's̃', 'ỹ' when they denote tilded variables.\n"
        "13) Normalize Greek variable words to symbols where appropriate (e.g., alpha→α, beta→β, lambda→λ).\n"
        "14) Normalize index notation consistently (e.g., 'x_{k+1}', 'z_0', or Unicode subscripts such as 'xₖ' when clear).\n"
        "15) Normalize operator spacing (e.g., 'r > 0', 'f(x) ≥ f(x*)', '‖x - x*‖ < r').\n"
        "16) Remove malformed artifacts such as '≤ft', 'dfrac', 'cases' literals, '∈fty', 'ldots', broken braces, and mixed punctuation.\n"
        "17) For piecewise definitions, output a clean piecewise form with all branches and conditions preserved.\n"
        "18) Example style: '(xₖ)_{k=0}^{∞} ⊂ ℝ²', 'xₖ = (1 + 1/2^k)(cos k, sin k)', 'f(x) = ‖x‖²',\n"
        "    'e₁ = (1, 0)ᵀ', '∇²f(x*)', 'λ_max(∇²f(x*)) / λ_min(∇²f(x*)) ≥ κ'.\n"
        "19) Keep line breaks only where readability improves; avoid fragmentary wraps.\n"
        "20) Return ONLY the rewritten comment body text.\n\n"
        f"Comment body:\n{original_body}\n"
    )
    try:
        rewritten = client.chat(
            prompt=prompt,
            max_tokens=1024,
            call_type="postprocess_comment_rewrite",
            exercise_label=label,
        ).strip()
    except Exception:
        return comment

    if not rewritten:
        return comment

    # Safety checks: reject if key numeric literals disappear.
    nums = set(re.findall(r"\d+(?:\.\d+)?", original_body))
    for n in nums:
        if n not in rewritten:
            return comment

    # Keep key inequality/equality symbols if present.
    for sym in ("≤", "≥", "<", ">", "="):
        if sym in original_body and sym not in rewritten:
            return comment

    return _compose_comment_block(rewritten)


def _rewrite_block_comments(
    text: str,
    *,
    llm_rewrite_comments: bool = False,
    llm_rewrite_all_comments: bool = False,
    llm_comments_only: bool = False,
    get_client: Callable[[], _ChatClient] | None = None,
    label: str = "",
) -> str:
    spans = _find_block_comment_spans(text)
    if not spans:
        return text

    out_parts: list[str] = []
    cursor = 0
    total = len(spans)

    for idx, (start, end) in enumerate(spans, start=1):
        out_parts.append(text[cursor:start])
        raw_comment = text[start:end]
        c = raw_comment
        # Pre-clean TeX-like noise before LLM so the model sees cleaner math text.
        if not llm_comments_only:
            c = _normalize_comment_tex(c)
        c = _normalize_math_style(c)
        should_llm = llm_rewrite_comments and get_client is not None and (
            llm_rewrite_all_comments or _needs_llm_cleanup(raw_comment)
        )
        if should_llm:
            c = _safe_llm_rewrite_comment(c, get_client(), label=label)
        c = _normalize_math_style(c)
        c = _wrap_comment_lines(c)
        out_parts.append(c)
        cursor = end

        if llm_rewrite_comments:
            # Progress signal for long-running files; keeps output responsive.
            print(
                f"[postprocess][comments] {label}: {idx}/{total}",
            )

    out_parts.append(text[cursor:])
    return "".join(out_parts)


def _hoist_directives_in_section(section_lines: list[str]) -> list[str]:
    i = 0
    n = len(section_lines)
    while i < n and not section_lines[i].strip():
        i += 1

    j = i
    while j < n:
        line = section_lines[j]
        stripped = line.strip()
        if stripped != line:
            break
        if stripped.startswith("open ") or stripped.startswith("variable "):
            j += 1
            continue
        break

    if j <= i:
        return section_lines

    head = section_lines[:i]
    directive_block = section_lines[i:j]
    tail = section_lines[j:]

    deduped_directives: list[str] = []
    seen: set[str] = set()
    for line in directive_block:
        if line in seen:
            continue
        seen.add(line)
        deduped_directives.append(line)

    return head + deduped_directives + tail


def _rewrite_section_opens(text: str) -> str:
    lines = text.splitlines()
    stack: list[tuple[str, int]] = []
    pairs: list[tuple[int, int, str]] = []

    for i, raw in enumerate(lines):
        line = raw.strip()
        ms = _SECTION_RE.match(line)
        if ms:
            stack.append((ms.group(1), i))
            continue
        me = _END_RE.match(line)
        if me:
            name = me.group(1)
            for j in range(len(stack) - 1, -1, -1):
                if stack[j][0] == name:
                    _, start = stack.pop(j)
                    pairs.append((start, i, name))
                    break

    for start, end, _name in sorted(pairs, key=lambda x: x[0], reverse=True):
        body = lines[start + 1 : end]
        body_new = _hoist_directives_in_section(body)
        lines[start + 1 : end] = body_new

    return "\n".join(lines) + ("\n" if text.endswith("\n") else "")


def postprocess_lean_text(
    text: str,
    *,
    llm_rewrite_comments: bool = False,
    llm_rewrite_all_comments: bool = False,
    llm_comments_only: bool = False,
    get_client: Callable[[], _ChatClient] | None = None,
    label: str = "",
) -> str:
    out = _rewrite_block_comments(
        text,
        llm_rewrite_comments=llm_rewrite_comments,
        llm_rewrite_all_comments=llm_rewrite_all_comments,
        llm_comments_only=llm_comments_only,
        get_client=get_client,
        label=label,
    )
    out = _rewrite_section_opens(out)
    return out


def postprocess_lean_file(
    path: Path,
    *,
    llm_rewrite_comments: bool = False,
    llm_rewrite_all_comments: bool = False,
    llm_comments_only: bool = False,
    get_client: Callable[[], _ChatClient] | None = None,
) -> bool:
    old = path.read_text(encoding="utf-8")
    new = postprocess_lean_text(
        old,
        llm_rewrite_comments=llm_rewrite_comments,
        llm_rewrite_all_comments=llm_rewrite_all_comments,
        llm_comments_only=llm_comments_only,
        get_client=get_client,
        label=path.name,
    )
    if new != old:
        path.write_text(new, encoding="utf-8")
        return True
    return False
