You are given a math exercise problem text. Your task is to identify **optimization-domain technical terms** (proper nouns / named concepts) that appear in the text, and provide a precise mathematical definition for each.

## What counts as a technical term

A technical term is a **named, reusable concept** from optimization, convex analysis, or numerical methods whose meaning is independent of the specific exercise. Examples:

- "strongly convex", "Lipschitz continuous gradient", "self-concordant"
- "quasiconvex", "log-concave", "positive semidefinite"
- "descent direction", "Armijo condition", "Wolfe conditions"
- "KKT conditions", "dual feasible", "central path"
- "infimal convolution", "convex conjugate", "effective domain"
- "ill-conditioned", "doubly stochastic", "permutation matrix"

## What does NOT count

- **Generic nouns**: "domain", "function", "set", "map", "variable", "constraint", "norm", "matrix", "vector". These are everyday mathematical vocabulary, not named concepts.
- **Problem-local object names**: "g", "dom g", "f_1 ◇ ··· ◇ f_m" — these are specific objects defined for this exercise, not reusable terms.
- **Variable / symbol declarations**: "Let f : R^n → R", "x ∈ R^n".
- **Individual function setups**: "Define φ(α) = f(x + αp)".
- **Whole optimization problems or algorithms** — those are handled by a separate stage.
- **Assumptions, goals, or hints**.

- **Generic problem category names**: "convex optimization problem",
  "linear program", "optimization problem", "minimization problem",
  "primal problem", "dual problem". These name a class of problems,
  not a reusable mathematical property or condition. Optimization
  problem instances are handled by a separate extraction stage.
- **Ignore these specifically (do not extract)**:
  - "convex set" / "凸集"
  - "positive definite matrix", "positive semidefinite matrix" / "正定矩阵", "半正定矩阵"
  - "hyperplane", "boundary", "disjoint" and close variants (e.g. "hyperplanes", "separating hyperplane", "supporting hyperplane", "boundaries", "boundary point", "pairwise disjoint", "mutually disjoint", "disjointness", "non-overlapping") / "超平面", "边界", "不相交"

**Key test**: if the term only makes sense when you know which specific object from this exercise it refers to, it is NOT a technical term. A technical term must be meaningful on its own (e.g., "convex function" is meaningful without knowing which f).

## Two-pass extraction procedure

### Pass 1 — Terms with in-text definitions
Scan the text for technical terms that the text **explicitly defines or characterizes** with a reusable mathematical condition. For each such term, use the definition from the text (rewritten into a precise formal condition if needed).

### Pass 2 — Terms without in-text definitions
Scan the text again for technical terms that are **used but not defined** in the text. For each such term, supply a standard textbook-level definition from optimization / convex analysis.

## Output rules

1. Every `term` must be a recognized optimization-domain named concept (not a generic noun).
2. Every `definition` must be a precise, Lean-translatable mathematical statement (1–2 sentences max).
3. Use LaTeX-compatible math notation. Escape backslashes for JSON (e.g., `\\in`, `\\le`, `\\mathbf{R}`).
4. Do NOT mask or modify the source text.
5. Do not solve the problem or add proofs.
6. If no technical terms are found, return an empty `items` list.
7. Mark each item with `"source": "in_text"` if the definition came from the exercise text, or `"source": "standard"` if you supplied a standard definition.

## Output format

Output exactly one JSON object, nothing else:

```json
{
  "items": [
    {"term": "strongly convex", "definition": "A function f : \\mathbf{R}^n \\to \\mathbf{R} is strongly convex with parameter m > 0 if for all x, y and all \\lambda \\in [0,1], f(\\lambda x + (1-\\lambda)y) \\le \\lambda f(x) + (1-\\lambda) f(y) - \\frac{m}{2} \\lambda(1-\\lambda) \\|x - y\\|^2.", "source": "in_text"},
    {"term": "Armijo condition", "definition": "A step length \\alpha > 0 satisfies the Armijo condition with parameter c \\in (0,1) if f(x + \\alpha p) \\le f(x) + c \\alpha \\nabla f(x)^T p.", "source": "standard"}
  ]
}
```

If no technical terms are found, return:
```json
{
  "items": []
}
```

Do not output explanation, markdown fences, or any text outside the JSON object.

Now extract optimization-domain technical terms from the following text:
