You are given one optimization exercise statement.
Rewrite it into a condition-complete, self-contained, textbook-style problem.

Input use rule:

- Primary source: problem_standardized_math. Preserve its task intent, core assumptions, and structure first.
- Secondary source: problem_with_context. Use it only to supplement missing dependency assumptions/formulas (including Reference/Double/Third/More reference lines) when clearly relevant.
- Before all other processing, ignore any hint/hints content entirely; hint text is disposable and must not be used in rewriting.
- If problem_standardized_math and problem_with_context differ, prefer problem_standardized_math unless context provides explicit supporting math needed for completeness.
- If problem_standardized_math lacks necessary mathematical support (assumptions/formulas/definitions), explicitly retrieve and integrate that support from problem_with_context.
- Keep strict dependency folding: third-hop -> second-hop -> first-hop -> original problem; if more-level dependencies exist, unfold/fold them layer-by-layer before final rewrite.

- Very important: Carefully check that every concept, symbol, function, and operator used in the problem is defined; if any definitions are missing, add precise definitions so the problem is fully self-contained and suitable for formalization.

Hard constraints:
- Do NOT solve the problem.
- Do NOT use, preserve, paraphrase, or output any hint/hints text; discard hints directly.
- Do NOT rewrite, split, reorder, or restate the original task objective in any form.
- The task objective must remain strictly identical to problem_standardized_math.
- Only identify and explicitly add implicit assumptions/conditions that are directly supported by input context.
- Add only information that is genuinely useful for mathematical completeness, dependency resolution, or precise definition; do not add irrelevant background, commentary, examples, or decorative exposition.
- Keep the original mathematical intent and task type.
- Do NOT add unnecessary stronger assumptions.
- Mandatory boundary-case safeguard: before treating the completed statement as acceptable, explicitly check edge conditions such as nonemptiness and zero-valued cases; if any such condition fails, provide a concrete counterexample and treat the item as `revise` with a clear reason in downstream review.
- Keep notation faithful and LaTeX-friendly.
- Use STANDARD LaTeX math notation only (no Unicode math symbols).
- For sets/spaces use \mathbf{R}, \mathbf{N}, \mathbf{Z}, \mathbf{Q}, \mathbf{C} when relevant.
- Use LaTeX operators: \le, \ge, \ne, \in, \subseteq, \to, \times, \cdot, \nabla.
- Keep all formulas compilable and avoid malformed TeX delimiters.
- Use explicit LaTeX commands (for example \alpha, \le, \times, \mathbf{R}) instead of Unicode math symbols.
- Keep math delimiters consistent: use \( ... \) / \[ ... \] correctly.
- Return JSON only.

Additional requirements (append-only):
- Respect dependency folding order: second-hop dependencies are merged into first-hop, then merged into the final problem statement.
- MUST fold dependencies in strict order before wording polish: third-hop -> second-hop -> first-hop -> original problem; if more-level dependencies exist, include them in layer order before final wording.
- MUST keep all mathematically necessary conditions introduced from third/second/first-hop substitutions in the final complete statement.
- Do not drop dependency assumptions/formulas that are necessary for task completeness.
- Preserve the exact mathematical intent from problem_standardized_math; only improve completeness/readability.
- Keep integrated dependency conditions explicit in mathematical form, not citation placeholders.
- Do not introduce new symbols unless directly implied by existing notation.
- Infer and explicitly state implicit conditions/definitions when they are supported by the input context.
- MUST identify implicit assumptions/conditions that are necessary for task validity and explicitly state them when supported by input context.
- MUST supplement missing definitions/conditions required to make the statement mathematically executable, but only when directly supported by input context.
- Do not over-expand: include only dependency-relevant, task-essential completions.
- Ensure the final statement is condition-complete and logically fluent in standard mathematical language.


Output schema:
{"problem_complete":"<condition-complete statement>"}
