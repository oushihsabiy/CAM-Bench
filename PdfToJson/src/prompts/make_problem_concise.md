
You are given one complete optimization problem statement.
Rewrite it to be concise and formalization-friendly while preserving meaning.

- Please rewrite the final problem as a self-contained, fluent, logically structured, concise,standard mathematical natural-language statement.


Rules:
- Very important: Remove any information that is not relevant to solving this problem, including but not limited to hints, remarks, background narrative, or repetitive phrases such as "you can"; ensure the final concise statement contains only material directly needed for the task.
- Also: Remove any equivalence phrasing (for example, "equivalently", "i.e.", "ie", ".i.e.", etc.) that asserts or repeats that two statements are equivalent; instead, provide explicit, unambiguous mathematical statements without shorthand equivalence language.
- Also: Preserve necessary definitions, concepts, assumptions, and any stated conclusions so that the final concise statement is a complete, self-consistent and concise problem suitable for formalization.
- Also remove : After a task directive such as "show that …" or "prove that …", if a trailing conclusion clause (e.g., "thus …", "therefore …", "hence …", "so …", "it follows that …") merely restates a consequence that is not part of the proof objective, remove that trailing clause. Keep it only if the conclusion itself is what the problem asks to prove.


Hard constraints:
- Do NOT solve the problem.
- Before all other work, ignore and discard any hint/hints content; it must not affect output.
- Do NOT rewrite, split, reorder, or restate the original task objective in any form.
- Keep the task objective strictly identical to problem_complete.
- Only keep wording cleanup and supported implicit-condition content; do not introduce new task structure.
- Keep all essential assumptions and constraints.
- Do NOT keep, paraphrase, or output hint/hints text.
- Mandatory boundary-case safeguard: before treating the concise statement as acceptable, explicitly check edge conditions such as nonemptiness and zero-valued cases; if an edge case fails, provide a concrete counterexample and treat the item as `revise` with a clear reason in downstream review.
- Remove narrative filler and keep formal mathematical phrasing.
- Try to remove redundant non-mathematical verbosity whenever possible.
- Use STANDARD LaTeX math notation only (no Unicode math symbols).
- Keep LaTeX commands explicit (for example \alpha, \mathbf{R}, \times, \le).
- Keep notation consistent and compilable; preserve mathematical correctness.
- Keep delimiters and escapes valid LaTeX (no malformed \(, \), \[, \]).
- Prefer explicit operators \le, \ge, \ne, \in, \subseteq, \to, \times, \cdot.
- Return JSON only.

Additional requirements (append-only):
- Keep semantic equivalence with problem_complete exactly.
- Do not compress away dependency assumptions/formulas required by the exercise.
- Do not remove any condition/formula introduced by validated third-hop -> second-hop -> first-hop dependency folding, or by validated more-level dependency unfolding.
- Do not delete or weaken any implicitly-completed definitions/conditions added in the complete stage.
- Keep TeX output standard and parser-stable.

-  Please rewrite the final problem as a self-contained, fluent, logically structured, concise,standard mathematical natural-language statement.

 
Output schema:
{"problem_concise":"<concise statement>"}
