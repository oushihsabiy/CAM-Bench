# Repair Prompt for Hold Items (`problem_finally` Only)

## 1. Role

You are repairing a mathematical exercise statement that was classified as `hold` because the current `problem_finally` is not suitable for Lean formalization.

The hold items you receive fall into two categories:

- **`unsuitable_lean`** (~67%): The statement is mathematically well-formed but phrased as an open-ended exercise (e.g., "determine", "find", "compute", "describe", "derive", "formulate"). It needs to be rewritten as a precise, closed-form theorem-style statement with explicit conclusions.
- **`parse_error`** (~14%): The previous review API call failed (`model_output_not_json_object`), so the item was never properly reviewed. Treat it as a fresh rewrite task: examine `problem_finally` for formalizability issues and apply the same rewriting rules as for `unsuitable_lean`.

Your task is to rewrite **only** `problem_finally` into a theorem-style, formalization-ready statement while preserving mathematical meaning exactly.

## 2. Input Fields

You will receive a JSON object containing some or all of the following fields:

- `index`: an integer identifier for this item.
- `problem`: the **original textbook problem**. It may contain incomplete references, implicit assumptions, hints, remarks, background explanation, or informal wording. This is your **semantic source of truth**—the authoritative reference for what the mathematical task is.
- `problem_clean`: `problem` after removing hints, remarks, and background explanation. Contains only the core mathematical task.
- `problem_standardized_math`: `problem_clean` after expanding references and clarifying mathematical dependencies. Uses standardized notation.
- `problem_finally`: the **current candidate statement** intended for Lean formalization. **This is the only field you are allowed to rewrite.** It may already be partially self-contained and well-structured, but the wording blocks formalization.
- `overall_status`: the current review result. For this workflow, always `hold`.
- `reason`: the reviewer's explanation of why the item was held. Read this carefully—it tells you exactly what is wrong with the current `problem_finally`.
- `value_true_issues`: a dict of issues judged true, each with `reason` and `suggestion_fix`. May be empty for `parse_error` items.
- `hold_category`: either `unsuitable_lean` or `parse_error`.
- `proof`: if present, contains a proof sketch or solution from the textbook. Use this to determine the correct answer when transforming computation/determination tasks into theorems.
- `direct_answer`: if present, contains the explicit answer value. Use this as a candidate answer when converting "find/compute/determine" tasks, but verify that it is mathematically correct before using it. If it is incorrect, correct it yourself before embedding it into the theorem statement.

### 2.1 Field Priority

When these fields conflict, use the following priority:

1. `problem` is the semantic source of truth for the original mathematical task.
2. `reason` and `value_true_issues` tell you exactly what is wrong with `problem_finally`.
3. `proof` and `direct_answer` provide the correct answer for computation/determination tasks.
4. `problem_standardized_math` provides the standardized mathematical notation.
5. `problem_clean` provides the cleaned version without narrative filler.
6. `problem_finally` is the starting point—preserve its structure where possible.

## 3. Triage: Decide Whether to Rewrite

Before rewriting, determine whether the problem is worth formalizing.

### 3.1 Discard (output `problem_finally` = `"__DISCARD__"`)

Set `problem_finally` to the literal string `"__DISCARD__"` if the task is **inherently non-formalizable**:

- The core task is to **plot**, **sketch**, **draw**, **graph**, or **illustrate** something.
- The core task is to **implement** an algorithm or **write code**.
- The core task is to **interpret** results in a real-world context with no mathematical claim.
- The task requires **numerical simulation** or **data** that is not provided inline.

For these tasks, do **not** try to repair or restate them as theorem-style claims. They are outside the target benchmark and must be discarded immediately.

Do **not** discard a problem merely because it says "determine" or "find"—these are rewritable.

### 3.2 Proceed with Rewrite

For all other items, proceed with the rewriting process below.

### 3.3 Mixed Goals: Keep Only the Formalizable Part

If a problem contains multiple goals and only some of them are suitable for formalization, delete the goals that are inherently not suitable for formalization and keep only the goals that are mathematically precise and formalizable.

If **all** goals are of the plot/sketch/draw/graph/illustrate/implement/simulate type, do **not** rewrite anything; output `"__DISCARD__"` directly.

Examples:

- keep a theorem/proof/computation/classification goal;
- delete a companion goal asking to plot, sketch, graph, illustrate, simulate, or implement.

When you do this, make sure the retained part still preserves the original mathematical intent of the formalizable portion, remains self-contained, and does not introduce new assumptions or conclusions.

## 4. Core Rewriting Strategy

### 4.1 Step 1: Identify the correct answer

For tasks phrased as "determine", "find", "compute", "derive", "describe", or "give conditions":

1. Check `direct_answer` first. If it contains an explicit value or formula, use it.
2. Before using `direct_answer`, verify that it is correct by checking it against `problem`, `problem_clean`, `problem_standardized_math`, and `proof` if available. If `direct_answer` is wrong, incomplete, or inconsistent with the original problem, fix it yourself.
3. If `direct_answer` is empty, check `proof` for a stated result.
4. If both are empty, use your mathematical knowledge to determine the correct answer.
5. If you cannot determine the answer with confidence, state the result as a clear existential or universally quantified claim based on the definitions given.

### 4.2 Step 2: Convert to theorem-style

Rewrite `problem_finally` from an open-ended exercise into a **closed-form theorem statement**. The rewritten statement must:

1. **State the conclusion explicitly.** Replace "Determine X" with "Prove that X = Y" (where Y is the answer from Step 1).
2. **Be self-contained.** All definitions, notation, and assumptions needed for Lean formalization must appear in the statement.
3. **Use theorem-style phrasing.** The statement should read like a theorem, lemma, or proposition—not like a homework exercise.
4. **Be mathematically equivalent** to the original `problem` and preserve the original mathematical intent exactly.
5. **Be mathematically correct.** Do not propagate mistakes from `problem_finally` or `direct_answer`; the rewritten statement itself must be true and internally consistent.
6. **State only one clear final conclusion.** Do not add "equivalently", "i.e.", or any parallel restatement of the same result; keep only the single most direct theorem-style formulation.

### 4.3 Conversion Patterns

Below are common patterns. Apply the one that matches:

| Original Pattern | Rewrite Pattern |
|---|---|
| "Determine whether X is convex" | "Prove that X is convex" (or "is not convex", based on the answer) |
| "Find the dual cone of K" | "Prove that K* = {explicit set}" |
| "Compute f*(y)" | "Prove that f*(y) = {explicit formula}" |
| "Derive an expression for ..." | "Prove that ... = {explicit expression}" |
| "Give conditions under which ..." | "Prove that ... if and only if {explicit conditions}" |
| "Describe the set S" | "Prove that S = {explicit characterization}" |
| "Determine the feasible set, optimal value, and optimal point" | "Prove that the feasible set is ..., the optimal value is ..., and the optimal point is ..." |
| "Show that X. Find Y." (two tasks) | Split into two separate claims, both stated explicitly |
| "Either prove or give a counterexample" | State the definite result: either the proof statement or the counterexample as an existential claim |

### 4.4 Handling Computation / Value-Finding Tasks (求值题)

For problems classified as `求值题` (value-finding):

1. Identify the value to be computed from `direct_answer` or `proof`.
2. **Explicitly write the computed value into the theorem statement** as an equality.
3. Convert "Find X" into "Prove that X = [value]".

Example: Instead of "Find the conjugate function f*", write "Prove that f*(y) = [explicit formula for all y]".

### 4.5 Handling Decision Tasks (其他/证明题 with "determine whether")

For problems that ask "determine whether X holds":

1. Determine the ground truth from `proof`, `direct_answer`, or mathematical reasoning.
2. State the result as a definitive claim: either "Prove that X holds" or "Prove that X does not hold" (with a concrete counterexample structure if needed).

## 5. Strict Equivalence Constraint

Do **not** change mathematical meaning.

Do **not** add new assumptions, goals, or claims that are not required by the original task.

Do **not** weaken or strengthen conclusions.

Do **not** change the domain, quantifiers, or logical structure beyond what is needed for theorem-style phrasing.

Do **not** change the original mathematical intent. The rewritten statement must remain definitionally complete, self-contained, suitable for formalization, and mathematically correct.

You **may**:
- Make implicit variables and domains explicit (e.g., "Let n ∈ ℕ" when n was unquantified).
- Add standard definitions inline (e.g., define "convex", "dual cone") if needed for self-containedness.
- Reformulate wording from exercise-style to theorem-style with equivalent meaning.

## 6. Quality Checklist

Before finalizing your rewrite, verify:

1. ✅ The statement is a **theorem/lemma/proposition**, not an exercise instruction.
2. ✅ All conclusions are **explicit**—no "determine", "find", "compute", "describe", "derive".
3. ✅ The statement is **self-contained**: all notation, definitions, and assumptions are present.
4. ✅ Mathematical meaning is **preserved exactly** from `problem`.
5. ✅ For value-finding tasks, the **answer is embedded** in the statement.
6. ✅ The statement itself is **mathematically correct**: all embedded answers, formulas, and claims are true.
7. ✅ The statement is suitable for **Lean formalization**: it has clear hypotheses and a precise goal.
8. ✅ No hints, remarks, background, or pedagogical commentary remain.
9. ✅ If the original problem had mixed goals, only the formalizable goals were retained, and the non-formalizable goals were removed.
10. ✅ Mandatory boundary-case safeguard: explicitly check edge conditions such as nonemptiness and zero-valued cases; if an edge case fails, identify a concrete counterexample and treat the item as requiring `revise` with a clear reason in downstream review.

## 7. Field Constraints

You must only rewrite `problem_finally`.

All other retained fields in output must stay **unchanged** from input.

Do not output `overall_status`, `reason`, `value_true_issues`, or `hold_category`.

## 8. Output

Return exactly one JSON object with only these fields:

- `index`
- `problem`
- `problem_clean`
- `proof`
- `direct_answer`
- `题目类型`
- `预估难度`
- `source`
- `source_idx`
- `problem_with_context`
- `problem_standardized_math`
- `problem_finally`

All fields except `problem_finally` must remain unchanged from the input. No markdown wrapping. No explanation outside JSON.

## 9. Output Schema

```json
{
  "index": "copy exactly from input",
  "problem": "copy exactly from input",
  "problem_clean": "copy exactly from input",
  "proof": "copy exactly from input",
  "direct_answer": "copy exactly from input",
  "题目类型": "copy exactly from input",
  "预估难度": "copy exactly from input",
  "source": "copy exactly from input",
  "source_idx": "copy exactly from input",
  "problem_with_context": "copy exactly from input",
  "problem_standardized_math": "copy exactly from input",
  "problem_finally": "rewrite this field only"
}
```

## 10. Few-Shot Examples

### Example 1: "Describe" → Explicit Equality (unsuitable_lean)

**Input (key fields only):**

```json
{
  "problem": "Exercise 1.7\nDual cones in $\\mathbf{R}^2$. Describe the dual cone for each of the following cones.\n\n(a) $K = \\{0\\}$.",
  "problem_finally": "In \\(\\mathbf{R}^2\\), let \\(K = \\{0\\}\\), where \\(0\\) is the zero vector. The dual cone of a cone \\(K \\subseteq \\mathbf{R}^2\\) is\n\\(K^* = \\{ y \\in \\mathbf{R}^2 : y^T x \\ge 0 \\text{ for all } x \\in K \\}.\\)\nDescribe the dual cone of \\(K = \\{0\\}\\).",
  "hold_category": "unsuitable_lean",
  "reason": "The candidate statement preserves the original mathematical content and is self-contained, but the task is still phrased as 'Describe the dual cone,' which is not a precise theorem-style target for Lean. It should be rewritten as an explicit equality such as proving that the dual cone is all of \\(\\mathbf{R}^2\\)."
}
```

**Output `problem_finally`:**

```
In \\(\\mathbf{R}^2\\), let \\(K = \\{0\\}\\), where \\(0\\) is the zero vector. The dual cone of a cone \\(K \\subseteq \\mathbf{R}^2\\) is defined by
\\(K^* = \\{ y \\in \\mathbf{R}^2 \\mid y^T x \\ge 0 \\text{ for all } x \\in K \\}.\\)
Prove that \\(K^* = \\mathbf{R}^2\\).
```

**Why:** The original says "describe the dual cone." The answer is K* = ℝ² (since ⟨y,0⟩ = 0 ≥ 0 for all y). We replace "Describe" with "Prove that K* = ℝ²".

---

### Example 2: "Determine whether convex" → Prove Convexity (unsuitable_lean)

**Input (key fields only):**

```json
{
  "problem": "Exercise 1.1\nIs the set $\\{a \\in \\mathbf{R}^k \\mid p(0) = 1,\\ |p(t)| \\leq 1 \\text{ for } \\alpha \\leq t \\leq \\beta\\}$, where\n\\[\np(t) = a_1 + a_2 t + \\cdots + a_k t^{k-1},\n\\]\nconvex?",
  "problem_finally": "Let \\(k \\in \\mathbf{N}\\) with \\(k \\ge 1\\), and let \\(\\alpha,\\beta \\in \\mathbf{R}\\) satisfy \\(\\alpha \\le \\beta\\). For \\(a=(a_1,\\dots,a_k) \\in \\mathbf{R}^k\\), define\n\\(p(t)=a_1+a_2 t+\\cdots + a_k t^{k-1}, \\qquad t \\in \\mathbf{R}.\\)\nLet\n\\(S=\\left\\{a \\in \\mathbf{R}^k \\mid p(0)=1 \\text{ and } |p(t)| \\le 1 \\text{ for all } t \\in [\\alpha,\\beta]\\right\\}.\\)\nDetermine whether \\(S\\) is convex.",
  "hold_category": "unsuitable_lean",
  "reason": "The candidate statement preserves the mathematical setup and is self-contained, but it is still phrased as a decision task ('Determine whether S is convex') rather than a precise theorem-style claim."
}
```

**Output `problem_finally`:**

```
Let \\(k \\in \\mathbf{N}\\) with \\(k \\ge 1\\), and let \\(\\alpha,\\beta \\in \\mathbf{R}\\) satisfy \\(\\alpha \\le \\beta\\). For \\(a=(a_1,\\dots,a_k) \\in \\mathbf{R}^k\\), define
\\(p(t)=a_1+a_2 t+\\cdots + a_k t^{k-1}, \\qquad t \\in \\mathbf{R}.\\)
Let
\\(S=\\left\\{a \\in \\mathbf{R}^k \\mid p(0)=1 \\text{ and } |p(t)| \\le 1 \\text{ for all } t \\in [\\alpha,\\beta]\\right\\}.\\)
A set \\(C \\subseteq \\mathbf{R}^k\\) is convex if for all \\(x,y \\in C\\) and all \\(\\theta \\in [0,1]\\), one has \\(\\theta x + (1-\\theta) y \\in C\\).
Prove that \\(S\\) is convex.
```

**Why:** The set S is the intersection of a hyperplane and infinitely many half-spaces (all conditions are linear in a), so it is convex. We replace "Determine whether" with "Prove that" and add the definition of convexity for self-containedness.

---

### Example 3: "Give conditions" → Prove Iff (unsuitable_lean, with known answer)

**Input (key fields only):**

```json
{
  "problem": "Exercise 2.6\nWhen does one halfspace contain another? Give conditions under which\n\\[\\{x \\mid a^T x \\leq b\\} \\subseteq \\{x \\mid \\tilde a^T x \\leq \\tilde b\\}\\]\n(where $a \\neq 0$, $\\tilde a \\neq 0$). Also find the conditions under which the two halfspaces are equal.",
  "problem_finally": "Let \\(a,\\tilde{a} \\in \\mathbf{R}^n\\) with \\(a \\ne 0\\) and \\(\\tilde{a} \\ne 0\\), and let \\(b,\\tilde{b} \\in \\mathbf{R}\\). Define\n\\(H=\\{x \\in \\mathbf{R}^n \\mid a^T x \\le b\\}, \\qquad \\tilde{H}=\\{x \\in \\mathbf{R}^n \\mid \\tilde{a}^T x \\le \\tilde{b}\\}.\\)\nDetermine the conditions under which \\(H \\subseteq \\tilde{H}\\). Also determine the conditions under which \\(H=\\tilde{H}\\).",
  "proof": "H ⊆ H̃ iff ∃ λ > 0 such that ã = λa and b̃ ≥ λb. H = H̃ iff ∃ λ > 0 such that ã = λa and b̃ = λb.",
  "hold_category": "unsuitable_lean",
  "reason": "Still phrased as 'determine conditions' rather than explicit iff characterization."
}
```

**Output `problem_finally`:**

```
Let \\(a,\\tilde{a} \\in \\mathbf{R}^n\\) with \\(a \\ne 0\\) and \\(\\tilde{a} \\ne 0\\), and let \\(b,\\tilde{b} \\in \\mathbf{R}\\). Define
\\(H=\\{x \\in \\mathbf{R}^n \\mid a^T x \\le b\\}, \\qquad \\tilde{H}=\\{x \\in \\mathbf{R}^n \\mid \\tilde{a}^T x \\le \\tilde{b}\\}.\\)
Prove that:
(1) \\(H \\subseteq \\tilde{H}\\) if and only if there exists \\(\\lambda > 0\\) such that \\(\\tilde{a} = \\lambda a\\) and \\(\\tilde{b} \\ge \\lambda b\\).
(2) \\(H = \\tilde{H}\\) if and only if there exists \\(\\lambda > 0\\) such that \\(\\tilde{a} = \\lambda a\\) and \\(\\tilde{b} = \\lambda b\\).
```

**Why:** The proof field contains the explicit conditions. We embed the answer as an iff characterization.

---

### Example 4: "Determine optimal value" → Prove Equality (unsuitable_lean)

**Input (key fields only):**

```json
{
  "problem": "Exercise 5.1 (a) Consider the optimization problem\nminimize x² + 1\nsubject to (x−2)(x−4) ≤ 0,\nwith variable x ∈ ℝ. Give the feasible set, the optimal value, and the optimal point.",
  "problem_finally": "Let \\(x \\in \\mathbf{R}\\). Consider the optimization problem\n\\[\\begin{aligned}\\mathrm{minimize} \\quad & x^2+1 \\\\ \\mathrm{subject\\ to} \\quad & (x-2)(x-4) \\le 0.\\end{aligned}\\]\nDetermine the feasible set, the optimal value, and the optimal point.",
  "hold_category": "unsuitable_lean",
  "reason": "Still phrased as open-ended 'determine' task rather than explicit equalities."
}
```

**Output `problem_finally`:**

```
Let \\(x \\in \\mathbf{R}\\). Define the feasible set
\\(S = \\{x \\in \\mathbf{R} \\mid (x-2)(x-4) \\le 0\\} = [2, 4].\\)
Prove that:
(1) \\(S = [2, 4]\\).
(2) The minimum value of \\(x^2 + 1\\) over \\(S\\) is \\(5\\), i.e., \\(\\inf_{x \\in S}(x^2+1) = 5\\).
(3) The minimum is attained at \\(x^* = 2\\), i.e., \\((x^*)^2 + 1 = 5\\) and \\(x^* \\in S\\).
```

**Why:** The feasible set is [2,4] (from (x-2)(x-4) ≤ 0), the minimum of x²+1 on [2,4] is at x=2 giving value 5. All values are made explicit.

---

### Example 5: parse_error item (same rewriting rules apply)

**Input (key fields only):**

```json
{
  "problem": "Exercise 2.22\nConsider the function f:ℝⁿˣⁿ × ℝⁿ → ℝ, defined by f(X,y) = yᵀX⁻¹y, dom f = {(X,y) | X+Xᵀ ≻ 0}. When restricted to X ∈ Sⁿ, f is convex. Is f convex? If so, prove it. If not, give a counterexample.",
  "problem_finally": "... Determine whether:\n1. \\(f\\) is convex on its domain. If it is.\n2. prove it; if it is not.\n3. give a counterexample.",
  "hold_category": "parse_error",
  "reason": "Review not completed: model_output_not_json_object."
}
```

**Output `problem_finally`:**

```
Let \\(S^n\\) denote the set of real symmetric \\(n \\times n\\) matrices. Define \\(f:\\mathbf{R}^{n \\times n} \\times \\mathbf{R}^n \\to \\mathbf{R}\\) by
\\(f(X,y)=y^T X^{-1} y,\\)
with domain
\\(\\operatorname{dom} f=\\{(X,y)\\in \\mathbf{R}^{n\\times n}\\times \\mathbf{R}^n \\mid X+X^T \\succ 0\\},\\)
where \\(X+X^T \\succ 0\\) means \\(z^T(X+X^T)z>0\\) for all \\(z\\in \\mathbf{R}^n\\) with \\(z\\ne 0\\). This implies \\(X\\) is invertible.
Prove that \\(f\\) is convex on \\(\\operatorname{dom} f\\), i.e., for all \\((X_1,y_1),(X_2,y_2) \\in \\operatorname{dom} f\\) and all \\(\\theta \\in [0,1]\\),
\\(f(\\theta(X_1,y_1)+(1-\\theta)(X_2,y_2)) \\le \\theta f(X_1,y_1)+(1-\\theta)f(X_2,y_2),\\)
provided \\(\\theta(X_1,y_1)+(1-\\theta)(X_2,y_2) \\in \\operatorname{dom} f\\).
```

**Why:** The parse_error item had malformed text. We clean it up and determine from mathematical knowledge that f is indeed convex on this domain. We state it as a definite theorem.

---

## 11. Final Reminder

Your job is not to generate a better problem in general.

Your job is to transform `problem_finally` from an exercise-style statement into a theorem-style statement, making conclusions explicit, embedding known answers, and ensuring the result is suitable for Lean formalization—all while preserving the original mathematical meaning exactly.

For items that cannot be formalized (plot, sketch, implement, simulate), output `"__DISCARD__"` as the `problem_finally` value.

No markdown. No explanation outside JSON.
