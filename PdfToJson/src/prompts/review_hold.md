# Review Prompt for Hold-Repaired Items

## 1. Role

You are reviewing a **hold-repaired** mathematical exercise for Lean formalization readiness.

The item you are reviewing was originally classified as `hold` because its `problem_finally` was phrased as an open-ended exercise (e.g., "determine", "find", "compute", "describe") or because a prior review API call failed (`parse_error`). A repair stage has since **deliberately rewritten** `problem_finally` to convert the exercise-style wording into a **theorem-style** statement with explicit conclusions.

Your task is to judge whether the repaired `problem_finally` is now:

- **`accept`**: faithful to the original mathematical intent, self-contained, definitions included, mathematically correct, and suitable for Lean formalization.
- **`revise`**: the repaired statement has specific fixable issues (e.g., missing assumption, incorrect embedded answer, missing definition) that block acceptance.
- **`hold`**: the repaired statement is mathematically incorrect, not reliably verifiable, or has unfixable structural problems (e.g., unresolved external dependencies, fundamentally not formalizable, or `__DISCARD__`).

## 2. Background: What Repair Did

Understanding the repair process is critical to calibrating your review. The repair stage performed one or more of the following transformations:

1. **Exercise → Theorem conversion**: "Determine X" → "Prove that X = Y"; "Find conditions" → "Prove that ... iff ..."; "Describe the set S" → "Prove that S = {explicit set}". This is the primary and most common transformation.
2. **Answer embedding**: For value-finding or condition-finding tasks, the repair stage identified the correct answer (from `direct_answer`, `proof`, or mathematical reasoning) and embedded it explicitly as a theorem conclusion.
3. **Non-formalizable goal removal**: If the original problem had mixed goals (e.g., "Show X is convex. Plot the boundary."), the repair stage removed the non-formalizable goal (plot) and kept only the formalizable goal (convexity proof).
4. **Discarding**: Items that are inherently non-formalizable (pure plot/sketch/implement tasks) were set to `"__DISCARD__"`.
5. **Definition inlining**: Standard mathematical definitions (convexity, dual cone, conjugate function, etc.) were added inline to ensure self-containedness.
**These transformations are expected and authorized.** Do not flag them as `task_drift` when they preserve mathematical meaning.

## 3. Input Fields

You will receive:

- `source_idx`: the exercise identifier.
- `source`: the source book or bibliographic reference.
- `problem`: the **original textbook problem**. This is your semantic source of truth. It may contain hints, remarks, background explanation, or informal wording.
- `problem_clean`: `problem` after removing hints, remarks, and background explanation.
- `problem_standardized_math`: `problem_clean` after expanding references and standardizing notation.
- `problem_finally`: the **repaired candidate statement** for Lean formalization. This is the object under review.
- `proof` (if present): the textbook proof or solution sketch.
- `direct_answer` (if present): the explicit answer value.

## 4. Core Objective

Compare `problem_finally` against `problem`, with awareness that authorized theorem-style reformulation has occurred.

Your review must answer five questions:

1. Does `problem_finally` preserve the **mathematical intent** of the original problem?
2. Is the embedded answer or conclusion **mathematically correct**?
3. Does `problem_finally` preserve all **necessary assumptions**?
4. Is `problem_finally` **self-contained** (all definitions, notation, and assumptions present)?
5. Is the resulting task **suitable for Lean formalization** (precise theorem-style, no open-ended verbs)?

Mathematical correctness is a **hard requirement**. If the repaired statement is false, or if its truth cannot be verified with sufficient confidence, it must not be accepted.

## 5. Issue Types

Use exactly these four issue types:

### 5.1 `missing_assumption`

A necessary assumption from `problem` is absent in `problem_finally`.

Examples: missing nonzero, nonnegative, positive-definite, domain, index range, continuity, differentiability, invertibility conditions.

**Do not flag** presentation-only refinements (e.g., making `n` explicit, making index families nonempty) unless they create a real mathematical gap.

### 5.2 `task_drift`

The mathematical task in `problem_finally` is **not mathematically equivalent** to the task in `problem`.

#### 5.2.1 What IS task drift (flag it)

- The embedded answer is **wrong**: e.g., the repair claims `K* = ℝ²` but the correct answer is `K* = ℝ²₊`.
- A conclusion was **incorrectly strengthened**: e.g., the original asks "is f convex?" and the answer is no, but the repair says "Prove that f is convex."
- A conclusion was **incorrectly weakened**: e.g., the original asks to prove an iff, but the repair only states one direction.
- A quantifier changed in a way that **alters mathematical meaning**: e.g., ∃ replaced with ∀.
- The conclusion **does not follow from the original task**: e.g., the original asks "describe the dual cone" and the repair proves something about a tangent cone instead.
- Assumptions were **added** that are not in the original problem and change the claim.
- A formalizable sub-goal was **dropped** without justification.
- The repaired statement adds an extra mathematical claim or theorem target that is not required by the original task.

#### 5.2.2 What is NOT task drift (do not flag)

The following are **authorized transformations** from the repair stage. Do not flag them as `task_drift`:

- "Determine whether X" → "Prove that X" (or "Prove that not X"), provided the stated result is correct.
- "Find X" → "Prove that X = [value]", provided the value is correct.
- "Describe/Compute/Derive X" → "Prove that X = [explicit expression]", provided the expression is correct.
- "Give conditions for X" → "Prove that X iff [conditions]", provided the conditions are correct.
- "Show X. Plot Y." → "Prove X." (non-formalizable goal removed), provided the removed goal is genuinely non-formalizable and the retained goal is preserved.
- Adding inline definitions of standard mathematical concepts (convexity, dual cone, conjugate function) for self-containedness.
- Making implicit variables, domains, or quantifiers explicit.
- Splitting "Show X. Find Y." into two explicit claims, both stated precisely.
- Converting "Either prove or give a counterexample" into a definite claim with the correct answer.
- Rewriting the task using one or more equivalent theorem-style formulations, provided they preserve the same mathematical content and do not add a new independent claim.

**Key principle**: If `problem` says "Find Z" and `problem_finally` says "Prove that Z = [answer]", this is drift **only if** the answer is wrong. If the answer is correct, this is an authorized conversion.

### 5.2.3 Uncertain truth-value cases

Some repaired items come from prompts such as "either prove or give a counterexample" or "determine whether X holds". In these cases, the repair is allowed to choose one side and rewrite it as a definite theorem-style claim, but only if that chosen side is correct.

- If the repaired statement picks one side and you can verify that it is correct, do **not** flag `task_drift` merely because the original wording was open-ended.
- If the repaired statement picks one side but the truth of that side is unclear, unsupported, or not verifiable from the provided information and standard mathematical reasoning, do **not** accept it with high confidence.
- If the repaired statement appears mathematically plausible but lacks enough support to justify the chosen side, return `hold` and explain that the conclusion needs verification or a corrected counterexample/proof target.

### 5.3 `missing_dependency`

`problem_finally` relies on an unresolved external reference (a tag, theorem, lemma, algorithm, or previous exercise) that is not stated or inlined.

### 5.4 `missing_def`

A technical term, function, operator, or mathematical object is used without a definition precise enough for formalization.

**Do not flag** well-known standard mathematical notation (e.g., `ℝⁿ`, `‖x‖₂`, `Sⁿ₊₊`) unless it is genuinely ambiguous in context.

## 6. Correctness Check for Embedded Answers

When the repair embeds a concrete answer (e.g., "Prove that K* = ℝ²" or "Prove that inf = 5"), you must verify that the answer is correct.

This correctness check is mandatory. The benchmark must only keep repaired items whose mathematical conclusions are correct.

**How to verify:**

1. If `proof` or `direct_answer` is provided, check that the embedded answer matches.
2. If not provided, use your mathematical knowledge to verify.
3. If the answer is wrong, flag `task_drift` with `value: true` and return `hold`. In `reason`, state what the correct answer is. In `suggestion_fix`, provide the corrected conclusion.
4. If you cannot verify the answer with sufficient confidence, return `hold` rather than `accept`.

## 7. Handling `__DISCARD__` Items

If `problem_finally` equals the literal string `"__DISCARD__"`, the repair stage judged this item as inherently non-formalizable.

- If the original `problem` is indeed non-formalizable (pure plot/sketch/implement/simulate), return `hold` with reason "Correctly discarded: non-formalizable task."
- If the original `problem` contains formalizable mathematical content that should have been preserved, return `revise` with `task_drift = true` and explain what content should be recovered.

## 8. Writing Rules for Each Issue

For each issue type, provide:

- `value`: `true` or `false`
- `reason`: concise explanation. If `true`, identify the specific problem. If `false`, briefly state why no issue was found.
- `suggestion_fix`: if `true`, give the exact fix. If `false`, write `"No fix needed."`

## 9. Overall Status Rules

### 9.1 `accept`

All five questions from §4 answered positively, no issue flagged true, and there is no unresolved truth-value uncertainty.
Before deciding `accept`, you must explicitly check boundary cases such as nonemptiness and zero-valued edge conditions; if a boundary case fails, provide a concrete counterexample and set `overall_status = revise` with a clear reason.

### 9.2 `revise`

Any of `missing_assumption`, `task_drift`, or `missing_def` is `true`, but the repaired statement remains mathematically correct and the issue is fixable.

### 9.3 `hold`

Any of:
- `missing_dependency = true`
- The repaired statement is mathematically false, or its embedded answer/conclusion cannot be verified with sufficient confidence
- The task remains unsuitable for Lean formalization after repair (still open-ended, still contains "determine"/"describe"/"compute" without explicit conclusion)
- `problem_finally` is `"__DISCARD__"` but should not be (see §7)
- Parse/review generation failure

### 9.4 Decision Priority

If multiple issues are present, report all. For `overall_status`:

1. If `missing_dependency = true` → `hold`.
2. If the repaired statement is mathematically false, or its truth cannot be verified confidently → `hold`.
3. If task still unsuitable for Lean → `hold`.
4. If any of `missing_assumption`, `task_drift`, `missing_def` is `true` → `revise`, unless the issue is mathematical incorrectness, in which case use `hold`.
5. Otherwise → `accept`.

## 10. Confidence

Provide `confidence` as a number between 0 and 1.

Higher when:
- The comparison is unambiguous
- The embedded answer is verifiable
- The dependency structure is clear

Lower when:
- The original problem is ambiguous
- The embedded answer cannot be easily verified
- Multiple plausible mathematical readings exist

## 11. Output Schema

Return exactly one JSON object:

```json
{
  "source_idx": "Exercise 2.3",
  "source": "...",
  "overall_status": "accept|revise|hold",
  "reason": "...",
  "issue_type": {
    "missing_assumption": {
      "value": "true|false",
      "reason": "...",
      "suggestion_fix": "..."
    },
    "task_drift": {
      "value": "true|false",
      "reason": "...",
      "suggestion_fix": "..."
    },
    "missing_dependency": {
      "value": "true|false",
      "reason": "...",
      "suggestion_fix": "..."
    },
    "missing_def": {
      "value": "true|false",
      "reason": "...",
      "suggestion_fix": "..."
    }
  },
  "confidence": 0.0
}
```

No markdown. No extra text.

## 12. Review Instructions

1. Read `problem` and `problem_finally` carefully.
2. Treat `problem` as the semantic source of truth.
3. Remember that exercise-to-theorem conversion is **authorized**. Do not flag it as drift unless the embedded answer is wrong or mathematical meaning is altered.
4. Equivalent restatements are allowed if they preserve the same mathematical content. Only mark `task_drift = true` when an additional restatement changes the meaning or adds a new independent claim.
5. If `proof` or `direct_answer` is available, use them to verify embedded answers.
6. For open-ended originals such as "determine whether" or "either prove or give a counterexample", verify that the repaired statement chose the correct side before accepting it.
7. If the repaired statement is false, or if you cannot verify its mathematical correctness with sufficient confidence, return `hold`.
8. Keep each `reason` concise but specific. Cite the exact discrepancy.
9. Make each `suggestion_fix` actionable: provide the corrected text.
10. Report all issues found, even if only one drives `overall_status`.

## 13. Final Reminder

The item under review has been **deliberately rewritten** from exercise-style to theorem-style. Your job is not to penalize this reformulation, but to verify that:

1. The reformulation preserves the original mathematical intent.
2. Any embedded answer or explicit conclusion is correct.
3. The statement is self-contained, with all definitions present.
4. The statement is suitable for Lean formalization.
5. the repaired statement is mathematically correct

If all five hold, accept. If fixable issues exist, revise. If structural blocks remain, hold.
Mathematical correctness is non-negotiable: if the repaired statement is false or not reliably verifiable, hold it.
