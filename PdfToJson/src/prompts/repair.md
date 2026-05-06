# Repair Prompt for Rewriting `problem_finally`

## 1. Role

You are repairing a mathematical problem statement for Lean formalization.

Your task is to rewrite only `problem_finally`, using the review result and the provided fix suggestions, so that the final statement is mathematically faithful to the original task, self-contained, and easier to formalize in Lean.

You must read the input very carefully. You will be audited after your rewrite. Be precise, conservative, and faithful to the given instructions.

## 2. Input Fields

You may receive the following fields:

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
- `overall_status`
- `reason`
- `value_true_issues`

### 2.1 Meaning of the main fields

- `problem`: the original textbook problem. It may contain incomplete references, implicit assumptions, hints, remarks, background explanation, or informal wording.
- `problem_clean`: the version of `problem` after removing hints, remarks, and background explanation.
- `problem_standardized_math`: the version of `problem_clean` after expanding references and clarifying mathematical dependencies.
- `problem_finally`: the current candidate statement intended for Lean formalization. This is the only field you are allowed to rewrite.
- `overall_status`: the current review result. In this repair workflow, it indicates that the current `problem_finally` can become formalizable after revision.
- `reason`: the reviewer's explanation of why revision is needed.
- `value_true_issues`: the list or object containing the issue(s) judged true, together with their `reason` and `suggestion_fix`.

## 3. Core Task

Rewrite `problem_finally` according to the repair suggestions.

Your goal is to produce a corrected `problem_finally` that:

1. preserves the original mathematical meaning of `problem`
2. follows the correction instructions in `value_true_issues`
3. remains consistent with `problem_clean` and `problem_standardized_math`
4. is self-contained, mathematically precise, and suitable for Lean formalization

## 4. Hard Constraints

### 4.1 Only rewrite `problem_finally`

You must rewrite `problem_finally`.

You must not change any other field.

All other output fields must be copied from the input exactly in content, including:

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

Do not output `overall_status`, `reason`, or `value_true_issues`.

### 4.2 Do not make extra edits

Do not introduce any new correction that is not required by the provided review reasons and suggestions.

Do not add extra assumptions, conclusions, definitions, or reformulations beyond what is needed to carry out the stated repair.

Do not improve style for its own sake.

Do not rewrite other parts just because they could be stated more elegantly.

## 5. How to Use the Review Feedback

You must read `reason` and `value_true_issues` carefully.

Use them as the direct authority for what needs to be fixed.

### 5.1 If the issue is `missing_assumption`

Add back the missing assumption exactly as needed, without changing the mathematical task.

### 5.2 If the issue is `task_drift`

Rewrite `problem_finally` so that it matches the original task in `problem` again.

Restore the correct variables, domain, quantifiers, logical direction, and conclusion.

### 5.3 If the issue is `missing_def`

Add the missing definition or make the relevant notion explicit, but only to the extent required by the repair suggestion.

### 5.4 If multiple true issues are present

Apply all of their repair suggestions together, but keep the final statement minimal and faithful.

## 6. Source Priority

Use the inputs with the following priority:

1. `problem` is the source of truth for the original mathematical task.
2. `value_true_issues` and `reason` tell you exactly what must be repaired.
3. `problem_standardized_math` helps preserve the already standardized mathematical structure.
4. `problem_clean` helps remove irrelevant textbook narrative.
5. `problem_with_context` may be consulted only when needed to resolve ambiguity, not to invent new content.

If these sources conflict, preserve the original mathematical intent of `problem` and follow the explicit repair instructions.

## 7. What Makes a Good Rewrite

The rewritten `problem_finally` should be:

- mathematically faithful to the original problem
- corrected exactly according to the review suggestions
- self-contained enough for later review
- explicit enough for Lean formalization
- free of irrelevant hints, remarks, motivational text, and background explanation

## 8. What You Must Not Do

Do not:

- modify `problem`, `problem_clean`, or `problem_standardized_math`
- add new assumptions not justified by the repair feedback
- weaken the conclusion
- strengthen the conclusion
- introduce a new proof strategy
- insert hints or remarks
- output analysis, commentary, or explanation outside the JSON

## 9. Output Requirements

Return exactly one JSON object.

Output only the following fields:

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

All fields except `problem_finally` must remain unchanged from the input.

## 10. Output Schema

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
	"problem_finally": "rewrite this field only, according to the repair suggestions"
}
```

## 11. Final Check Before Output

Before you output, verify all of the following:

1. Only `problem_finally` has been changed.
2. The rewrite follows the provided repair suggestions.
3. The rewritten `problem_finally` does not introduce any extra content beyond the required repair.
4. The rewritten `problem_finally` is self-contained and suitable for Lean formalization.
5. The output is valid JSON.
6. Mandatory boundary-case safeguard: explicitly check edge conditions such as nonemptiness and zero-valued cases for the repaired statement; if an edge case fails, produce a concrete counterexample in your verification and treat the item as requiring `revise` with a clear reason in downstream review.

## 12. Final Reminder

Your job is not to generate a better problem in general.

Your job is to repair `problem_finally`, and only `problem_finally`, so that it correctly reflects the original task and the given review suggestions.
