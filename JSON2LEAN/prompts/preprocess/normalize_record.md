You are given a JSON array of preprocessed mathematical records. Each record has fields like `index`, `source`, `source_idx`, `kind`, `content`, and optionally `term`.

Your task is to normalize each record's `content` (and `term` if present) to standard mathematical English, following these rules:

Normalization rules:
1. Use standard mathematical language and notation.
2. Write definitions and theorem statements in standard mathematical English.
3. Do NOT add library-specific notation explanations (e.g., do not add "in Lean, this is..." or "using Mathlib's...").
4. Do NOT over-explain. Keep statements concise and precise.
5. Do NOT change the mathematical meaning or add claims not present in the original.
6. Do NOT merge or split records. Return exactly the same number of records.
7. Preserve LaTeX notation. Use standard conventions (e.g., \mathbf{R} for reals).
8. If a record is already well-written, return its content unchanged.

Output format — output exactly one JSON object, nothing else:

```json
{
  "records": [
    {"content": "normalized content for record 0"},
    {"content": "normalized content for record 1", "term": "normalized term"}
  ]
}
```

The `records` array must have exactly the same length as the input array. Include `term` in the output only if the input record had a `term` field.

Do not output explanation, markdown fences, or any text outside the JSON object.

Now normalize the following records:
