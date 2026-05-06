You are given a math exercise text in its original, unprocessed form — no extraction markers and no placeholder tokens exist yet. This is the very first extraction pass. Your task is to extract ONLY hint items from this raw text.

Hints include: explicit hints, suggested methods, auxiliary guidance

Critical boundary rules — internalize these before deciding what to extract:
- A hint is supplementary guidance that helps solve the problem — it is not the goal itself.
- Do not extract a statement as a hint if it is actually a goal (something to be proved/found), an assumption (a given condition), or a definition (a variable/function/set declaration). Those will be handled in subsequent extraction stages.
- Only extract hints that are explicitly present in the text — do not invent hints.

Hint detection requirement:
- Only treat a span as a hint if it is explicitly signaled in the text. A span counts as a hint only when at least one of the following is true:
  - It is labeled with an explicit hint marker such as "Hint:", "Hint.", "Note:", "Suggestion:", or similar editorial markers.
  - It contains permissive instructional phrasing such as "you may", "you might", "one can", "it may help to", or "try" when used to suggest an optional approach (case-insensitive). Plain imperative suggestions like "Consider" without permissive phrasing should be treated conservatively and not counted as a hint unless an explicit hint marker is present.

Rules:
1. Extract ONLY hints. Do not extract definitions, assumptions, or goals.
1a. Apply the Hint detection requirement above: if the candidate span lacks an explicit hint marker or permissive phrasing (e.g., "you may"), do NOT extract it as a hint.
2. Do NOT invent hints. Only extract hints that are explicitly present in the text.
3. A hint must be guidance or a suggested approach — never a bare definition, symbol declaration, domain membership statement, assumption, or goal (e.g. "f : R^n → R" or "x ∈ R^n" are definitions, not hints; "show that f is convex" is a goal, not a hint).
4. Use LaTeX-compatible syntax for math. Escape backslashes for JSON (e.g., \\in, \\le, \\mathbf{R}).
5. Do not solve the problem or add proofs.
6. After extracting hints, produce masked_text: copy the input text but replace the i-th extracted hint (1-indexed) with the **indexed** marker `[HINTi_EXTRACTED]`. For example, the first hint is replaced by `[HINT1_EXTRACTED]`, the second by `[HINT2_EXTRACTED]`, etc. No other markers exist in the input, so the output will only contain these indexed hint markers where hints were found.

Output format — output exactly one JSON object, nothing else:

```json
{
  "items": [
    {"id": "1", "text": "..."}
  ],
  "masked_text": "... [HINT1_EXTRACTED] ... remaining text ..."
}
```

If no hints are found, return:
```json
{
  "items": [],
  "masked_text": "<the input text unchanged>"
}
```

Do not output explanation, markdown fences, or any text outside the JSON object.

Now extract hints from the following text:
