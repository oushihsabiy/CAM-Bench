# mathdoc-parser

`mathdoc-parser` is a pipeline for converting mathematical textbook PDFs into structured, formalization-ready JSON. It extracts exercises, theorems, definitions, and proofs through a multi-stage process and then standardises, reviews, and optionally repairs the results for downstream Lean formalisation.

## Pipeline Overview

```
PDF ──► Markdown ──► LaTeX ──► JSON ──► Naturalized JSON ──► Review ──► Summary
                                                                 │
                                                          ┌──────┴──────┐
                                                          │  revise-only │
                                                          │  (repair →   │
                                                          │   re-review →│
                                                          │   re-summary)│
                                                          └─────────────┘
                                                                 │
                                                          ┌──────┴──────┐
                                                          │   hold-only  │
                                                          │ (repair_hold→│
                                                          │  review_hold→│
                                                          │  re-summary) │
                                                          └─────────────┘
```

### Main stages

| # | Stage | Script | Description |
|---|-------|--------|-------------|
| 1 | PDF → Markdown | `src/book/pdfTomd.py` | Page-wise OCR via vision API; outputs `<!-- PAGE n -->` Markdown |
| 2 | Markdown → LaTeX | `src/book/mdTotex.py` | Semantic chunking, tag recovery, LaTeX structure |
| 3 | LaTeX → JSON | `src/book/texTojson.py` | Structured extraction with dependency tracking, type inference, problem cleaning |
| 4 | Naturalize | `src/book/jsonNaturalize.py` | LLM-based standardisation: dependency folding, concise rewriting |
| 5 | Review | `src/review/read.py` + `src/review/review.py` | Per-item LLM review (missing assumptions, task drift, missing deps, missing defs) |
| 6 | Summary | `src/review/summary.py` | Splits results into `accept` / `hold` / `revise`; updates reviewchat tables |
| 7 | Revise Repair (optional) | `src/review/repair.py` → `read.py` → `summary.py` | Rewrites `revise` items, re-reviews, re-splits |
| 8 | Hold Repair (optional) | `src/review/repair_hold.py` → `read.py`(review_hold) → `summary.py` | Rewrites hold(except missing_dependency) items to `-re3`, re-reviews, re-splits |

### Reviewchat tables

`src/review/reviewchat.py` generates per-prefix aggregation tables:

- `chat1`: processing efficiency across `round1_origin` / `round2_revise` / `round3_hold(except missing_dependency)`
- `chat2`: revise reason counts (`missing_assumption`, `task_drift`, `missing_def`)
- `chat3`: hold reason counts (`missing_dependency`, `unsuitable_lean`, `parse_error`)

Outputs: `table.md`, `table.json`, `table.csv`, `table_chat2.csv`, `table_chat3.csv`.

## Repository Layout

```
main.py                        # Pipeline runner with resume support
settings.json                  # Root-level pipeline settings
config.json                    # API credentials (git-ignored; see config.example.json)
src/
  book/
    pdfTomd.py                 # Stage 1: PDF → Markdown (OCR)
    mdTotex.py                 # Stage 2: Markdown → LaTeX
    texTojson.py               # Stage 3: LaTeX → JSON
    jsonNaturalize.py          # Stage 4: Naturalize JSON
    settings.json              # Stage-level settings (OCR, TeX, JSON)
  review/
    read.py                    # Stage 5: batch review orchestrator
    review.py                  # Stage 5: single-item LLM review
    reviewchat.py              # Reviewchat table generator
    summary.py                 # Stage 6: split by status + reviewchat update
    repair.py                  # Stage 7: LLM repair for revise items
    repair_run.py              # Stage 7: standalone repair pipeline runner
    repair_hold.py             # Stage 8: LLM repair for hold items (except missing_dependency)
    hold_run.py                # Stage 8: standalone hold pipeline runner
  prompts/
    clean_problem.md           # Prompt: problem text cleaning
    make_problem_complete.md   # Prompt: dependency-folded complete rewrite
    make_problem_concise.md    # Prompt: concise formalization-friendly rewrite
    review.md                  # Prompt: review criteria
    repair.md                  # Prompt: repair criteria
    review_hold.md             # Prompt: hold re-review criteria
    repair_hold.md             # Prompt: hold repair criteria
  token_usage.py               # API token usage logging
input_pdfs/book/               # Place input PDFs here
work/                          # Intermediate Markdown and LaTeX files
output_json/                   # Stage 3 JSON output
output_json_naturalized/       # Stage 4 naturalized JSON output
output_review/
  reviewlog/                   # Stage 5 review reports
  hold/                        # Stage 6 hold items
  accept/                      # Stage 6 accepted items
  revise/                      # Stage 6 items to revise
    book/                      # Revise inputs for repair pipeline
    rewrite/                   # Repair outputs
    reviewlog/                 # Re-review reports
    split/                     # Re-summary outputs
  hold/
    rewrite/                   # Hold repair outputs (-re3)
    reviewlog/                 # Hold re-review reports
    split/                     # Hold re-summary outputs
  reviewchat/                  # Aggregation tables
```

## Configuration

### API credentials

Copy `config.example.json` to `config.json` and fill in:

```json
{
  "api_key": "sk-...",
  "base_url": "https://api.openai.com/v1",
  "model": "gpt-4o"
}
```

`config.json` is git-ignored.

### Pipeline settings

Root `settings.json` controls pipeline behaviour (input/output directories, toggle switches, model names, token limits, worker counts, etc.). Stage-level settings live in `src/book/settings.json`.

Key toggles:

| Setting | Default | Description |
|---------|---------|-------------|
| `ENABLE_NATURALIZE` | `false` | Run LLM naturalisation after JSON extraction |
| `ENABLE_REVIEW` | `false` | Run LLM review after naturalisation |
| `ENABLE_REPAIR_PIPELINE` | `false` | Run repair pipeline for revise items |
| `ENABLE_HOLD_PIPELINE` | `false` | Run hold-only repair pipeline |
| `TEX_CLEAN_PROBLEM` | `false` | Clean problem text before dependency extraction |
| `STRICT_RESUME` | `true` | Validate stage output completeness before skipping |
| `ATOMIC_OUTPUTS` | `true` | Write to temp file then rename (crash-safe) |

## Usage

### Full pipeline

```bash
python main.py
```

### Review + Summary only (reuse existing JSON)

```bash
python src/review/summary.py --review-only
```

### Summary only (reuse existing review logs)

```bash
python src/review/summary.py --summary-only
```

### Revise-only repair cycle

```bash
python src/review/repair_run.py --revise-only
```

### Hold-only repair cycle

```bash
python src/review/hold_run.py --hold-only
```

See `命令.md` for more command examples including single-file reruns and component-level invocations.

## Requirements

- Python 3.10+
- OpenAI-compatible API access (for OCR, LLM stages)
- PyMuPDF (`fitz`) for PDF page counting and text extraction

Install dependencies:

```bash
pip install openai pymupdf
```

## License

Released under the Apache License 2.0. See [LICENSE](LICENSE) for details.
