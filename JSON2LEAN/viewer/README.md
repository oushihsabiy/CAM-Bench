# JSON Diff Viewer

A lightweight, zero-build single-page tool for comparing `data/` (raw input) and `preprocessed_data/` (processed output) JSON files side-by-side with diff highlighting.

---

## Quick Start

Run a static server from the **repository root**:

```bash
# Python (built-in, recommended)
python -m http.server 8000

# OR Node.js
npx serve .
```

Then open: **http://localhost:8000/viewer/**

> The server **must** be started from the repository root (the directory that contains `data/` and `preprocessed_data/`), not from inside `viewer/`.

---

## Auto-load vs Manual Upload

| Scenario | Behaviour |
|---|---|
| Server started from repo root | Left sidebar automatically lists all `.json` files found in `data/`. Files with matching names in `preprocessed_data/` are shown as **paired** (⇄). Click any file to load both sides instantly. |
| File opened directly (`file://`) or server started from wrong folder | Directory scan returns nothing. Use the **Manual Upload** buttons at the bottom of the sidebar to pick files from your local filesystem. |

The auto-scan works by fetching the directory listing that Python's `http.server` returns as an HTML page and parsing the `<a href>` links — no server-side code required.

---

## UI Guide

### Sidebar
- **File list** — shows all discovered files. A green **⇄** badge means a matching file was found in both directories. A grey **1** badge means only one side is available.
- **Search** — filters the file list by name.
- **Manual Upload** — pick any two local JSON files to compare, independent of the server directories.

### Toolbar
| Control | Description |
|---|---|
| **Tree / Raw** | Switch between collapsible tree view and syntax-highlighted raw text view |
| **Diff only** | In tree mode, hides all unchanged fields so only changed nodes are visible |
| **⊞ Expand / ⊟ Collapse** | Expand or collapse all nodes in both panels |
| **↓ Export Diff** | Download the jsondiffpatch delta as a JSON file |

### Tree View
- Click the **▶** triangle (or anywhere on a row) to expand/collapse an object or array node.
- Nodes open automatically up to depth 4 (depth 2 for files > 5 MB).
- For large files a banner appears with an **Expand All** button scoped to that panel.

### Diff Highlighting
| Colour | Meaning |
|---|---|
| 🟢 Green left border | Field was **added** in the preprocessed version (right side only) |
| 🔴 Red left border | Field was **removed** from the preprocessed version (left side only) |
| 🟡 Amber left border | Field value was **modified** (shown on both sides) |
| 🟣 Purple left border | Object/array **contains** nested changes |

Long string values are truncated in the tree. Click the row to see the full value in the **info bar** at the bottom.

### Info Bar
Clicking any row in the tree shows, at the bottom of the page:
- The full **dot-path** to the field (e.g. `$[0].content.proof`)
- The value on the **left** (original) side
- The value on the **right** (preprocessed) side

### Export Diff
Clicking **↓ Export Diff** downloads a `.json` file containing:
```json
{
  "filename": "picks.json",
  "exportedAt": "2026-04-08T...",
  "summary": { "added": 5, "removed": 2, "modified": 12 },
  "delta": { ... }
}
```
The `delta` field follows the [jsondiffpatch delta format](https://github.com/benjamine/jsondiffpatch/blob/master/docs/deltas.md).

---

## Dependencies (CDN)

| Library | Version | Purpose |
|---|---|---|
| [jsondiffpatch](https://github.com/benjamine/jsondiffpatch) | 0.6.0 | Structural JSON diff |
| [highlight.js](https://highlightjs.org/) | 11.9.0 | Syntax highlighting in Raw view |

Both are loaded via CDN; no `npm install` required. The app works fully offline for manual uploads if cached, but requires a network connection on first load to fetch the CDN scripts.

---

## File Structure

```
viewer/
  index.html    — HTML shell + CDN imports
  app.js        — Application logic (discovery, rendering, diff)
  styles.css    — All styles (dark theme, diff colours, layout)
  README.md     — This file
```

---

## Browser Compatibility

Tested in modern evergreen browsers (Chrome 90+, Firefox 90+, Safari 15+, Edge 90+). Uses `fetch`, `DOMParser`, `TextEncoder`, `URL.createObjectURL`, and native `<details>`/`<summary>` — all widely available.
