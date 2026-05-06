#!/usr/bin/env python3
"""
Generate per-problem timing data and an 8-hour cumulative success-rate curve
for the Strict-Isolated-8h benchmark protocol.

No third-party plotting dependency is required. The figure is emitted as SVG.
"""

from __future__ import annotations

import csv
import html
import math
import re
from collections import defaultdict
from pathlib import Path


ROOT = Path("/root/workspace/benchmark/JSON2LEAN")
COMPARE_DIR = ROOT / "记录" / "compare"
M2F_CSV = ROOT / "lean/m2f/final99_run_summary_20260504T131426Z/per_problem_summary.csv"
M2F_PROBLEMS = ROOT / "lean/m2f/problems"
ARISTOTLE_MD = ROOT / "记录/精确记录.md"

PER_PROBLEM_OUT = COMPARE_DIR / "strict_isolated_8h_per_problem_times_20260505.csv"
HOURLY_OUT = COMPARE_DIR / "strict_isolated_8h_hourly_curve_20260505.csv"
SVG_OUT = COMPARE_DIR / "strict_isolated_8h_success_curve_20260505.svg"
PDF_OUT = COMPARE_DIR / "strict_isolated_8h_success_curve_20260505.pdf"
SUMMARY_OUT = COMPARE_DIR / "strict_isolated_8h_curve说明_20260505.md"

N_PROBLEMS = 200
TIME_BUDGET_MIN = 8 * 60
X_AXIS_MAX_HOURS = 8.0


def pseudo_log_x_fraction(hours: float) -> float:
    if hours < 0:
        raise ValueError("pseudo-log x coordinate requires a nonnegative hour value")
    return math.log1p(hours) / math.log1p(X_AXIS_MAX_HOURS)


def problem_num(name: str) -> int:
    match = re.search(r"\d+", name)
    if not match:
        raise ValueError(f"cannot parse problem number from {name!r}")
    return int(match.group(0))


def strip_lean_comments(text: str) -> str:
    """Remove line and block comments while preserving line count."""
    out: list[str] = []
    i = 0
    block_depth = 0
    while i < len(text):
        if block_depth:
            if text.startswith("/-", i):
                block_depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        else:
            if text.startswith("--", i):
                while i < len(text) and text[i] != "\n":
                    out.append(" ")
                    i += 1
            elif text.startswith("/-", i):
                block_depth = 1
                out.extend("  ")
                i += 2
            else:
                out.append(text[i])
                i += 1
    return "".join(out)


def read_m2f_rows() -> dict[int, dict[str, str]]:
    rows: dict[int, dict[str, str]] = {}
    with M2F_CSV.open(newline="") as f:
        for row in csv.DictReader(f):
            n = problem_num(row["problem"])
            row["problem_num"] = str(n)
            rows[n] = row
    if len(rows) != N_PROBLEMS:
        raise RuntimeError(f"expected {N_PROBLEMS} m2f rows, got {len(rows)}")
    return rows


def scan_m2f_problem_files() -> tuple[dict[int, list[str]], dict[int, list[str]]]:
    pseudo: dict[int, list[str]] = defaultdict(list)
    cross_imports: dict[int, list[str]] = defaultdict(list)
    pseudo_patterns = [
        ("exact?", re.compile(r"(?<![A-Za-z0-9_])exact\?(?![A-Za-z0-9_])")),
        ("sorryAx", re.compile(r"(?<![A-Za-z0-9_])sorryAx(?![A-Za-z0-9_])")),
        ("sorry", re.compile(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])")),
        ("admit", re.compile(r"(?<![A-Za-z0-9_])admit(?![A-Za-z0-9_])")),
    ]
    import_pattern = re.compile(r"^\s*import\s+(?:problems|m2f\.problems)\.?\«?problem-?\d+")

    for path in sorted(M2F_PROBLEMS.glob("problem-*.lean"), key=lambda p: problem_num(p.name)):
        n = problem_num(path.name)
        code = strip_lean_comments(path.read_text(errors="ignore"))
        for lineno, line in enumerate(code.splitlines(), start=1):
            stripped = line.strip()
            if import_pattern.search(line):
                cross_imports[n].append(f"{lineno}: {stripped}")
            for kind, pattern in pseudo_patterns:
                if pattern.search(line):
                    pseudo[n].append(f"{lineno}: {kind}: {stripped}")
    return pseudo, cross_imports


def parse_aristotle_records() -> dict[int, dict[str, str | float | bool]]:
    text = ARISTOTLE_MD.read_text(errors="ignore")
    records: dict[int, dict[str, str | float | bool]] = {}
    block_pattern = re.compile(
        r'<a id="problem-(\d+)"></a>(.*?)(?=<a id="problem-\d+"></a>|<a id="exact-list"></a>)',
        re.S,
    )
    for match in block_pattern.finditer(text):
        n = int(match.group(1))
        block = match.group(2)
        time_match = re.search(r"用时：([^\n]+)", block)
        mark_match = re.search(r"人工标记[：:]\s*([^\n]+)", block)
        if not time_match or not mark_match:
            raise RuntimeError(f"missing Aristotle fields for problem {n}")
        time_text = time_match.group(1).strip()
        mark = mark_match.group(1).strip()
        hm = re.fullmatch(r"(?:(\d+)h)?(?:(\d+)m)?", time_text)
        if not hm:
            raise RuntimeError(f"cannot parse Aristotle time for problem {n}: {time_text}")
        minutes = int(hm.group(1) or 0) * 60 + int(hm.group(2) or 0)
        records[n] = {
            "minutes": float(minutes),
            "time_text": time_text,
            "mark": mark,
            "loose_yes": mark.lower().startswith("yes"),
            "has_exact": "exact?" in mark.lower(),
            "is_xiu": "xiu" in mark.lower(),
        }
    if len(records) != N_PROBLEMS:
        raise RuntimeError(f"expected {N_PROBLEMS} Aristotle rows, got {len(records)}")
    return records


def m2f_classification(
    row: dict[str, str], pseudo: dict[int, list[str]], cross_imports: dict[int, list[str]]
) -> tuple[bool, str]:
    n = int(row["problem_num"])
    minutes = float(row["minutes_total"] or 0.0)
    if row["reason_group"] != "done":
        return False, f"not_done:{row['reason_group']}"
    if minutes > TIME_BUDGET_MIN:
        return False, "over_8h"
    if n in pseudo:
        return False, "pseudo_proof"
    if n in cross_imports:
        return False, "cross_problem_import"
    return True, "success"


def aristotle_classification(record: dict[str, str | float | bool]) -> tuple[bool, str]:
    minutes = float(record["minutes"])
    if not bool(record["loose_yes"]):
        return False, "not_yes"
    if minutes > TIME_BUDGET_MIN:
        return False, "over_8h"
    if bool(record["has_exact"]):
        return False, "exact?"
    if bool(record["is_xiu"]):
        return False, "xiu"
    return True, "success"


def pct(count: int) -> float:
    return count / N_PROBLEMS * 100.0


def write_csvs() -> tuple[list[dict[str, str]], list[dict[str, str]]]:
    m2f_rows = read_m2f_rows()
    pseudo, cross_imports = scan_m2f_problem_files()
    aristotle = parse_aristotle_records()

    per_problem_rows: list[dict[str, str]] = []
    for n in range(1, N_PROBLEMS + 1):
        m2f = m2f_rows[n]
        ari = aristotle[n]
        m2f_minutes = float(m2f["minutes_total"] or 0.0)
        ari_minutes = float(ari["minutes"])
        m2f_success, m2f_exclusion = m2f_classification(m2f, pseudo, cross_imports)
        ari_success, ari_exclusion = aristotle_classification(ari)
        per_problem_rows.append(
            {
                "problem": str(n),
                "m2f_minutes": f"{m2f_minutes:.2f}",
                "m2f_hours": f"{m2f_minutes / 60.0:.4f}",
                "m2f_reason_group": m2f["reason_group"],
                "m2f_tokens_used_source": m2f["tokens_used_source"],
                "m2f_has_pseudo": "yes" if n in pseudo else "no",
                "m2f_pseudo_lines": " | ".join(pseudo.get(n, [])),
                "m2f_cross_import": "yes" if n in cross_imports else "no",
                "m2f_cross_import_lines": " | ".join(cross_imports.get(n, [])),
                "m2f_strict_isolated_8h_success": "yes" if m2f_success else "no",
                "m2f_exclusion_reason": m2f_exclusion,
                "aristotle_minutes": f"{ari_minutes:.2f}",
                "aristotle_hours": f"{ari_minutes / 60.0:.4f}",
                "aristotle_mark": str(ari["mark"]),
                "aristotle_loose_yes": "yes" if ari["loose_yes"] else "no",
                "aristotle_has_exact": "yes" if ari["has_exact"] else "no",
                "aristotle_is_xiu": "yes" if ari["is_xiu"] else "no",
                "aristotle_strict_isolated_8h_success": "yes" if ari_success else "no",
                "aristotle_exclusion_reason": ari_exclusion,
            }
        )

    with PER_PROBLEM_OUT.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(per_problem_rows[0].keys()))
        writer.writeheader()
        writer.writerows(per_problem_rows)

    hourly_rows: list[dict[str, str]] = []
    for hour in range(0, 9):
        threshold = hour * 60.0
        m2f_count = sum(
            1
            for r in per_problem_rows
            if r["m2f_strict_isolated_8h_success"] == "yes"
            and float(r["m2f_minutes"]) <= threshold
        )
        ari_count = sum(
            1
            for r in per_problem_rows
            if r["aristotle_strict_isolated_8h_success"] == "yes"
            and float(r["aristotle_minutes"]) <= threshold
        )
        hourly_rows.append(
            {
                "hour": str(hour),
                "budget_minutes": f"{threshold:.0f}",
                "m2f_solved": str(m2f_count),
                "m2f_success_rate_pct_of_200": f"{pct(m2f_count):.2f}",
                "aristotle_solved": str(ari_count),
                "aristotle_success_rate_pct_of_200": f"{pct(ari_count):.2f}",
            }
        )

    with HOURLY_OUT.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(hourly_rows[0].keys()))
        writer.writeheader()
        writer.writerows(hourly_rows)

    return per_problem_rows, hourly_rows


def monotone_smooth_path(points: list[tuple[float, float]]) -> str:
    """Fritsch-Carlson monotone cubic Hermite path through exact points."""
    if len(points) < 2:
        return ""
    xs = [p[0] for p in points]
    ys = [p[1] for p in points]
    n = len(points)
    h = [xs[i + 1] - xs[i] for i in range(n - 1)]
    delta = [(ys[i + 1] - ys[i]) / h[i] for i in range(n - 1)]
    m = [0.0] * n
    m[0] = delta[0]
    m[-1] = delta[-1]
    for i in range(1, n - 1):
        if delta[i - 1] * delta[i] <= 0:
            m[i] = 0.0
        else:
            m[i] = (delta[i - 1] + delta[i]) / 2.0
    for i in range(n - 1):
        if delta[i] == 0:
            m[i] = 0.0
            m[i + 1] = 0.0
        else:
            a = m[i] / delta[i]
            b = m[i + 1] / delta[i]
            s = a * a + b * b
            if s > 9:
                tau = 3 / math.sqrt(s)
                m[i] = tau * a * delta[i]
                m[i + 1] = tau * b * delta[i]

    parts = [f"M {xs[0]:.2f} {ys[0]:.2f}"]
    for i in range(n - 1):
        c1x = xs[i] + h[i] / 3.0
        c1y = ys[i] + m[i] * h[i] / 3.0
        c2x = xs[i + 1] - h[i] / 3.0
        c2y = ys[i + 1] - m[i + 1] * h[i] / 3.0
        parts.append(f"C {c1x:.2f} {c1y:.2f}, {c2x:.2f} {c2y:.2f}, {xs[i+1]:.2f} {ys[i+1]:.2f}")
    return " ".join(parts)


def render_svg(hourly_rows: list[dict[str, str]]) -> None:
    width, height = 800, 520
    margin_left, margin_right, margin_top, margin_bottom = 98, 30, 36, 84
    plot_w = width - margin_left - margin_right
    plot_h = height - margin_top - margin_bottom
    y_min, y_max = 0.0, 100.0

    def sx(x: float) -> float:
        return margin_left + pseudo_log_x_fraction(x) * plot_w

    def sy(y: float) -> float:
        return margin_top + (y_max - y) / (y_max - y_min) * plot_h

    m2f_points = [
        (sx(float(r["hour"])), sy(float(r["m2f_success_rate_pct_of_200"]))) for r in hourly_rows
    ]
    ari_points = [
        (sx(float(r["hour"])), sy(float(r["aristotle_success_rate_pct_of_200"]))) for r in hourly_rows
    ]

    m2f_path = monotone_smooth_path(m2f_points)
    ari_path = monotone_smooth_path(ari_points)

    grid = []
    for hour in range(0, 9):
        x = sx(hour)
        grid.append(f'<line x1="{x:.2f}" y1="{margin_top}" x2="{x:.2f}" y2="{height-margin_bottom}" class="grid"/>')
        grid.append(f'<text x="{x:.2f}" y="{height-margin_bottom+34}" class="tick" text-anchor="middle">{hour}</text>')
    for y in range(0, 101, 10):
        yy = sy(y)
        grid.append(f'<line x1="{margin_left}" y1="{yy:.2f}" x2="{width-margin_right}" y2="{yy:.2f}" class="grid"/>')
        grid.append(f'<text x="{margin_left-16}" y="{yy+6:.2f}" class="tick" text-anchor="end">{y}%</text>')

    markers = []
    for r in hourly_rows:
        hour = float(r["hour"])
        m2f_rate = float(r["m2f_success_rate_pct_of_200"])
        ari_rate = float(r["aristotle_success_rate_pct_of_200"])
        x = sx(hour)
        ym = sy(m2f_rate)
        ya = sy(ari_rate)
        markers.append(
            f'<circle cx="{x:.2f}" cy="{ym:.2f}" r="4.0" class="marker m2f">'
            f"<title>M2F {int(hour)}h: {r['m2f_solved']}/200 = {m2f_rate:.2f}%</title></circle>"
        )
        markers.append(
            f'<circle cx="{x:.2f}" cy="{ya:.2f}" r="4.0" class="marker ari">'
            f"<title>Aristotle {int(hour)}h: {r['aristotle_solved']}/200 = {ari_rate:.2f}%</title></circle>"
        )

    last = hourly_rows[-1]
    label_m2f = f"M2F: {last['m2f_solved']}/200 ({last['m2f_success_rate_pct_of_200']}%)"
    label_ari = f"Aristotle: {last['aristotle_solved']}/200 ({last['aristotle_success_rate_pct_of_200']}%)"
    legend_x = margin_left + 8
    legend_y = margin_top + 10
    legend_w = 400
    legend_h = 92

    svg = f'''<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">
  <style>
    .bg {{ fill: #ffffff; }}
    .panel {{ fill: #ffffff; stroke: #222; stroke-width: 1.2; }}
    .grid {{ stroke: #d2d2d2; stroke-width: 0.9; stroke-dasharray: 2 2; }}
    .axis {{ stroke: #222; stroke-width: 1.6; }}
    .tick {{ fill: #2f2f2f; font: 20px serif; }}
    .axis-label {{ fill: #111; font: 26px serif; }}
    .curve {{ fill: none; stroke-width: 3.4; stroke-linecap: round; stroke-linejoin: round; }}
    .m2f-line {{ stroke: #2ca02c; }}
    .ari-line {{ stroke: #ff7f0e; stroke-dasharray: 5 3; }}
    .marker {{ stroke: white; stroke-width: 1.7; }}
    .marker.m2f {{ fill: #2ca02c; }}
    .marker.ari {{ fill: #ff7f0e; }}
    .legend-box {{ fill: #ffffff; fill-opacity: 0.92; stroke: #b8b8b8; stroke-width: 0.9; }}
    .legend {{ fill: #111; font: 21px serif; }}
  </style>
  <rect class="bg" width="100%" height="100%"/>
  <rect x="{margin_left}" y="{margin_top}" width="{plot_w}" height="{plot_h}" class="panel"/>
  {''.join(grid)}
  <path d="{m2f_path}" class="curve m2f-line"/>
  <path d="{ari_path}" class="curve ari-line"/>
  {''.join(markers)}
  <line x1="{margin_left}" y1="{height-margin_bottom}" x2="{width-margin_right}" y2="{height-margin_bottom}" class="axis"/>
  <line x1="{margin_left}" y1="{margin_top}" x2="{margin_left}" y2="{height-margin_bottom}" class="axis"/>
  <text x="{margin_left + plot_w/2:.2f}" y="{height-24}" class="axis-label" text-anchor="middle">Time budget (hours, log(1+x) scale)</text>
  <text x="31" y="{margin_top + plot_h/2:.2f}" class="axis-label" text-anchor="middle" transform="rotate(-90 31 {margin_top + plot_h/2:.2f})">Cumulative success rate (%)</text>
  <rect x="{legend_x}" y="{legend_y}" width="{legend_w}" height="{legend_h}" class="legend-box"/>
  <line x1="{legend_x+20}" y1="{legend_y+30}" x2="{legend_x+72}" y2="{legend_y+30}" class="curve m2f-line"/>
  <circle cx="{legend_x+46}" cy="{legend_y+30}" r="4.0" class="marker m2f"/>
  <text x="{legend_x+88}" y="{legend_y+37}" class="legend">{html.escape(label_m2f)}</text>
  <line x1="{legend_x+20}" y1="{legend_y+66}" x2="{legend_x+72}" y2="{legend_y+66}" class="curve ari-line"/>
  <circle cx="{legend_x+46}" cy="{legend_y+66}" r="4.0" class="marker ari"/>
  <text x="{legend_x+88}" y="{legend_y+73}" class="legend">{html.escape(label_ari)}</text>
</svg>
'''
    SVG_OUT.write_text(svg)


def _pdf_escape(text: str) -> str:
    return text.replace("\\", "\\\\").replace("(", "\\(").replace(")", "\\)")


def _pdf_text(
    parts: list[str],
    x: float,
    y: float,
    text: str,
    size: float,
    *,
    anchor: str = "start",
    rotate90: bool = False,
) -> None:
    width = len(text) * size * 0.46
    if rotate90:
        if anchor == "middle":
            y -= width / 2
        elif anchor == "end":
            y -= width
        parts.append(f"BT /F1 {size:.1f} Tf 0 1 -1 0 {x:.2f} {y:.2f} Tm ({_pdf_escape(text)}) Tj ET")
    else:
        if anchor == "middle":
            x -= width / 2
        elif anchor == "end":
            x -= width
        parts.append(f"BT /F1 {size:.1f} Tf 1 0 0 1 {x:.2f} {y:.2f} Tm ({_pdf_escape(text)}) Tj ET")


def _pdf_circle(parts: list[str], x: float, y: float, r: float) -> None:
    c = 0.5522847498 * r
    parts.append(
        f"{x+r:.2f} {y:.2f} m "
        f"{x+r:.2f} {y+c:.2f} {x+c:.2f} {y+r:.2f} {x:.2f} {y+r:.2f} c "
        f"{x-c:.2f} {y+r:.2f} {x-r:.2f} {y+c:.2f} {x-r:.2f} {y:.2f} c "
        f"{x-r:.2f} {y-c:.2f} {x-c:.2f} {y-r:.2f} {x:.2f} {y-r:.2f} c "
        f"{x+c:.2f} {y-r:.2f} {x+r:.2f} {y-c:.2f} {x+r:.2f} {y:.2f} c B"
    )


def _pdf_smooth_path(points: list[tuple[float, float]]) -> str:
    # Same monotone cubic Hermite interpolation as the SVG path, emitted as PDF commands.
    if len(points) < 2:
        return ""
    xs = [p[0] for p in points]
    ys = [p[1] for p in points]
    n = len(points)
    h = [xs[i + 1] - xs[i] for i in range(n - 1)]
    delta = [(ys[i + 1] - ys[i]) / h[i] for i in range(n - 1)]
    m = [0.0] * n
    m[0] = delta[0]
    m[-1] = delta[-1]
    for i in range(1, n - 1):
        if delta[i - 1] * delta[i] <= 0:
            m[i] = 0.0
        else:
            m[i] = (delta[i - 1] + delta[i]) / 2.0
    for i in range(n - 1):
        if delta[i] == 0:
            m[i] = 0.0
            m[i + 1] = 0.0
        else:
            a = m[i] / delta[i]
            b = m[i + 1] / delta[i]
            s = a * a + b * b
            if s > 9:
                tau = 3 / math.sqrt(s)
                m[i] = tau * a * delta[i]
                m[i + 1] = tau * b * delta[i]

    parts = [f"{xs[0]:.2f} {ys[0]:.2f} m"]
    for i in range(n - 1):
        c1x = xs[i] + h[i] / 3.0
        c1y = ys[i] + m[i] * h[i] / 3.0
        c2x = xs[i + 1] - h[i] / 3.0
        c2y = ys[i + 1] - m[i + 1] * h[i] / 3.0
        parts.append(f"{c1x:.2f} {c1y:.2f} {c2x:.2f} {c2y:.2f} {xs[i+1]:.2f} {ys[i+1]:.2f} c")
    return " ".join(parts)


def render_pdf(hourly_rows: list[dict[str, str]]) -> None:
    width, height = 800.0, 520.0
    margin_left, margin_right, margin_top, margin_bottom = 98.0, 30.0, 36.0, 84.0
    plot_w = width - margin_left - margin_right
    plot_h = height - margin_top - margin_bottom

    def sx(x: float) -> float:
        return margin_left + pseudo_log_x_fraction(x) * plot_w

    def sy(y: float) -> float:
        return height - (margin_top + (100.0 - y) / 100.0 * plot_h)

    m2f_points = [
        (sx(float(r["hour"])), sy(float(r["m2f_success_rate_pct_of_200"]))) for r in hourly_rows
    ]
    ari_points = [
        (sx(float(r["hour"])), sy(float(r["aristotle_success_rate_pct_of_200"]))) for r in hourly_rows
    ]

    content: list[str] = []
    content.append("1 1 1 rg 0 0 800 520 re f")
    content.append("1 1 1 rg 0 0 0 RG 1.2 w")
    content.append(f"{margin_left:.2f} {height-margin_top-plot_h:.2f} {plot_w:.2f} {plot_h:.2f} re B")

    content.append("0.82 0.82 0.82 RG 0.9 w [2 2] 0 d")
    for hour in range(0, 9):
        x = sx(hour)
        content.append(f"{x:.2f} {height-margin_top:.2f} m {x:.2f} {height-margin_top-plot_h:.2f} l S")
    for y in range(0, 101, 10):
        yy = sy(y)
        content.append(f"{margin_left:.2f} {yy:.2f} m {width-margin_right:.2f} {yy:.2f} l S")

    content.append("0 0 0 RG 1.6 w [] 0 d")
    content.append(f"{margin_left:.2f} {height-margin_top-plot_h:.2f} m {width-margin_right:.2f} {height-margin_top-plot_h:.2f} l S")
    content.append(f"{margin_left:.2f} {height-margin_top:.2f} m {margin_left:.2f} {height-margin_top-plot_h:.2f} l S")

    content.append("0.1725 0.6275 0.1725 RG 3.4 w [] 0 d")
    content.append(_pdf_smooth_path(m2f_points) + " S")
    content.append("1.0 0.498 0.055 RG 3.4 w [5 3] 0 d")
    content.append(_pdf_smooth_path(ari_points) + " S")

    content.append("1 1 1 RG 1.7 w [] 0 d")
    for x, y in m2f_points:
        content.append("0.1725 0.6275 0.1725 rg")
        _pdf_circle(content, x, y, 4.0)
    for x, y in ari_points:
        content.append("1.0 0.498 0.055 rg")
        _pdf_circle(content, x, y, 4.0)

    content.append("0 0 0 rg")
    for hour in range(0, 9):
        _pdf_text(content, sx(hour), height - (height - margin_bottom + 34), str(hour), 20, anchor="middle")
    for y in range(0, 101, 10):
        _pdf_text(content, margin_left - 16, sy(y) - 6, f"{y}%", 20, anchor="end")

    _pdf_text(content, margin_left + plot_w / 2, 24, "Time budget (hours, log(1+x) scale)", 26, anchor="middle")
    _pdf_text(content, 31, height - (margin_top + plot_h / 2), "Cumulative success rate (%)", 26, anchor="middle", rotate90=True)

    last = hourly_rows[-1]
    label_m2f = f"M2F: {last['m2f_solved']}/200 ({last['m2f_success_rate_pct_of_200']}%)"
    label_ari = f"Aristotle: {last['aristotle_solved']}/200 ({last['aristotle_success_rate_pct_of_200']}%)"
    legend_x = margin_left + 8
    legend_y = height - margin_top - 10 - 92
    content.append("1 1 1 rg 0.72 0.72 0.72 RG 0.9 w")
    content.append(f"{legend_x:.2f} {legend_y:.2f} 400 92 re B")
    content.append("0.1725 0.6275 0.1725 RG 3.4 w [] 0 d")
    content.append(f"{legend_x+20:.2f} {legend_y+62:.2f} m {legend_x+72:.2f} {legend_y+62:.2f} l S")
    content.append("0.1725 0.6275 0.1725 rg 1 1 1 RG 1.7 w")
    _pdf_circle(content, legend_x + 46, legend_y + 62, 4.0)
    content.append("0 0 0 rg")
    _pdf_text(content, legend_x + 88, legend_y + 55, label_m2f, 21)
    content.append("1.0 0.498 0.055 RG 3.4 w [5 3] 0 d")
    content.append(f"{legend_x+20:.2f} {legend_y+26:.2f} m {legend_x+72:.2f} {legend_y+26:.2f} l S")
    content.append("1.0 0.498 0.055 rg 1 1 1 RG 1.7 w [] 0 d")
    _pdf_circle(content, legend_x + 46, legend_y + 26, 4.0)
    content.append("0 0 0 rg")
    _pdf_text(content, legend_x + 88, legend_y + 19, label_ari, 21)

    stream = "\n".join(content).encode("ascii")
    objects = [
        b"<< /Type /Catalog /Pages 2 0 R >>",
        b"<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
        f"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 {width:.0f} {height:.0f}] /Resources << /Font << /F1 4 0 R >> >> /Contents 5 0 R >>".encode("ascii"),
        b"<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>",
        b"<< /Length " + str(len(stream)).encode("ascii") + b" >>\nstream\n" + stream + b"\nendstream",
    ]
    pdf = bytearray(b"%PDF-1.4\n")
    offsets = [0]
    for i, obj in enumerate(objects, start=1):
        offsets.append(len(pdf))
        pdf.extend(f"{i} 0 obj\n".encode("ascii"))
        pdf.extend(obj)
        pdf.extend(b"\nendobj\n")
    xref = len(pdf)
    pdf.extend(f"xref\n0 {len(objects)+1}\n".encode("ascii"))
    pdf.extend(b"0000000000 65535 f \n")
    for offset in offsets[1:]:
        pdf.extend(f"{offset:010d} 00000 n \n".encode("ascii"))
    pdf.extend(
        f"trailer\n<< /Size {len(objects)+1} /Root 1 0 R >>\nstartxref\n{xref}\n%%EOF\n".encode("ascii")
    )
    PDF_OUT.write_bytes(pdf)


def write_summary(per_problem_rows: list[dict[str, str]], hourly_rows: list[dict[str, str]]) -> None:
    m2f_success = [r for r in per_problem_rows if r["m2f_strict_isolated_8h_success"] == "yes"]
    ari_success = [r for r in per_problem_rows if r["aristotle_strict_isolated_8h_success"] == "yes"]
    m2f_import_removed = [r for r in per_problem_rows if r["m2f_exclusion_reason"] == "cross_problem_import"]
    m2f_history_retained = [
        r
        for r in m2f_success
        if r["m2f_tokens_used_source"] == "history_log_sum"
    ]
    lines = [
        "# Strict-Isolated-8h 时间曲线数据说明",
        "",
        "生成日期：2026-05-05",
        "",
        "## 文件",
        "",
        f"- 每题时间明细：`{PER_PROBLEM_OUT.name}`",
        f"- 1h 粒度精确曲线数据：`{HOURLY_OUT.name}`",
        f"- SVG 图：`{SVG_OUT.name}`",
        f"- PDF 图：`{PDF_OUT.name}`",
        f"- 生成脚本：`{Path(__file__).name}`",
        "",
        "## 主标准",
        "",
        "按 `推荐统计标准_20260505.md`：8 小时以内、原题、无 `exact?/sorry/sorryAx/admit`、Aristotle 去 `yes -xiu`、m2f 去跨题 import，且 m2f 不因 `history_log_sum` 扣正确性。",
        "",
        "## 主结果",
        "",
        f"- M2F：{len(m2f_success)}/200 = {pct(len(m2f_success)):.2f}%",
        f"- Aristotle：{len(ari_success)}/200 = {pct(len(ari_success)):.2f}%",
        "",
        "## 1h 粒度精确数据",
        "",
        "| 时间预算 | M2F 解出 | M2F 正确率 | Aristotle 解出 | Aristotle 正确率 |",
        "|---:|---:|---:|---:|---:|",
    ]
    for r in hourly_rows:
        lines.append(
            f"| {r['hour']}h | {r['m2f_solved']} | {r['m2f_success_rate_pct_of_200']}% | "
            f"{r['aristotle_solved']} | {r['aristotle_success_rate_pct_of_200']}% |"
        )
    lines.extend(
        [
            "",
            "## 绘图说明",
            "",
            "图使用 `log(1+x)` 伪 log 横坐标和平滑曲线连接 1h 粒度精确观测点，因此 0h 点保留在图中。M2F 使用绿色实线，Aristotle 使用橙色虚线，轴名为 `Time budget (hours, log(1+x) scale)` 和 `Cumulative success rate (%)`。",
            "",
            "建议 caption：",
            "",
            r"\\caption{Cumulative strict success rate of M2F and Aristotle under increasing time budgets. M2F solves 143/200 targets within 8 hours, while Aristotle solves 125/200.}",
            "",
            "## m2f 过滤说明",
            "",
            "8h 内 `done` 为 147 题；主标准去掉 4 个跨题 import 后为 143 题。",
            "",
            "跨题 import 被去掉的题：",
            "",
            ", ".join(r["problem"] for r in m2f_import_removed),
            "",
            "`history_log_sum` 保留在主榜中的题：",
            "",
            ", ".join(r["problem"] for r in m2f_history_retained),
            "",
        ]
    )
    SUMMARY_OUT.write_text("\n".join(lines))


def main() -> None:
    COMPARE_DIR.mkdir(parents=True, exist_ok=True)
    per_problem_rows, hourly_rows = write_csvs()
    render_svg(hourly_rows)
    render_pdf(hourly_rows)
    write_summary(per_problem_rows, hourly_rows)
    print(f"wrote {PER_PROBLEM_OUT}")
    print(f"wrote {HOURLY_OUT}")
    print(f"wrote {SVG_OUT}")
    print(f"wrote {PDF_OUT}")
    print(f"wrote {SUMMARY_OUT}")


if __name__ == "__main__":
    main()
