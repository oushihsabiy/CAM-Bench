#!/usr/bin/env python3
"""
Formalization-error analysis for M2F and Aristotle on the 200-problem set.

Unlike the strict-score reports, this script does not treat `exact?` as a
standalone category. It focuses on why failed/unfinished/statement-repair
cases did not yield a clean original Lean proof.
"""

from __future__ import annotations

import csv
import json
import re
from collections import Counter, defaultdict
from pathlib import Path


ROOT = Path("/root/workspace/benchmark/JSON2LEAN")
OUT_DIR = ROOT / "记录"
M2F_CSV = ROOT / "lean/m2f/final99_run_summary_20260504T131426Z/per_problem_summary.csv"
M2F_PROBLEMS = ROOT / "lean/m2f/problems"
ARISTOTLE_MD = ROOT / "记录/精确记录.md"

REPORT = OUT_DIR / "m2f_aristotle形式化错误分析_20260505.md"
DETAIL_CSV = OUT_DIR / "m2f_aristotle_formal_error_records_20260505.csv"

CATEGORIES = [
    "Mathlib/API hallucination",
    "Lean proficiency/type-system",
    "Missing formal infrastructure",
    "General capability/unfinished",
    "Misalignment/statement issue",
]

ADVANCED_KEYWORDS = re.compile(
    r"(?i)\b("
    r"farkas|duality|dual|kkt|karush|separation|separating|hyperplane|"
    r"spectral|eigen|eigenvalue|eigenvector|hadamard|cauchy|fischer|"
    r"pre?kopa|leindler|logconcave|log-concave|log_concave|logdet|log_det|determinant|"
    r"hessian|gradient|subgradient|convex|concave|fenchel|legendre|"
    r"measurable|integrable|measure|probability|gaussian|normal|"
    r"matrix|positive definite|posdef|semidefinite|psd|cone|interior|"
    r"compact|closed|continuous|differentiable|deriv|fderiv|tendsto|"
    r"optimal|optimization|program|barrier|likelihood|newton|bfgs|sr1"
    r")\b"
)

MISSING_INFRA_TEXT = re.compile(
    r"(?i)("
    r"not available in Mathlib|not currently available in Mathlib|not available|"
    r"requires .* Mathlib|requires.*infrastructure|deep result|fundamental result|"
    r"would require|substantial formalization|not in Mathlib|missing.*Mathlib|"
    r"neither .* available|standard proofs require"
    r")"
)

API_TEXT = re.compile(
    r"(?i)("
    r"unknown constant|unknown identifier|invalid field|field .* not found|"
    r"monotoneOn_gradient|gradient_monotone|strong_duality|farkas|KKT|"
    r"separating_hyperplane|spectral_theorem|Matrix\.[A-Za-z0-9_]*_"
    r")"
)

LEAN_TYPE_TEXT = re.compile(
    r"(?i)("
    r"type mismatch|application type mismatch|failed to synthesize|unsolved goals|"
    r"compile|编译|tactic|linarith|nlinarith|simp|rewrite|rw|ring|"
    r"syntax|parser|no goals|dependent elimination"
    r")"
)

TACTIC_OR_TYPE_CODE = re.compile(
    r"\b("
    r"simp|simpa|rw|rewrite|linarith|nlinarith|ring|ring_nf|omega|aesop|"
    r"positivity|norm_num|field_simp|exact|apply|refine|constructor|rcases|"
    r"funext|ext|calc|have|show|convert|congr|subst"
    r")\b"
)

MISALIGNMENT_TEXT = re.compile(
    r"(?i)("
    r"bad_statement|题目有错|待修改|false as written|mathematically false|"
    r"target theorem is false|statement is false|theorem is false|claim is false|"
    r"修题|xiu|修改题|改题|not equal to original|changed statement|"
    r"counterexample|not derivable|cannot inhabit|no proof term"
    r")"
)

def strip_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
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
                depth = 1
                out.extend("  ")
                i += 2
            else:
                out.append(text[i])
                i += 1
    return "".join(out)


def placeholder_counts(code: str) -> Counter:
    return Counter(
        {
            "sorry": len(re.findall(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])", code)),
            "sorryAx": len(re.findall(r"(?<![A-Za-z0-9_])sorryAx(?![A-Za-z0-9_])", code)),
            "admit": len(re.findall(r"(?<![A-Za-z0-9_])admit(?![A-Za-z0-9_])", code)),
            "exact?": len(re.findall(r"(?<![A-Za-z0-9_])exact\?(?![A-Za-z0-9_])", code)),
        }
    )


def problem_num(name: str) -> int:
    m = re.search(r"\d+", name)
    if not m:
        raise ValueError(name)
    return int(m.group())


def classify_text_and_code(text: str, code: str, base_reason: str = "") -> tuple[list[str], list[str]]:
    labels: set[str] = set()
    evidence: list[str] = []
    combined = f"{base_reason}\n{text}"
    placeholders = placeholder_counts(code)

    if placeholders["sorry"] or placeholders["sorryAx"] or placeholders["admit"]:
        labels.add("General capability/unfinished")
        evidence.append(
            "active placeholders: "
            + ", ".join(f"{k}={v}" for k, v in placeholders.items() if v and k != "exact?")
        )
    if re.search(r"(?i)(remaining_sorry|remaining_sorryAx|有sorry|全是sorry|sorry remains|unable to fully eliminate|partial|not completed|unfinished|failed|limit_exceeded|llm_error)", combined):
        labels.add("General capability/unfinished")
        evidence.append("feedback indicates unfinished proof / remaining sorry / failed run")
    if MISALIGNMENT_TEXT.search(combined):
        labels.add("Misalignment/statement issue")
        evidence.append("feedback indicates statement repair, false statement, or counterexample")
    if MISSING_INFRA_TEXT.search(combined) or ADVANCED_KEYWORDS.search(combined[:8000]):
        labels.add("Missing formal infrastructure")
        evidence.append("advanced optimization/analysis concept or explicit missing-infrastructure feedback")
    if API_TEXT.search(combined) or API_TEXT.search(code):
        labels.add("Mathlib/API hallucination")
        evidence.append("unknown/invalid/high-level API signal")
    if LEAN_TYPE_TEXT.search(combined) or (TACTIC_OR_TYPE_CODE.search(code) and not sum(placeholders.values())):
        labels.add("Lean proficiency/type-system")
        evidence.append("compile/type/tactic signal or non-placeholder tactic-heavy attempt")

    if not labels:
        labels.add("General capability/unfinished")
        evidence.append("failed/filtered case without more specific signal")
    return sorted(labels), evidence[:5]


def parse_aristotle_records() -> dict[int, dict[str, str]]:
    text = ARISTOTLE_MD.read_text(errors="ignore")
    records: dict[int, dict[str, str]] = {}
    block_pattern = re.compile(
        r'<a id="problem-(\d+)"></a>(.*?)(?=<a id="problem-\d+"></a>|<a id="exact-list"></a>)',
        re.S,
    )
    for m in block_pattern.finditer(text):
        n = int(m.group(1))
        block = m.group(2)
        time_match = re.search(r"用时：([^\n]+)", block)
        mark_match = re.search(r"人工标记[：:]\s*([^\n]+)", block)
        summary_match = re.search(r'"output_summary":\s*"(.*?)",\n\s*"has_input_files"', block, re.S)
        output_summary = ""
        if summary_match:
            raw = '"' + summary_match.group(1) + '"'
            try:
                output_summary = json.loads(raw)
            except Exception:
                output_summary = summary_match.group(1)
        records[n] = {
            "time": time_match.group(1).strip() if time_match else "",
            "mark": mark_match.group(1).strip() if mark_match else "",
            "block": block,
            "output_summary": output_summary,
        }
    return records


def collect_m2f() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    with M2F_CSV.open(newline="") as f:
        for row in csv.DictReader(f):
            n = problem_num(row["problem"])
            if row["reason_group"] == "done":
                continue
            lean_path = M2F_PROBLEMS / f"problem-{n}.lean"
            text = lean_path.read_text(errors="ignore") if lean_path.exists() else ""
            code = strip_comments(text)
            base_reason = f"{row['reason_group']} {row.get('failure_reason','')}"
            labels, evidence = classify_text_and_code(text, code, base_reason)
            ph = placeholder_counts(code)
            rows.append(
                {
                    "agent": "m2f",
                    "problem": str(n),
                    "status_or_mark": row["reason_group"],
                    "source": str(lean_path),
                    "active_sorry": str(ph["sorry"]),
                    "active_sorryAx": str(ph["sorryAx"]),
                    "active_admit": str(ph["admit"]),
                    "active_exact?": str(ph["exact?"]),
                    "labels": "; ".join(labels),
                    "evidence": " | ".join(evidence),
                    "feedback_excerpt": row.get("failure_reason", "")[:600],
                }
            )
    return rows


def collect_aristotle() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    records = parse_aristotle_records()
    for n, rec in sorted(records.items()):
        mark = rec["mark"].lower()
        # Do not analyze yes-exact? as a formal-error category here, per request.
        # Include no/failed/compile/sorry and statement-repair xiu cases.
        include = (
            mark.startswith("no")
            or "xiu" in mark
            or "编译" in mark
            or "failed" in mark
            or "有sorry" in mark
            or "全是sorry" in mark
        )
        if not include:
            continue
        combined = rec["mark"] + "\n" + rec["output_summary"] + "\n" + rec["block"]
        labels, evidence = classify_text_and_code(combined, "", rec["mark"])
        rows.append(
            {
                "agent": "aristotle",
                "problem": str(n),
                "status_or_mark": rec["mark"],
                "source": str(ARISTOTLE_MD),
                "active_sorry": "",
                "active_sorryAx": "",
                "active_admit": "",
                "active_exact?": "",
                "labels": "; ".join(labels),
                "evidence": " | ".join(evidence),
                "feedback_excerpt": rec["output_summary"][:600].replace("\n", " "),
            }
        )
    return rows


def count_labels(rows: list[dict[str, str]]) -> dict[str, Counter]:
    counts: dict[str, Counter] = defaultdict(Counter)
    for row in rows:
        for label in row["labels"].split("; "):
            if label:
                counts[row["agent"]][label] += 1
    return counts


def markdown_table(headers: list[str], rows: list[list[str]]) -> str:
    lines = ["| " + " | ".join(headers) + " |", "| " + " | ".join("---" for _ in headers) + " |"]
    lines.extend("| " + " | ".join(row) + " |" for row in rows)
    return "\n".join(lines)


def examples(rows: list[dict[str, str]]) -> dict[str, dict[str, dict[str, str]]]:
    out: dict[str, dict[str, dict[str, str]]] = defaultdict(dict)
    used: dict[str, set[str]] = defaultdict(set)

    def score(row: dict[str, str], label: str) -> tuple[int, int, int]:
        labels = row["labels"].split("; ")
        status = row["status_or_mark"].lower()
        priority = 5
        if label == "Misalignment/statement issue" and ("bad_statement" in status or "xiu" in status):
            priority = 0
        elif label == "General capability/unfinished" and ("sorry" in status or "unfinished" in status or "failed" in status):
            priority = 0
        elif label == "Lean proficiency/type-system" and ("编译" in status or "compile" in row["evidence"]):
            priority = 0
        elif label == "Mathlib/API hallucination" and ("unknown" in row["evidence"] or "api" in row["evidence"].lower()):
            priority = 0
        elif label == "Missing formal infrastructure" and ("infrastructure" in row["evidence"]):
            priority = 0
        reuse_penalty = 2 if row["problem"] in used[row["agent"]] else 0
        return (priority + reuse_penalty, len(labels), int(row["problem"]))

    for agent in ["m2f", "aristotle"]:
        agent_rows = [r for r in rows if r["agent"] == agent]
        for label in CATEGORIES:
            candidates = [r for r in agent_rows if label in r["labels"].split("; ")]
            if not candidates:
                continue
            row = sorted(candidates, key=lambda r: score(r, label))[0]
            out[agent][label] = row
            used[agent].add(row["problem"])
    return out


def category_problem_lists(rows: list[dict[str, str]]) -> list[list[str]]:
    out = []
    for agent in ["m2f", "aristotle"]:
        agent_rows = [r for r in rows if r["agent"] == agent]
        for cat in CATEGORIES:
            nums = sorted(int(r["problem"]) for r in agent_rows if cat in r["labels"].split("; "))
            out.append([agent, cat, ", ".join(map(str, nums)) if nums else "-"])
    return out


def write_outputs(rows: list[dict[str, str]]) -> None:
    with DETAIL_CSV.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    by_agent: dict[str, list[dict[str, str]]] = defaultdict(list)
    for row in rows:
        by_agent[row["agent"]].append(row)
    label_counts = count_labels(rows)

    scale_rows = []
    for agent in ["m2f", "aristotle"]:
        rs = by_agent[agent]
        scale_rows.append([agent, str(len(rs)), ", ".join(f"{k}: {v}" for k, v in Counter(r["status_or_mark"] for r in rs).most_common())])

    label_rows = []
    for agent in ["m2f", "aristotle"]:
        denom = len(by_agent[agent])
        row = [agent, str(denom)]
        for cat in CATEGORIES:
            row.append(f"{label_counts[agent][cat]}/{denom}")
        label_rows.append(row)
    category_rows = category_problem_lists(rows)

    ex = examples(rows)
    lines = [
        "# M2F / Aristotle 形式化错误分类分析",
        "",
        "生成日期：2026-05-05",
        "",
        "## 口径",
        "",
        "本报告沿用 pass@32 的形式化错误类别，但对象换成 M2F 和 Aristotle 在同一批 200 题上的失败/修题案例。这里不把 `exact?` 单独作为错误类别；`yes-exact?` 题不纳入本报告的主要失败原因统计。重点是：为什么没有得到一个干净的原题 Lean 证明。",
        "",
        "- M2F：统计 `per_problem_summary.csv` 中 `reason_group != done` 的 27 题，并读取对应 `lean/m2f/problems/problem-N.lean` 最终文件。",
        "- Aristotle：统计人工记录中 `no`、`no -编译有错`、`no -有sorry`、`no -failed`、`yes -xiu` 等非干净原题证明案例；不把 `yes-exact?` 作为本报告重点。",
        "",
        "错误类别是多标签，因此各列不会相加为 100%。",
        "",
        "其中 `Missing formal infrastructure` 是宽口径：它表示失败发生在凸分析、谱理论、对偶性、测度积分、KKT/分离定理等高层数学对象上，通常需要中间层 Mathlib 桥接定理；不等价于 Lean 明确报出“库中不存在某个定理”。",
        "",
        "## 数据规模",
        "",
        markdown_table(["agent", "cases", "status / mark distribution"], scale_rows),
        "",
        "## 形式化错误分类统计",
        "",
        markdown_table(["agent", "denom"] + CATEGORIES, label_rows),
        "",
        "## 按类别题号明细",
        "",
        markdown_table(["agent", "category", "problem ids"], category_rows),
        "",
        "## 类别解释",
        "",
        "1. **Mathlib/API hallucination**：调用不存在或不匹配的 theorem/field/API，或反馈显示模型需要一个高层 Mathlib lemma 但实际没有可用接口。",
        "2. **Lean proficiency/type-system**：编译错误、类型不匹配、tactic/rewrite/simp/linarith 失败、typeclass synthesis 失败等。",
        "3. **Missing formal infrastructure**：题目依赖凸分析、矩阵谱理论、测度概率、对偶性、KKT、分离定理等中间层数学基础设施；数学方向清楚但 Mathlib 缺少现成桥接定理。",
        "4. **General capability/unfinished**：仍有 `sorry/sorryAx/admit`、没有完成计划、运行失败或最后保留占位证明。",
        "5. **Misalignment/statement issue**：题面/形式化 statement 可能有问题，或者需要 `xiu` 修题/改 statement 才能完成。",
        "",
        "## 代表性例子",
        "",
    ]

    for agent in ["m2f", "aristotle"]:
        lines.append(f"### {agent}")
        for cat in CATEGORIES:
            row = ex[agent].get(cat)
            if not row:
                continue
            lines.append(
                f"- **{cat}**：problem {row['problem']}；status=`{row['status_or_mark']}`；"
                f"evidence={row['evidence']}；source=`{row['source']}`；"
                f"feedback={row['feedback_excerpt'][:240]}"
            )
        lines.append("")

    lines.extend(
        [
            "## 结合 M2F 与 Aristotle 反馈的观察",
            "",
            "### M2F",
            "",
            "- M2F 的失败高度集中在两类：`bad_statement_*` 与 `remaining_sorry/sorryAx`。前者说明一部分题的形式化 statement 或可证明性需要额外审计；后者说明系统能推进证明但停在关键中间引理。",
            "- `success_but_remaining_sorry` 一类通常不是语法层面的小错，而是缺少深层桥接结果，例如谱理论、矩阵不等式、测度积分、Prékopa-Leindler、Farkas/duality 等。",
            "- M2F 的 `bad_statement_long_tail/from_history` 与 Aristotle 的 `yes -xiu` 是同一个现象的两种表现：benchmark 不只测 theorem proving，也测 statement 是否忠实、是否可证明、是否需要修题。",
            "",
            "### Aristotle",
            "",
            "- Aristotle 的失败记录里 `no -有sorry`、`no -全是sorry` 多数明确指出“已经证明部分 helper，但关键深层定理缺失”。这更接近 Missing formal infrastructure，而不是简单的模型没理解题意。",
            "- `no -编译有错` 反映 Lean proficiency/type-system 问题：证明草稿可能数学上接近，但没有通过 Lean 的类型、rewrite、simp、linarith、typeclass 等检查。",
            "- `yes -xiu` 不应算原题成功，但它对 benchmark 有价值：它暴露了题面或形式化 statement 的边界问题，可作为 statement-audit 子任务。",
            "",
            "## 和 pass@32 的关系",
            "",
            "pass@32 的主要错误是 `库基础设施缺口 + API 幻觉 + Lean 类型系统细节` 的组合；M2F/Aristotle 的人工与汇总反馈也支持这个结论。不同之处是：M2F/Aristotle 的记录更能暴露 statement 层面的错误，例如 `bad_statement` 与 `xiu`；pass@32 的最后快照更能暴露具体 Lean 报错类型。",
            "",
            "## 结论",
            "",
            "在这 200 题上，失败原因不宜简单归因于模型能力不足。更准确的说法是：当前系统在高层优化数学 formalization 中，经常缺少可直接调用的 Mathlib 中间层定理；模型随后会出现 API 幻觉、类型系统/tactic 失败，或保留 `sorry`。这说明 benchmark 的价值在于同时检验 proof search、Mathlib 检索/API 对齐、statement audit 和高层数学库建设需求。",
            "",
            "## 产物",
            "",
            f"- 明细 CSV：`{DETAIL_CSV.name}`",
            f"- 分析脚本：`{Path(__file__).name}`",
            "",
        ]
    )
    REPORT.write_text("\n".join(lines))


def main() -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    rows = collect_m2f() + collect_aristotle()
    write_outputs(rows)
    print(f"records: {len(rows)}")
    print(f"wrote {DETAIL_CSV}")
    print(f"wrote {REPORT}")


if __name__ == "__main__":
    main()
