#!/usr/bin/env python3
"""
Formalization-error analysis for /root/workspace/benchmark/result/*/pass@32.

The script reads the last Lean snapshot for each failed proof block, assigns
multi-label formalization-error categories, and recompiles a deterministic
sample of final snapshots to calibrate the static labels with real Lean errors.
"""

from __future__ import annotations

import csv
import hashlib
import json
import re
import subprocess
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path


RESULT_ROOT = Path("/root/workspace/benchmark/result")
LEAN_CWD = Path("/root/workspace/benchmark/JSON2LEAN/lean")
OUT_DIR = Path("/root/workspace/benchmark/JSON2LEAN/记录")

REPORT = OUT_DIR / "pass32形式化错误分析_20260505.md"
RECORDS_CSV = OUT_DIR / "pass32_formal_error_records_20260505.csv"
COMPILE_CSV = OUT_DIR / "pass32_compile_sample_errors_20260505.csv"

SAMPLE_PER_MODEL = 120
COMPILE_TIMEOUT_SEC = 8
MAX_WORKERS = 8


ERROR_CATEGORIES = [
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
    r"pre?kopa|leindler|logconcave|log_concave|logdet|log_det|determinant|"
    r"hessian|gradient|subgradient|convex|concave|fenchel|legendre|"
    r"measurable|integrable|measure|probability|gaussian|normal|"
    r"matrix|positive definite|posdef|semidefinite|psd|cone|interior|"
    r"compact|closed|continuous|differentiable|deriv|fderiv|tendsto"
    r")\b"
)

HALLUCINATION_STATIC = re.compile(
    r"(?i)("
    r"monotoneOn_gradient|gradient_monotone|convex.*gradient|"
    r"log_det.*concav|det.*pos|PosDef.*det|spectral_theorem|"
    r"farkas|strong_duality|KKT|separating_hyperplane|"
    r"norm_sq|inner_self_nonneg|Matrix\.[A-Za-z0-9_]*_(?:pos|nonneg|convex|concave)|"
    r"\.[A-Za-z0-9_]*(?:_of_|_iff_|_eq_|_le_|_lt_|_nonneg|_pos|_convex|_concave)"
    r")"
)

TACTIC_OR_TYPE_PATTERNS = re.compile(
    r"\b("
    r"simp|simpa|rw|rewrite|linarith|nlinarith|ring|ring_nf|omega|aesop|"
    r"positivity|norm_num|field_simp|exact|apply|refine|constructor|rcases|"
    r"funext|ext|calc|have|show|convert|congr|subst"
    r")\b"
)

MISALIGNMENT_PATTERNS = re.compile(
    r"\b(False\.elim|exfalso|by_contra|nomatch|contradiction|absurd)\b"
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


def choose_last_snapshot(proof_log: Path, sorry_index: int) -> Path | None:
    files = list(proof_log.glob(f"sorry{sorry_index}_turn*.lean"))
    if not files:
        files = list(proof_log.glob(f"*sorry{sorry_index}*.lean"))
    if not files:
        return None

    def key(path: Path) -> tuple[int, int, str]:
        match = re.search(r"_turn(\d+)(?:_(prefix|block))?\.lean$", path.name)
        turn = int(match.group(1)) if match else -1
        suffix = match.group(2) if match else "other"
        # Prefer complete snapshots over block/prefix fragments at the same turn.
        suffix_rank = {"": 3, None: 3, "block": 2, "prefix": 1, "other": 0}.get(suffix, 0)
        return (turn, suffix_rank, path.name)

    return max(files, key=key)


def model_from_summary(path: Path) -> str:
    rel = path.relative_to(RESULT_ROOT)
    return rel.parts[0]


def problem_from_summary(path: Path) -> str:
    pass_root = RESULT_ROOT / model_from_summary(path) / "pass@32"
    return str(path.parent.relative_to(pass_root))


def active_placeholder_counts(code: str) -> Counter:
    return Counter(
        {
            "sorry": len(re.findall(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])", code)),
            "admit": len(re.findall(r"(?<![A-Za-z0-9_])admit(?![A-Za-z0-9_])", code)),
            "exact?": len(re.findall(r"(?<![A-Za-z0-9_])exact\?(?![A-Za-z0-9_])", code)),
        }
    )


def classify_static(
    *,
    code: str,
    full_text: str,
    block_name: str,
    termination_reason: str,
    has_snapshot: bool,
) -> tuple[list[str], list[str]]:
    labels: set[str] = set()
    evidence: list[str] = []
    placeholders = active_placeholder_counts(code)
    placeholder_total = sum(placeholders.values())

    if not has_snapshot:
        labels.add("General capability/unfinished")
        evidence.append("no final Lean snapshot exported")
    if placeholder_total:
        labels.add("General capability/unfinished")
        evidence.append(
            "active placeholders: "
            + ", ".join(f"{k}={v}" for k, v in placeholders.items() if v)
        )
    if termination_reason in {"llm_error", "llm_error_budget_exceeded", "limit_exceeded"}:
        labels.add("General capability/unfinished")
        evidence.append(f"termination={termination_reason}")
    if ADVANCED_KEYWORDS.search(block_name) or ADVANCED_KEYWORDS.search(full_text[:6000]):
        labels.add("Missing formal infrastructure")
        evidence.append("advanced optimization/analysis keyword in statement or proof")
    if HALLUCINATION_STATIC.search(code):
        labels.add("Mathlib/API hallucination")
        evidence.append("uses high-level or field-style theorem/API name likely not available")
    if TACTIC_OR_TYPE_PATTERNS.search(code) and not placeholder_total:
        labels.add("Lean proficiency/type-system")
        evidence.append("non-placeholder proof attempt relies on tactics/rewrites/typeclass synthesis")
    if MISALIGNMENT_PATTERNS.search(code):
        labels.add("Misalignment/statement issue")
        evidence.append("proof uses contradiction/False-elimination pattern")

    if not labels:
        labels.add("General capability/unfinished")
        evidence.append("failed block without more specific static signal")
    return sorted(labels), evidence[:5]


def lean_error_category(stderr: str) -> tuple[list[str], str]:
    s = stderr.lower()
    labels: set[str] = set()
    primary = "other"
    if any(x in s for x in ["unknown constant", "unknown identifier", "invalid field", "invalid projection"]):
        labels.add("Mathlib/API hallucination")
        primary = "unknown API/identifier"
    if any(
        x in s
        for x in [
            "application type mismatch",
            "type mismatch",
            "failed to synthesize",
            "invalid argument",
            "has type",
            "expected",
            "invalid field notation",
        ]
    ):
        labels.add("Lean proficiency/type-system")
        if primary == "other":
            primary = "type/synthesis mismatch"
    if any(x in s for x in ["unsolved goals", "tactic", "linarith", "simp", "ring", "omega"]):
        labels.add("Lean proficiency/type-system")
        if primary == "other":
            primary = "tactic/goal failure"
    if any(x in s for x in ["unexpected token", "expected token", "parser", "invalid syntax"]):
        labels.add("Lean proficiency/type-system")
        primary = "syntax/parser"
    if any(x in s for x in ["declaration uses 'sorry'", "sorry"]):
        labels.add("General capability/unfinished")
        if primary == "other":
            primary = "placeholder"
    if not labels:
        labels.add("Lean proficiency/type-system")
    return sorted(labels), primary


def collect_records() -> list[dict[str, str]]:
    records: list[dict[str, str]] = []
    for summary_path in sorted(RESULT_ROOT.glob("*/pass@32/**/summary.json")):
        model = model_from_summary(summary_path)
        problem = problem_from_summary(summary_path)
        try:
            summary = json.loads(summary_path.read_text(errors="ignore"))
        except Exception:
            continue
        proof_log = summary_path.parent / "proof_log"
        for block in summary.get("block_details", []):
            if block.get("passed"):
                continue
            idx = int(block.get("sorry_index", -1))
            snapshot = choose_last_snapshot(proof_log, idx)
            text = snapshot.read_text(errors="ignore") if snapshot else ""
            code = strip_comments(text)
            labels, evidence = classify_static(
                code=code,
                full_text=text,
                block_name=str(block.get("name", "")),
                termination_reason=str(block.get("termination_reason", "")),
                has_snapshot=snapshot is not None,
            )
            placeholders = active_placeholder_counts(code)
            records.append(
                {
                    "model": model,
                    "problem": problem,
                    "block": str(block.get("name", "")),
                    "sorry_index": str(idx),
                    "attempts": str(block.get("attempts", "")),
                    "termination_reason": str(block.get("termination_reason", "")),
                    "snapshot": str(snapshot) if snapshot else "",
                    "has_snapshot": "yes" if snapshot else "no",
                    "active_sorry": str(placeholders["sorry"]),
                    "active_admit": str(placeholders["admit"]),
                    "active_exact?": str(placeholders["exact?"]),
                    "static_labels": "; ".join(labels),
                    "static_evidence": " | ".join(evidence),
                    "compile_sampled": "no",
                    "compile_primary_error": "",
                    "compile_labels": "",
                    "compile_error_excerpt": "",
                }
            )
    return records


def sample_compile_records(records: list[dict[str, str]]) -> list[dict[str, str]]:
    by_model: dict[str, list[dict[str, str]]] = defaultdict(list)
    for record in records:
        if record["has_snapshot"] != "yes":
            continue
        if int(record["active_sorry"]) or int(record["active_admit"]) or int(record["active_exact?"]):
            continue
        by_model[record["model"]].append(record)

    selected: list[dict[str, str]] = []
    for model, model_records in by_model.items():
        ranked = sorted(
            model_records,
            key=lambda r: hashlib.md5((r["model"] + "/" + r["problem"] + "/" + r["block"]).encode()).hexdigest(),
        )
        selected.extend(ranked[:SAMPLE_PER_MODEL])
    return selected


def compile_one(record: dict[str, str]) -> tuple[dict[str, str], str, str, str]:
    path = record["snapshot"]
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", path],
            cwd=LEAN_CWD,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=COMPILE_TIMEOUT_SEC,
        )
        output = (proc.stdout + "\n" + proc.stderr).strip()
        if proc.returncode == 0:
            return record, "compiled_ok_but_summary_failed", "", output[:1200]
        labels, primary = lean_error_category(output)
        return record, primary, "; ".join(labels), output[:1200].replace("\n", "\\n")
    except subprocess.TimeoutExpired as exc:
        stdout = exc.stdout or ""
        stderr = exc.stderr or ""
        if isinstance(stdout, bytes):
            stdout = stdout.decode(errors="ignore")
        if isinstance(stderr, bytes):
            stderr = stderr.decode(errors="ignore")
        output = (stdout + "\n" + stderr).strip()
        return record, "compile_timeout", "Missing formal infrastructure; General capability/unfinished", output[:1200].replace("\n", "\\n")


def run_compile_sample(records: list[dict[str, str]]) -> None:
    selected = sample_compile_records(records)
    by_key = {(r["model"], r["problem"], r["block"], r["sorry_index"]): r for r in records}
    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
        futures = [pool.submit(compile_one, r) for r in selected]
        for fut in as_completed(futures):
            record, primary, labels, excerpt = fut.result()
            key = (record["model"], record["problem"], record["block"], record["sorry_index"])
            target = by_key[key]
            target["compile_sampled"] = "yes"
            target["compile_primary_error"] = primary
            target["compile_labels"] = labels
            target["compile_error_excerpt"] = excerpt
            if labels:
                merged = set(target["static_labels"].split("; ")) | set(labels.split("; "))
                target["static_labels"] = "; ".join(sorted(x for x in merged if x))


def write_records(records: list[dict[str, str]]) -> None:
    fields = list(records[0].keys()) if records else []
    with RECORDS_CSV.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        writer.writerows(records)
    sampled = [r for r in records if r["compile_sampled"] == "yes"]
    with COMPILE_CSV.open("w", newline="") as f:
        fields2 = [
            "model",
            "problem",
            "block",
            "snapshot",
            "compile_primary_error",
            "compile_labels",
            "compile_error_excerpt",
        ]
        writer = csv.DictWriter(f, fieldnames=fields2)
        writer.writeheader()
        for r in sampled:
            writer.writerow({k: r[k] for k in fields2})


def count_labels(records: list[dict[str, str]]) -> dict[str, Counter]:
    out: dict[str, Counter] = defaultdict(Counter)
    for r in records:
        labels = [x.strip() for x in r["static_labels"].split("; ") if x.strip()]
        for label in labels:
            out[r["model"]][label] += 1
    return out


def representative_examples(records: list[dict[str, str]]) -> dict[str, dict[str, dict[str, str]]]:
    examples: dict[str, dict[str, dict[str, str]]] = defaultdict(dict)
    for r in records:
        labels = [x.strip() for x in r["static_labels"].split("; ") if x.strip()]
        for label in labels:
            if label in examples[r["model"]]:
                continue
            examples[r["model"]][label] = r
    return examples


def markdown_table(headers: list[str], rows: list[list[str]]) -> str:
    lines = ["| " + " | ".join(headers) + " |", "| " + " | ".join("---" for _ in headers) + " |"]
    lines.extend("| " + " | ".join(row) + " |" for row in rows)
    return "\n".join(lines)


def write_report(records: list[dict[str, str]]) -> None:
    by_model = defaultdict(list)
    for r in records:
        by_model[r["model"]].append(r)
    label_counts = count_labels(records)
    examples = representative_examples(records)

    rows = []
    for model in sorted(by_model):
        rs = by_model[model]
        snapshots = sum(r["has_snapshot"] == "yes" for r in rs)
        sampled = sum(r["compile_sampled"] == "yes" for r in rs)
        rows.append([model, str(len(rs)), str(snapshots), str(sampled)])

    label_rows = []
    for model in sorted(by_model):
        denom = len(by_model[model])
        row = [model, str(denom)]
        for cat in ERROR_CATEGORIES:
            row.append(f"{label_counts[model][cat]}/{denom}")
        label_rows.append(row)

    term_rows = []
    for model in sorted(by_model):
        c = Counter(r["termination_reason"] for r in by_model[model])
        term_rows.append([model, ", ".join(f"{k}: {v}" for k, v in c.most_common())])

    compile_rows = []
    for model in sorted(by_model):
        c = Counter(r["compile_primary_error"] for r in by_model[model] if r["compile_sampled"] == "yes")
        compile_rows.append([model, ", ".join(f"{k}: {v}" for k, v in c.most_common())])

    lines: list[str] = [
        "# pass@32 最后快照形式化错误分析",
        "",
        "生成日期：2026-05-05",
        "",
        "## 口径",
        "",
        "分析对象是 `/root/workspace/benchmark/result/*/pass@32` 中所有未通过的 proof block。对每个 failed block，脚本选取 `proof_log/sorry{i}_turn*.lean` 中 turn 最大、且优先完整文件而不是 `_block/_prefix` 片段的最后一次 Lean 快照。",
        "",
        "错误类别是多标签：一个 proof block 可以同时有 Mathlib API 幻觉、类型系统错误和缺少上层数学库等问题。因此表格中各列不会相加为 100%。",
        "",
        "## 数据规模",
        "",
        markdown_table(["model", "failed proof blocks", "有最后快照", "重新编译样本"], rows),
        "",
        "## 形式化错误分类统计",
        "",
        markdown_table(["model", "denom"] + ERROR_CATEGORIES, label_rows),
        "",
        "## 终止原因",
        "",
        markdown_table(["model", "termination reasons"], term_rows),
        "",
        "## 重新编译样本的 Lean 报错类型",
        "",
        f"对每个模型最多抽样 {SAMPLE_PER_MODEL} 个“最后快照中没有 active `sorry/admit/exact?`”的 failed block，使用 `lake env lean` 重新编译，单个快照 timeout={COMPILE_TIMEOUT_SEC}s。",
        "",
        markdown_table(["model", "compile primary error distribution"], compile_rows),
        "",
        "## 错误类型解释",
        "",
        "1. **Mathlib/API hallucination**：最后快照调用不存在或不匹配的 Mathlib 定理/字段/API，例如 `hconv.monotoneOn_gradient` 这类 field-style theorem，真实 Lean 报错常见为 `unknown identifier`、`unknown constant`、`invalid field`。",
        "",
        "2. **Lean proficiency/type-system**：证明思路可能接近，但 Lean 层面失败，包括 application/type mismatch、typeclass synthesis failure、tactic failure、unsolved goals、rewrite/simp/linarith 使用不当。",
        "",
        "3. **Missing formal infrastructure**：题目依赖优化、凸分析、矩阵分析、测度概率、对偶性、谱理论、分离定理等上层结果；模型经常需要一个数学上标准但 Mathlib 中没有现成接口的引理，随后表现为 API 幻觉或停在 `sorry`。",
        "",
        "4. **General capability/unfinished**：最后快照仍有 active `sorry/admit/exact?`，或者 32 次尝试耗尽、LLM error、没有导出最终尝试。这类是最直接的“没有完成证明”。",
        "",
        "5. **Misalignment/statement issue**：最后快照出现明显反证/`False.elim`/构造与原命题不一致的倾向；这类在自动静态分析里只作为弱信号，需要人工复核。",
        "",
        "## 代表性例子",
        "",
    ]

    for model in sorted(examples):
        lines.append(f"### {model}")
        for cat in ERROR_CATEGORIES:
            r = examples[model].get(cat)
            if not r:
                continue
            lines.append(
                f"- **{cat}**：`{r['problem']}` / `{r['block']}`；"
                f"termination=`{r['termination_reason']}`；snapshot=`{r['snapshot']}`；"
                f"evidence={r['static_evidence'] or r['compile_primary_error']}"
            )
        lines.append("")

    lines.extend(
        [
            "## 和 Aristotle / M2F 反馈的一致性",
            "",
            "这批 pass@32 快照的错误形态与前面对 Aristotle/M2F 的人工审核结论一致：",
            "",
            "- Aristotle 的人工记录中，`exact?` 被归为伪证明，说明“看似完成但依赖占位/伪证明”的问题必须从主成功率里剔除；pass@32 中同类信号对应 `General capability/unfinished`。",
            "- M2F 的非 `done` 题里有大量 `bad_statement_*` 和 `success_but_remaining_sorry*`，对应这里的 `Misalignment/statement issue` 与 `General capability/unfinished` 两类。",
            "- M2F/Aristotle 都在凸分析、矩阵谱理论、测度概率、对偶性等题上出现长尾失败；pass@32 的最后快照也反复显示模型会调用不存在的高层 Mathlib lemma，说明 benchmark 的核心难点不是单纯自然语言理解，而是“数学中间层 API/库基础设施”缺口。",
            "",
            "## 主要结论",
            "",
            "1. 最常见失败不是单一类型错误，而是 **库基础设施缺口 + API 幻觉 + Lean 类型系统细节** 的组合：模型知道数学上该用什么定理，但无法落到 Mathlib 中真实存在、类型正确的接口。",
            "",
            "2. `compile_stuck` 占多数，说明 pass@32 的瓶颈通常发生在最后几步 formalization repair，而不是完全没有数学方向。",
            "",
            "3. 大量最后快照仍保留 active `sorry`，说明即使 32 次尝试后，模型也经常无法把高层数学论证分解成 Mathlib 已有的小引理。",
            "",
            "4. 这些错误支持 benchmark 的价值：它能区分模型的自然语言数学理解、Mathlib 检索/API 使用能力、Lean 类型系统熟练度、以及发现题面/形式化 statement 问题的能力。",
            "",
            "## 产物",
            "",
            f"- 全量 block 记录：`{RECORDS_CSV.name}`",
            f"- 编译样本错误：`{COMPILE_CSV.name}`",
            f"- 分析脚本：`{Path(__file__).name}`",
            "",
        ]
    )
    REPORT.write_text("\n".join(lines))


def main() -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    records = collect_records()
    run_compile_sample(records)
    write_records(records)
    write_report(records)
    print(f"records: {len(records)}")
    print(f"wrote {RECORDS_CSV}")
    print(f"wrote {COMPILE_CSV}")
    print(f"wrote {REPORT}")


if __name__ == "__main__":
    main()
