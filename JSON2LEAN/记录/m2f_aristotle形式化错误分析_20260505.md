# M2F / Aristotle 形式化错误分类分析

生成日期：2026-05-05

## 口径

本报告沿用 pass@32 的形式化错误类别，但对象换成 M2F 和 Aristotle 在同一批 200 题上的失败/修题案例。这里不把 `exact?` 单独作为错误类别；`yes-exact?` 题不纳入本报告的主要失败原因统计。重点是：为什么没有得到一个干净的原题 Lean 证明。

- M2F：统计 `per_problem_summary.csv` 中 `reason_group != done` 的 27 题，并读取对应 `lean/m2f/problems/problem-N.lean` 最终文件。
- Aristotle：统计人工记录中 `no`、`no -编译有错`、`no -有sorry`、`no -failed`、`yes -xiu` 等非干净原题证明案例；不把 `yes-exact?` 作为本报告重点。

错误类别是多标签，因此各列不会相加为 100%。

其中 `Missing formal infrastructure` 是宽口径：它表示失败发生在凸分析、谱理论、对偶性、测度积分、KKT/分离定理等高层数学对象上，通常需要中间层 Mathlib 桥接定理；不等价于 Lean 明确报出“库中不存在某个定理”。

## 数据规模

| agent | cases | status / mark distribution |
| --- | --- | --- |
| m2f | 27 | success_but_remaining_sorry: 8, bad_statement_from_history: 7, bad_statement_long_tail: 7, success_but_remaining_sorryAx: 1, history_planned_not_completed: 1, stale_running_remaining_sorry: 1, partial_history_success_remaining_sorry: 1, needs_replan_unfinished: 1 |
| aristotle | 42 | no: 16, no -编译有错: 8, no -有sorry: 7, yes -xiu: 6, no -failed: 2, no - 编译有错: 1, no -全是sorry: 1, no - failed: 1 |

## 形式化错误分类统计

| agent | denom | Mathlib/API hallucination | Lean proficiency/type-system | Missing formal infrastructure | General capability/unfinished | Misalignment/statement issue |
| --- | --- | --- | --- | --- | --- | --- |
| m2f | 27 | 13/27 | 26/27 | 27/27 | 27/27 | 14/27 |
| aristotle | 42 | 8/42 | 29/42 | 38/42 | 19/42 | 8/42 |

## 按类别题号明细

| agent | category | problem ids |
| --- | --- | --- |
| m2f | Mathlib/API hallucination | 10, 17, 20, 54, 67, 74, 75, 96, 100, 165, 168, 198, 199 |
| m2f | Lean proficiency/type-system | 10, 17, 20, 30, 53, 54, 67, 70, 74, 75, 77, 86, 96, 100, 122, 131, 149, 161, 165, 168, 174, 176, 194, 197, 198, 199 |
| m2f | Missing formal infrastructure | 10, 17, 20, 30, 48, 53, 54, 67, 70, 74, 75, 77, 86, 96, 100, 122, 131, 149, 161, 165, 168, 174, 176, 194, 197, 198, 199 |
| m2f | General capability/unfinished | 10, 17, 20, 30, 48, 53, 54, 67, 70, 74, 75, 77, 86, 96, 100, 122, 131, 149, 161, 165, 168, 174, 176, 194, 197, 198, 199 |
| m2f | Misalignment/statement issue | 10, 20, 53, 70, 77, 86, 100, 122, 131, 161, 168, 176, 194, 199 |
| aristotle | Mathlib/API hallucination | 20, 46, 74, 86, 127, 161, 168, 199 |
| aristotle | Lean proficiency/type-system | 7, 11, 17, 20, 22, 30, 39, 40, 41, 42, 44, 49, 54, 66, 70, 75, 96, 108, 109, 111, 122, 127, 131, 161, 167, 168, 194, 197, 199 |
| aristotle | Missing formal infrastructure | 7, 11, 17, 20, 22, 30, 32, 39, 40, 41, 42, 44, 46, 49, 52, 53, 54, 66, 67, 70, 74, 75, 77, 86, 96, 108, 109, 111, 125, 127, 131, 161, 167, 168, 194, 197, 198, 199 |
| aristotle | General capability/unfinished | 7, 17, 30, 32, 52, 53, 67, 74, 75, 86, 96, 109, 111, 118, 140, 167, 176, 197, 199 |
| aristotle | Misalignment/statement issue | 52, 53, 70, 86, 122, 161, 168, 194 |

## 类别解释

1. **Mathlib/API hallucination**：调用不存在或不匹配的 theorem/field/API，或反馈显示模型需要一个高层 Mathlib lemma 但实际没有可用接口。
2. **Lean proficiency/type-system**：编译错误、类型不匹配、tactic/rewrite/simp/linarith 失败、typeclass synthesis 失败等。
3. **Missing formal infrastructure**：题目依赖凸分析、矩阵谱理论、测度概率、对偶性、KKT、分离定理等中间层数学基础设施；数学方向清楚但 Mathlib 缺少现成桥接定理。
4. **General capability/unfinished**：仍有 `sorry/sorryAx/admit`、没有完成计划、运行失败或最后保留占位证明。
5. **Misalignment/statement issue**：题面/形式化 statement 可能有问题，或者需要 `xiu` 修题/改 statement 才能完成。

## 代表性例子

### m2f
- **Mathlib/API hallucination**：problem 17；status=`success_but_remaining_sorry`；evidence=active placeholders: sorry=1 | feedback indicates unfinished proof / remaining sorry / failed run | advanced optimization/analysis concept or explicit missing-infrastructure feedback | unknown/invalid/high-level API signal | compile/type/tactic signal or non-placeholder tactic-heavy attempt；source=`/root/workspace/benchmark/JSON2LEAN/lean/m2f/problems/problem-17.lean`；feedback=queue marked success/processed one file, but the Lean file still contains sorry; likely final pipeline considered the file processed after restoring a compiling state. Latest log excerpt: [Final Agent B summary] - attempt 3: summary=[proble
- **Lean proficiency/type-system**：problem 30；status=`success_but_remaining_sorryAx`；evidence=active placeholders: sorryAx=3 | feedback indicates unfinished proof / remaining sorry / failed run | advanced optimization/analysis concept or explicit missing-infrastructure feedback | compile/type/tactic signal or non-placeholder tactic-heavy attempt；source=`/root/workspace/benchmark/JSON2LEAN/lean/m2f/problems/problem-30.lean`；feedback=queue marked success, but current file still uses sorryAx placeholders at lines 281, 284, and 287; final Agent B log also noted remaining sorry-based warnings.
- **Missing formal infrastructure**：problem 48；status=`history_planned_not_completed`；evidence=active placeholders: sorry=3 | advanced optimization/analysis concept or explicit missing-infrastructure feedback；source=`/root/workspace/benchmark/JSON2LEAN/lean/m2f/problems/problem-48.lean`；feedback=Historical final run has Agent C plan only for remaining goals; no successful completion/result found, and file still contains sorry.
- **General capability/unfinished**：problem 149；status=`success_but_remaining_sorry`；evidence=active placeholders: sorry=2 | feedback indicates unfinished proof / remaining sorry / failed run | advanced optimization/analysis concept or explicit missing-infrastructure feedback | compile/type/tactic signal or non-placeholder tactic-heavy attempt；source=`/root/workspace/benchmark/JSON2LEAN/lean/m2f/problems/problem-149.lean`；feedback=queue marked success/processed one file, but the Lean file still contains sorry; likely final pipeline considered the file processed after restoring a compiling state. Latest log excerpt: If Agent A introduced temporary helper lemmas during
- **Misalignment/statement issue**：problem 53；status=`bad_statement_from_history`；evidence=active placeholders: sorry=1 | feedback indicates unfinished proof / remaining sorry / failed run | feedback indicates statement repair, false statement, or counterexample | advanced optimization/analysis concept or explicit missing-infrastructure feedback | compile/type/tactic signal or non-placeholder tactic-heavy attempt；source=`/root/workspace/benchmark/JSON2LEAN/lean/m2f/problems/problem-53.lean`；feedback=Historical final run reported failed_bad_statement. The target theorem is mathematically false as written. Earlier in the same file, `lagrangeDualFunction_statement_false` proves the negation of the theorem's universal statement by speciali

### aristotle
- **Mathlib/API hallucination**：problem 46；status=`no`；evidence=advanced optimization/analysis concept or explicit missing-infrastructure feedback | unknown/invalid/high-level API signal；source=`/root/workspace/benchmark/JSON2LEAN/记录/精确记录.md`；feedback=I made significant progress on proving the theorems in `problems/problem-46.lean`. Here is the status:  **Theorem 1: `normalCone_is_convex_cone`** — ✅ Fully proved. The normal cone is shown to be both convex and closed under non-negative sc
- **Lean proficiency/type-system**：problem 11；status=`no`；evidence=advanced optimization/analysis concept or explicit missing-infrastructure feedback | compile/type/tactic signal or non-placeholder tactic-heavy attempt；source=`/root/workspace/benchmark/JSON2LEAN/记录/精确记录.md`；feedback=I made significant progress on the theorem `sublevel_distribution_logConcave` in `problems/problem-11.lean`. The original file had a single `sorry` in the main theorem. I decomposed the proof into a clean chain of helper lemmas:  1. **`prek
- **Missing formal infrastructure**：problem 77；status=`no`；evidence=advanced optimization/analysis concept or explicit missing-infrastructure feedback；source=`/root/workspace/benchmark/JSON2LEAN/记录/精确记录.md`；feedback=I made significant progress on the theorem in `problems/problem-77.lean` proving that Newton's method at a multiple root converges Q-linearly. The proof is structured as follows:  **Proved lemmas:** 1. `f_zero_of_multipleRoot` — f(0) = 0 fo
- **General capability/unfinished**：problem 118；status=`no - failed`；evidence=feedback indicates unfinished proof / remaining sorry / failed run；source=`/root/workspace/benchmark/JSON2LEAN/记录/精确记录.md`；feedback=
- **Misalignment/statement issue**：problem 122；status=`yes -xiu`；evidence=feedback indicates statement repair, false statement, or counterexample | compile/type/tactic signal or non-placeholder tactic-heavy attempt；source=`/root/workspace/benchmark/JSON2LEAN/记录/精确记录.md`；feedback=The original theorem `g_homogeneous` (with `0 ≤ t`) was **false** as stated. The issue arises when `t = 0` and `f(0) < 0`:  - `g(0) = sInf {f(0)/α | α > 0}` is `⊥` (bottom in `WithBot ℝ`) since `f(0)/α → -∞` as `α → 0⁺` - But `0 * g(x) = 0`

## 结合 M2F 与 Aristotle 反馈的观察

### M2F

- M2F 的失败高度集中在两类：`bad_statement_*` 与 `remaining_sorry/sorryAx`。前者说明一部分题的形式化 statement 或可证明性需要额外审计；后者说明系统能推进证明但停在关键中间引理。
- `success_but_remaining_sorry` 一类通常不是语法层面的小错，而是缺少深层桥接结果，例如谱理论、矩阵不等式、测度积分、Prékopa-Leindler、Farkas/duality 等。
- M2F 的 `bad_statement_long_tail/from_history` 与 Aristotle 的 `yes -xiu` 是同一个现象的两种表现：benchmark 不只测 theorem proving，也测 statement 是否忠实、是否可证明、是否需要修题。

### Aristotle

- Aristotle 的失败记录里 `no -有sorry`、`no -全是sorry` 多数明确指出“已经证明部分 helper，但关键深层定理缺失”。这更接近 Missing formal infrastructure，而不是简单的模型没理解题意。
- `no -编译有错` 反映 Lean proficiency/type-system 问题：证明草稿可能数学上接近，但没有通过 Lean 的类型、rewrite、simp、linarith、typeclass 等检查。
- `yes -xiu` 不应算原题成功，但它对 benchmark 有价值：它暴露了题面或形式化 statement 的边界问题，可作为 statement-audit 子任务。

## 和 pass@32 的关系

pass@32 的主要错误是 `库基础设施缺口 + API 幻觉 + Lean 类型系统细节` 的组合；M2F/Aristotle 的人工与汇总反馈也支持这个结论。不同之处是：M2F/Aristotle 的记录更能暴露 statement 层面的错误，例如 `bad_statement` 与 `xiu`；pass@32 的最后快照更能暴露具体 Lean 报错类型。

## 结论

在这 200 题上，失败原因不宜简单归因于模型能力不足。更准确的说法是：当前系统在高层优化数学 formalization 中，经常缺少可直接调用的 Mathlib 中间层定理；模型随后会出现 API 幻觉、类型系统/tactic 失败，或保留 `sorry`。这说明 benchmark 的价值在于同时检验 proof search、Mathlib 检索/API 对齐、statement audit 和高层数学库建设需求。

## 产物

- 明细 CSV：`m2f_aristotle_formal_error_records_20260505.csv`
- 分析脚本：`analyze_m2f_aristotle_formal_errors.py`
