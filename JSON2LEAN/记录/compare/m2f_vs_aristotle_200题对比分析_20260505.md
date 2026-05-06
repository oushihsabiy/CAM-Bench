# m2f 与 aristotle 在 200 题 benchmark 上的对比分析

生成日期：2026-05-05

## 数据口径

- m2f：读取 `/root/workspace/benchmark/JSON2LEAN/lean/m2f/final99_run_summary_20260504T131426Z/per_problem_summary.csv` 和对应 JSON；以 `reason_group == done` 作为“做出来”，其余视为未完成。
- aristotle：读取 `/root/workspace/benchmark/JSON2LEAN/记录/精确记录.md`；以人工审核的 `人工标记` 为准，`yes*` 算做出来，`no*` 算未做出来。
- aristotle 原始结果：读取 `/root/workspace/benchmark/JSON2LEAN/记录/status_json/status_json`，只用于检查原始 status 与人工审核的偏差。

重要 caveat：两边不是完全同一实验条件。aristotle 是逐题独立运行，不能看到或引用其他题；m2f 在同一批题内可以 `import` 其他 problem 文件，因此 m2f 的结果更接近“batch/library-building setting”，会包含跨题复用收益和跨题依赖成本。若目标是比较单题独立求解能力，应把这个因素单独控制；若目标是比较在一批相关题上构建可复用 Lean 小库的能力，则 m2f 的设置更接近真实形式化项目。

## 总体结果

| 指标 | m2f | aristotle 人工审核 |
|---|---:|---:|
| 做出题数 | 173 / 200 (86.5%) | 164 / 200 (82.0%) |
| 未做出题数 | 27 | 36 |
| 两者都做出 | 不适用 | 153 |
| 至少一个 agent 做出 | 不适用 | 184 / 200 (92.0%) |
| 两者都未做出 | 不适用 | 16 |

关键结论：m2f 的严格无 sorry 口径通过 173 题，比 aristotle 人工审核的 164 题多 9 题；但两者有明显互补，任取两者中成功的一份可以覆盖 184 题，剩下 16 题是共同难点。

## 失败集合对比

- m2f 未做出 27 题：10, 17, 20, 30, 48, 53, 54, 67, 70, 74, 75, 77, 86, 96, 100, 122, 131, 149, 161, 165, 168, 174, 176, 194, 197, 198, 199
- aristotle 未做出 36 题：7, 11, 17, 20, 22, 30, 32, 39, 40, 41, 42, 44, 46, 49, 53, 54, 66, 67, 74, 75, 77, 86, 96, 108, 109, 111, 118, 125, 127, 131, 140, 167, 176, 197, 198, 199
- 两者都未做出 16 题：17, 20, 30, 53, 54, 67, 74, 75, 77, 86, 96, 131, 176, 197, 198, 199
- m2f 做出但 aristotle 未做出 20 题：7, 11, 22, 32, 39, 40, 41, 42, 44, 46, 49, 66, 108, 109, 111, 118, 125, 127, 140, 167
- aristotle 做出但 m2f 未做出 11 题：10, 48, 70, 100, 122, 149, 161, 165, 168, 174, 194

共同失败题集中在深数学基础设施或陈述问题：Prékopa-Leindler/Brunn-Minkowski、Pick/Herglotz/Schur、John/Loewner 椭球、矩阵 log-det/谱函数凸性、Farkas/锥对偶、Newton 多重根收敛、LICQ slack reformulation 等。

## m2f 未做出题目与原因

| 题号 | m2f 用时 | m2f reason_group | 原因简述 | aristotle 人工结果 |
|---:|---:|---|---|---|
| 10 | 13h5m | `bad_statement_from_history` | 历史日志判定目标陈述有缺陷或不可由现有假设推出。 | yes -exact? |
| 17 | 15h55m | `success_but_remaining_sorry` | 队列/日志接近成功，但当前 Lean 文件仍有 sorry；属于证明洞未清完。 | no -有sorry |
| 20 | 21h59m | `bad_statement_long_tail` | Agent 反复报 bad_statement，进入长尾后被停止。 | no -编译有错 |
| 30 | 2h1m | `success_but_remaining_sorryAx` | 仍有 sorryAx 占位；形式上不是完整证明。 | no -有sorry |
| 48 | 0m | `history_planned_not_completed` | 只有后续计划或历史线索，没有完成证明；当前仍有 sorry。 | yes |
| 53 | 48h17m | `bad_statement_from_history` | 历史日志判定目标陈述有缺陷或不可由现有假设推出。 | no -有sorry |
| 54 | 16h42m | `success_but_remaining_sorry` | 队列/日志接近成功，但当前 Lean 文件仍有 sorry；属于证明洞未清完。 | no |
| 67 | 2h16m | `success_but_remaining_sorry` | 队列/日志接近成功，但当前 Lean 文件仍有 sorry；属于证明洞未清完。 | no |
| 70 | 21h28m | `bad_statement_long_tail` | Agent 反复报 bad_statement，进入长尾后被停止。 | yes -xiu |
| 74 | 16h34m | `success_but_remaining_sorry` | 队列/日志接近成功，但当前 Lean 文件仍有 sorry；属于证明洞未清完。 | no |
| 75 | 29m | `stale_running_remaining_sorry` | 队列状态陈旧/残留 running，当前文件仍有 sorry。 | no |
| 77 | 43h20m | `bad_statement_from_history` | 历史日志判定目标陈述有缺陷或不可由现有假设推出。 | no |
| 86 | 21h10m | `bad_statement_long_tail` | Agent 反复报 bad_statement，进入长尾后被停止。 | no -有sorry |
| 96 | 1h42m | `success_but_remaining_sorry` | 队列/日志接近成功，但当前 Lean 文件仍有 sorry；属于证明洞未清完。 | no -有sorry |
| 100 | 50h12m | `bad_statement_from_history` | 历史日志判定目标陈述有缺陷或不可由现有假设推出。 | yes-exact? |
| 122 | 20h11m | `bad_statement_long_tail` | Agent 反复报 bad_statement，进入长尾后被停止。 | yes -xiu |
| 131 | 32h9m | `bad_statement_from_history` | 历史日志判定目标陈述有缺陷或不可由现有假设推出。 | no |
| 149 | 13.8m | `success_but_remaining_sorry` | 队列/日志接近成功，但当前 Lean 文件仍有 sorry；属于证明洞未清完。 | yes |
| 161 | 13h39m | `bad_statement_from_history` | 历史日志判定目标陈述有缺陷或不可由现有假设推出。 | yes -xiu |
| 165 | 8.5m | `partial_history_success_remaining_sorry` | 历史上完成了部分目标，但当前仍有后续 sorry。 | yes |
| 168 | 41h24m | `bad_statement_from_history` | 历史日志判定目标陈述有缺陷或不可由现有假设推出。 | yes -xiu |
| 174 | 4h33m | `success_but_remaining_sorry` | 队列/日志接近成功，但当前 Lean 文件仍有 sorry；属于证明洞未清完。 | yes |
| 176 | 19h12m | `bad_statement_long_tail` | Agent 反复报 bad_statement，进入长尾后被停止。 | no -failed |
| 194 | 7h52m | `bad_statement_long_tail` | Agent 反复报 bad_statement，进入长尾后被停止。 | yes -xiu |
| 197 | 41h24m | `needs_replan_unfinished` | 需要重新规划的未完成题；当前仍有 sorry。 | no -有sorry |
| 198 | 3h58m | `success_but_remaining_sorry` | 队列/日志接近成功，但当前 Lean 文件仍有 sorry；属于证明洞未清完。 | no |
| 199 | 7h51m | `bad_statement_long_tail` | Agent 反复报 bad_statement，进入长尾后被停止。 | no |

m2f 失败原因分组：
- `success_but_remaining_sorry`：8 题，17, 54, 67, 74, 96, 149, 174, 198。队列/日志接近成功，但当前 Lean 文件仍有 sorry；属于证明洞未清完。
- `bad_statement_from_history`：7 题，10, 53, 77, 100, 131, 161, 168。历史日志判定目标陈述有缺陷或不可由现有假设推出。
- `bad_statement_long_tail`：7 题，20, 70, 86, 122, 176, 194, 199。Agent 反复报 bad_statement，进入长尾后被停止。
- `history_planned_not_completed`：1 题，48。只有后续计划或历史线索，没有完成证明；当前仍有 sorry。
- `needs_replan_unfinished`：1 题，197。需要重新规划的未完成题；当前仍有 sorry。
- `partial_history_success_remaining_sorry`：1 题，165。历史上完成了部分目标，但当前仍有后续 sorry。
- `stale_running_remaining_sorry`：1 题，75。队列状态陈旧/残留 running，当前文件仍有 sorry。
- `success_but_remaining_sorryAx`：1 题，30。仍有 sorryAx 占位；形式上不是完整证明。

可以看到，m2f 的 27 个失败里有 14 个属于 `bad_statement*`，13 个属于“当前文件仍有 sorry/sorryAx 或未完成”。`bad_statement*` 中有 7 题后来被 aristotle 人工判为 yes（10, 70, 100, 122, 161, 168, 194），其中多题带 `yes -xiu`，说明这类差异很可能来自“是否允许修正/重述问题”或 bad-statement 判定策略差异，而不只是证明能力差异。

## aristotle 未做出题目与原因

| 题号 | aristotle 用时 | 人工标记 | 原因简述 | m2f 结果 |
|---:|---:|---|---|---|
| 7 | 12h24m | no | 剩余 Fischer/Cauchy-Binet 与最小特征值乘积、log 特征值和凹性等谱理论基础设施。 | `done` |
| 11 | 11h6m | no | 卡在 Prékopa-Leindler/Brunn-Minkowski 型深定理。 | `done` |
| 17 | 16h0m | no -有sorry | 谱分解与 bordered Hessian 判别中仍有 helper sorry。 | `success_but_remaining_sorry` |
| 20 | 4h45m | no -编译有错 | 人工审核为编译有错；原始 summary 声称成功但不可靠。 | `bad_statement_long_tail` |
| 22 | 17h5m | no | Euclidean distance matrix 对偶锥的反向包含，需更强分离/线性代数基础设施。 | `done` |
| 30 | 8h43m | no -有sorry | log-concavity 部分依赖 Prékopa-Leindler。 | `success_but_remaining_sorryAx` |
| 32 | 13h50m | no -有sorry | analytic center 椭球界，缺 log-det/特征值/微分基础设施。 | `done` |
| 39 | 1h20m | no - 编译有错 | 人工审核为编译有错；原始 summary 声称成功但不可靠。 | `done` |
| 40 | 2h8m | no -编译有错 | 人工审核为编译有错；原始 summary 声称成功但不可靠。 | `done` |
| 41 | 6h58m | no -编译有错 | 人工审核为编译有错；原始 summary 声称成功但不可靠。 | `done` |
| 42 | 51m | no -编译有错 | 人工审核为编译有错；原始 summary 声称成功但不可靠。 | `done` |
| 44 | 1h1m | no -编译有错 | 人工审核为编译有错；原始 summary 声称成功但不可靠。 | `done` |
| 46 | 12h5m | no | normal cone/polyhedron 等式的 hard direction，实质是 Farkas/分离定理应用。 | `done` |
| 49 | 5h59m | no -编译有错 | 人工审核为编译有错；原始 summary 声称成功但不可靠。 | `done` |
| 53 | 6h15m | no -有sorry | 陈述与类型不匹配：A 被建模成任意函数，证明需要线性矩阵假设。 | `bad_statement_from_history` |
| 54 | 8h24m | no | log-det primal/dual 形式化，核心矩阵 infimum 与 Lagrange dual 框架缺口。 | `success_but_remaining_sorry` |
| 66 | 56m | no -编译有错 | 人工审核为编译有错；原始 summary 声称成功但不可靠。 | `done` |
| 67 | 9h35m | no | det/trace 组合 log-concavity，Minkowski determinant 不足以推出主结论。 | `success_but_remaining_sorry` |
| 74 | 7h38m | no | John ellipsoid 的 Fritz John/KKT 条件未形式化。 | `success_but_remaining_sorry` |
| 75 | 8h13m | no | Ky Fan norm SDP，仍缺 block PSD/谱范数相关核心结论。 | `stale_running_remaining_sorry` |
| 77 | 7h59m | no | Newton multiple root Q-linear 证明仍依赖未完成的 ratio limit；m2f 还判定陈述过强。 | `bad_statement_from_history` |
| 86 | 6h3m | no -有sorry | Lagrangian 约束符号错误，存在具体反例。 | `bad_statement_long_tail` |
| 96 | 12h20m | no -有sorry | Pick/Carathéodory 插值，需 Herglotz 表示/Schur 算法。 | `success_but_remaining_sorry` |
| 108 | 20m | no -编译有错 | 人工审核为编译有错；原始 summary 声称成功但不可靠。 | `done` |
| 109 | 14h55m | no | log-det barrier 椭球界，和 analytic center 类似，需要深矩阵微分/特征值基础设施。 | `done` |
| 111 | 5h37m | no -全是sorry | 人工标记为全是 sorry，原始 COMPLETE 不可信。 | `done` |
| 118 | 2h54m | no - failed | 原始任务 FAILED，未给 output_summary；人工审核失败。 | `done` |
| 125 | 12h19m | no | Loewner-John ellipsoid 唯一性，需椭球体积/严格凸性等基础设施。 | `done` |
| 127 | 12h35m | no | 对偶锥等式 hard direction，本质是 Farkas lemma。 | `done` |
| 131 | 9h39m | no | LICQ slack reformulation，需精确计算 product space 中约束梯度；m2f 还指出结构字段可覆写。 | `bad_statement_from_history` |
| 140 | 3h12m | no -failed | 原始任务 FAILED，未给 output_summary；人工审核失败。 | `done` |
| 167 | 11h28m | no | Thomas/tridiagonal 结论的核心 Hessian 恒等式未完成。 | `done` |
| 176 | 3h40m | no -failed | 原始任务 FAILED，未给 output_summary；m2f 反复 bad_statement。 | `bad_statement_long_tail` |
| 197 | 8h39m | no -有sorry | convolution log-concavity 依赖一般 Prékopa-Leindler。 | `needs_replan_unfinished` |
| 198 | 11h55m | no | log det + trace inverse 的矩阵凸性；需谱函数/Hessian 矩阵分析。 | `success_but_remaining_sorry` |
| 199 | 13h54m | no | Pick-Nevanlinna 插值，需 Herglotz/Riesz 表示和 Schur 构造。 | `bad_statement_long_tail` |

aristotle 的失败大致分三类：
- 编译有错：9 题，20, 39, 40, 41, 42, 44, 49, 66, 108。这些题的原始 output_summary 往往声称成功，说明原始 status/summary 不能直接用作准确标签。
- 明确剩余 sorry/全是 sorry：8 题，17, 30, 32, 53, 86, 96, 111, 197。
- 原始任务 FAILED：3 题，118, 140, 176。
- 其他人工 no：16 题，7, 11, 22, 46, 54, 67, 74, 75, 77, 109, 125, 127, 131, 167, 198, 199，多数是深定理缺基础设施或题目陈述/建模存在问题。

## aristotle 原始 status 的不准确性

- 原始 status JSON 文件数：217，覆盖 200 题；其中 17 题有重复运行记录。
- 按每题 `last_updated_at` 取最新 status，状态分布为：{'FAILED': 4, 'COMPLETE': 142, 'COMPLETE_WITH_ERRORS': 52, 'IN_PROGRESS': 2}。
- 最新原始 status 与人工标记冲突 38 题。
- 原始 COMPLETE 但人工 no：8 题，20, 39, 41, 42, 49, 66, 108, 111。
- 原始非 COMPLETE 但人工 yes：30 题，1, 13, 18, 29, 33, 38, 48, 52, 57, 61, 64, 83, 89, 95, 106, 107, 122, 124, 126, 128, 155, 159, 160, 161, 162, 172, 179, 189, 191, 195。

因此 aristotle 的原始 status 不能直接作为 benchmark 成败口径；本报告后续比较均以人工审核为准。

## 耗时分布

### 总体统计

| agent/集合 | 统计 |
|---|---|
| m2f 全部 | n=200, mean=4h27m, median=27.1m, p75=2h36m, p90=13h58m, max=50h12m |
| m2f 成功 | n=173, mean=2h26m, median=23.6m, p75=1h16m, p90=11h19m, max=22h9m |
| m2f 失败 | n=27, mean=17h19m, median=15h55m, p75=21h44m, p90=42h11m, max=50h12m |
| aristotle 全部 | n=200, mean=3h11m, median=1h28m, p75=4h6m, p90=8h48m, max=17h5m |
| aristotle 成功 | n=164, mean=2h6m, median=1h2m, p75=2h38m, p90=5h36m, max=12h15m |
| aristotle 失败 | n=36, mean=8h8m, median=8h18m, p75=12h8m, p90=13h52m, max=17h5m |

配对比较：m2f 在 149/200 题上耗时短于 aristotle，aristotle 在 51/200 题上耗时短于 m2f；m2f-aristotle 的中位差为 -28.9m（负数表示 m2f 更快），均值差为 1h15m。均值被 m2f 少数极长 bad_statement/重试长尾拉高。

### m2f 分桶

| 区间 | 总数 | 成功 | 失败 | 成功率 |
|---:|---:|---:|---:|---:|
| <30m | 107 | 103 | 4 | 96.3% |
| 30-60m | 17 | 17 | 0 | 100.0% |
| 1-2h | 18 | 17 | 1 | 94.4% |
| 2-4h | 12 | 9 | 3 | 75.0% |
| 4-8h | 4 | 1 | 3 | 25.0% |
| 8-12h | 14 | 14 | 0 | 100.0% |
| >12h | 28 | 12 | 16 | 42.9% |

### aristotle 分桶

| 区间 | 总数 | 成功 | 失败 | 成功率 |
|---:|---:|---:|---:|---:|
| <30m | 39 | 38 | 1 | 97.4% |
| 30-60m | 42 | 40 | 2 | 95.2% |
| 1-2h | 35 | 33 | 2 | 94.3% |
| 2-4h | 32 | 28 | 4 | 87.5% |
| 4-8h | 26 | 18 | 8 | 69.2% |
| 8-12h | 15 | 6 | 9 | 40.0% |
| >12h | 11 | 1 | 10 | 9.1% |

耗时观察：
- m2f 的中位耗时只有 27m，明显低于 aristotle 的 88m；短题上 m2f 更激进，<30m 桶成功率 96.3%。
- m2f 的均值反而更高，原因是长尾很重：失败题均值 17h19m、p90 42h11m，主要来自 bad_statement 重复尝试和历史多日志累积。
- aristotle 的成功率随时间单调下降更明显：8-12h 桶成功率 40.0%，>12h 桶只有 9.1%。这说明人工审核下，长时间运行通常不是“快要成功”，而是卡在缺失数学基础设施或残留 sorry。
- m2f 有一批 8-12h 成功题全部通过，但 >12h 后成功率降到 42.9%；m2f 的长时间成功更多像是多轮日志/历史结果累计，长时间失败则多为 bad_statement 或未完成 proof hole。

为什么 m2f 的分布更极端：
- m2f 的时间不是完全均质的“单题 wall-clock”。有些题使用 `reported` 时间，有些是 `history_log_sum` 或 `log_sum`，历史日志累计会把少数长尾题拉到很大。
- m2f 允许跨题 import，快题可能复用其他 problem 中已经做出的 lemma 或深定理桥接；真正昂贵的证明成本可能被计到另一个题上，导致大量题落入 `<30m`。
- m2f 的调度/判定像两段式：能快速清掉的题很快完成；一旦进入 bad_statement、剩余 sorry、反复修复编译的状态，就会长时间重试或累计历史日志。因此中间 `4-8h` 桶很少，而 `<30m` 和 `>12h` 两端很多。
- aristotle 是逐题独立 API 任务，时间更像单个 job 从创建到更新的耗时；没有跨题复用，也较少把多轮历史日志累计到同一题，所以分布更平滑。
- 这也解释了 m2f 的中位数更低但均值更高：大多数题很快，少数 bad_statement/未完成题极长。

## 互补性分析

| 集合 | 题数 | 题号 | m2f 中位耗时 | aristotle 中位耗时 |
|---|---:|---|---:|---:|
| 两者都做出 | 153 | 1, 2, 3, 4, 5, 6, 8, 9, 12, 13, 14, 15, 16, 18, 19, 21, 23, 24, 25, 26, 27, 28, 29, 31, 33, 34, 35, 36, 37, 38, 43, 45, 47, 50, 51, 52, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 68, 69, 71, 72, 73, 76, 78, 79, 80, 81, 82, 83, 84, 85, 87, 88, 89, 90, 91, 92, 93, 94, 95, 97, 98, 99, 101, 102, 103, 104, 105, 106, 107, 110, 112, 113, 114, 115, 116, 117, 119, 120, 121, 123, 124, 126, 128, 129, 130, 132, 133, 134, 135, 136, 137, 138, 139, 141, 142, 143, 144, 145, 146, 147, 148, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 162, 163, 164, 166, 169, 170, 171, 172, 173, 175, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 195, 196, 200 | 19.0m | 1h1m |
| m2f 做出但 aristotle 未做出 | 20 | 7, 11, 22, 32, 39, 40, 41, 42, 44, 46, 49, 66, 108, 109, 111, 118, 125, 127, 140, 167 | 1h18m | 6h28m |
| aristotle 做出但 m2f 未做出 | 11 | 10, 48, 70, 100, 122, 149, 161, 165, 168, 174, 194 | 13h5m | 1h19m |
| 两者都未做出 | 16 | 17, 20, 30, 53, 54, 67, 74, 75, 77, 86, 96, 131, 176, 197, 198, 199 | 16h38m | 8h32m |

互补性最强的两组：
- m2f 独有成功 20 题，aristotle 在这些题上的中位耗时 6h28m，m2f 中位耗时 1h18m；这类题多是 aristotle 编译错误、Farkas/锥对偶、ellipsoid、Hessian 计算等失败。
- aristotle 独有成功 11 题，m2f 在这些题上的中位耗时 13h5m，aristotle 中位耗时 1h19m；其中 70, 122, 161, 168, 194 带 `yes -xiu`，提示 m2f 的 bad_statement 判定与人工修订策略存在差异。

## 在这 200 个 benchmark 上的结论

1. m2f 按“当前 Lean 文件无 sorry”口径略强：173/200 vs aristotle 人工 yes 164/200。
2. 两者不是简单包含关系：m2f 独有成功 20 题，aristotle 独有成功 11 题；组合后可达 184/200，这比单 agent 高 10-20 题。
3. 共同失败的 16 题基本是 benchmark 的硬核部分，失败原因以缺少库级深定理和题目陈述/建模问题为主，而不是普通 tactic 调参。
4. aristotle 原始 status 噪声很大，38/200 与人工审核冲突；后续评测如果要自动化，需要至少检查 Lean 编译、sorry/sorryAx、以及是否修改了 theorem statement。
5. m2f 的工程策略更善于快速收敛大量简单/中等题，但 bad_statement 和重试长尾会显著拉高均值耗时；需要更早的 false-statement 判定终止条件，以及对“可修题/不可改题”的明确评测规则。
6. 对 benchmark 本身，建议把 16 个共同失败题和 m2f/aristotle 判定冲突题单独标注为“需要题面审计/需要基础设施”的子集；否则总成功率会混合证明能力、题面正确性、是否允许修题三种因素。

## 附：共同失败 16 题的主因

| 题号 | 主因 |
|---:|---|
| 17 | 谱分解与 bordered Hessian 判别中仍有 helper sorry。 |
| 20 | 人工审核为编译有错；原始 summary 声称成功但不可靠。 |
| 30 | log-concavity 部分依赖 Prékopa-Leindler。 |
| 53 | 陈述与类型不匹配：A 被建模成任意函数，证明需要线性矩阵假设。 |
| 54 | log-det primal/dual 形式化，核心矩阵 infimum 与 Lagrange dual 框架缺口。 |
| 67 | det/trace 组合 log-concavity，Minkowski determinant 不足以推出主结论。 |
| 74 | John ellipsoid 的 Fritz John/KKT 条件未形式化。 |
| 75 | Ky Fan norm SDP，仍缺 block PSD/谱范数相关核心结论。 |
| 77 | Newton multiple root Q-linear 证明仍依赖未完成的 ratio limit；m2f 还判定陈述过强。 |
| 86 | Lagrangian 约束符号错误，存在具体反例。 |
| 96 | Pick/Carathéodory 插值，需 Herglotz 表示/Schur 算法。 |
| 131 | LICQ slack reformulation，需精确计算 product space 中约束梯度；m2f 还指出结构字段可覆写。 |
| 176 | 原始任务 FAILED，未给 output_summary；m2f 反复 bad_statement。 |
| 197 | convolution log-concavity 依赖一般 Prékopa-Leindler。 |
| 198 | log det + trace inverse 的矩阵凸性；需谱函数/Hessian 矩阵分析。 |
| 199 | Pick-Nevanlinna 插值，需 Herglotz/Riesz 表示和 Schur 构造。 |

## 附：m2f 报 bad_statement 但 aristotle 的情况

m2f 一共有 14 题被归到 `bad_statement_from_history` 或 `bad_statement_long_tail`：

10, 20, 53, 70, 77, 86, 100, 122, 131, 161, 168, 176, 194, 199

其中，aristotle 人工审核完成了 7 题：

| 题号 | m2f 分组 | aristotle 人工标记 | aristotle 是否也报告题目问题 | 备注 |
|---:|---|---|---|---|
| 10 | `bad_statement_from_history` | yes -exact? | 否 | aristotle 报告两个 theorem 都证明完成；这是最明确的“m2f 报 bad_statement，但 aristotle 正常完成且未报题面问题”的例子。 |
| 70 | `bad_statement_long_tail` | yes -xiu | 是 | aristotle 认为原 convexity 说法数学上不正确，并给出修正变量替换方向；完成口径依赖人工修订。 |
| 100 | `bad_statement_from_history` | yes-exact? | 是/有修订记录 | 记录中先指出原 domain characterization false as stated，后续运行给出使用 `symmPart` 的证明；该题应视作“修订后完成”。 |
| 122 | `bad_statement_long_tail` | yes -xiu | 是 | aristotle 明确说原 `g_homogeneous` 在 `t = 0` 时 false as stated，并修正。 |
| 161 | `bad_statement_from_history` | yes -xiu | 是 | aristotle 先指出 `n = 0` 反例，需要 `n ≥ 1`；后续记录为修正后完成。 |
| 168 | `bad_statement_from_history` | yes -xiu | 是 | aristotle 指出结构字段 `P.feasible` 可覆写，原 theorem false as stated，并改为显式可行性条件。 |
| 194 | `bad_statement_long_tail` | yes -xiu | 是 | aristotle 指出 `transposeRange` 结构字段可覆写，原 theorem false as stated，并改用 `Set.range p.A.transpose.mulVec`。 |

结论：如果只问“m2f 报 bad_statement，但 aristotle 最终完成”，共有 7 题：10, 70, 100, 122, 161, 168, 194。  
如果进一步要求“aristotle 完成且没有报告题目本身有问题”，目前只有题 10 最干净；其余 6 题基本都是 `yes -xiu` 或带修订/反例说明，说明 aristotle 的完成口径包含了人工修题。

另外还有 5 题 m2f 报 bad_statement，但 aristotle 未完成且也没有明确把失败归因于题目 false/题面错误：

| 题号 | m2f 分组 | aristotle 人工标记 | aristotle 侧说明 |
|---:|---|---|---|
| 20 | `bad_statement_long_tail` | no -编译有错 | 原始 summary 声称证明成功，但人工审核为编译有错；未明确说题目本身 false。 |
| 77 | `bad_statement_from_history` | no | aristotle 主要描述 Newton multiple root 证明未完成，剩余 ratio limit 相关证明洞；未明确报题目有错。 |
| 131 | `bad_statement_from_history` | no | aristotle 说 LICQ slack reformulation 形式化很难，未明确报题目 false；m2f 则指出结构字段可覆写导致陈述问题。 |
| 176 | `bad_statement_long_tail` | no -failed | aristotle 原始任务 FAILED 且无 output_summary；没有可用证据说明它报过题目问题。 |
| 199 | `bad_statement_long_tail` | no | aristotle 归因为 Pick-Nevanlinna 所需复分析基础设施缺失，未明确报题目有错。 |

剩下 2 题 m2f 报 bad_statement，aristotle 也明确报告了题目/建模问题但未完成：53, 86。
