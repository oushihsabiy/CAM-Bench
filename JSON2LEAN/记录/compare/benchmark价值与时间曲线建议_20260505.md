# 200 题 benchmark 的价值定位与时间曲线建议

生成日期：2026-05-05

## 核心立场

这批 200 题最有价值的地方，不是用来宣称某个 agent 比另一个 agent 强，而是作为一个 Lean 数学形式化 benchmark，提供多维诊断信号：

1. 常规证明工程吞吐：大量题能在分钟到数小时内完成，适合看 agent 是否能稳定消 `sorry`、修编译、拆 helper lemma。
2. 真实数学基础设施缺口：共同失败题集中暴露 Prékopa-Leindler、Brunn-Minkowski、Pick/Herglotz/Schur、John/Loewner ellipsoid、矩阵 log-det/谱函数凸性、Farkas/锥对偶等缺失。
3. 题面审计能力：有一批题被判为 false as stated、字段可覆写、缺边界条件、建模类型不够强。这能测试 agent 是否会发现不可证目标，而不是盲目填证明。
4. 评测协议可靠性：aristotle 原始 status 与人工审核冲突 38/200，说明自动 benchmark 不能只看 `COMPLETE`，还需要 Lean 编译、无 `sorry/sorryAx`、statement 是否被改、是否证明了修正版等检查。
5. batch/library-building 能力：m2f 可以跨题 `import`，这使 benchmark 能测试“在一批相关题上积累小型 Lean 库”的能力，而不只是单题隔离求解。

这个定位对我们有利：它把 benchmark 从单一 pass rate 扩展成“证明、审题、复用、时间、评测可靠性”的综合测量工具。

## 与现有 theorem proving benchmark 的关系

现有 benchmark 大致提供了几类重要参照：

| Benchmark | 主要特点 | 我们这 200 题的补充价值 |
|---|---|---|
| miniF2F | 奥赛/竞赛风格，跨 Lean/Metamath/Isabelle/HOL Light，488 个 formal statement。 | 我们不是奥赛题，而是优化、矩阵分析、概率/凸分析等应用数学教材题，更接近研究/工程形式化场景。 |
| ProofNet | 本科数学，包含自然语言 statement、formal Lean 3 theorem、自然语言 proof，371 例。 | 我们更偏 Lean 4.28 下的完整证明工程和 agent 运行结果审计，并保留耗时、失败原因、人工审核。 |
| PutnamBench | Putnam 竞赛题，640 个 theorem、约 1697 个多语言 formalization，强调难度和跨系统。 | 我们规模较小但更细粒度记录 agent 过程：成功/失败、耗时、原始 status 噪声、bad_statement 分析、可修题。 |
| LeanDojo Benchmark | 从 mathlib 抽取约 10 万 theorem/proof，强调 premise selection、retrieval、repository-aware proving。 | 我们不是从已有库抽定理，而是来自一批待补证明的 problem 文件；更能测试从 problem statement 到可编译证明的端到端修复能力。 |

由此可以把我们的 benchmark 定位为：

> A human-audited Lean 4 benchmark for textbook-style convex optimization and matrix-analysis formalization, measuring not only proof completion but also statement validity, repairability, cross-problem reuse, and solve-time dynamics.

这个定位避开了“我们比 miniF2F/PutnamBench 更难或更好”的不必要比较，而是强调互补维度。

## 当前结果里对 benchmark 有利的信号

### 1. 难度处在有信息量的区间

如果一个 benchmark 太容易，所有系统都接近满分；太难，所有系统都接近 0，二者都不利于分析。当前结果比较理想：

- m2f：173/200 成功。
- aristotle 人工审核：164/200 成功。
- 两者共同成功：153/200。
- 至少一个成功：184/200。
- 两者共同失败：16/200。

这说明它不是饱和 benchmark：既有大量可解题用于比较工程吞吐，也有明确 hard core 用于长期进展。

### 2. 可以自然分层，而不是只给一个总分

从现有分析看，至少能分出四个子集：

- clean-solvable subset：两者都能做出的 153 题，适合测 proof engineering 和速度。
- complementary subset：m2f 独有成功 20 题、aristotle 独有成功 11 题，适合测不同策略的互补性。
- hard-infrastructure subset：共同失败 16 题，适合长期跟踪 mathlib/agent 能否补齐深定理。
- statement-audit subset：m2f 报 `bad_statement*` 的 14 题，适合测发现 false statement、构造反例、提出修正条件的能力。

这个分层本身就是 benchmark 价值。很多 benchmark 只给 pass/fail，而这批题能把失败拆成“证明没做完”“题目有问题”“编译有错”“评测状态噪声”“需要跨题复用”等不同原因。

### 3. 人工审核暴露了自动 status 的噪声

aristotle 原始 status 与人工审核冲突 38/200：

- 原始 COMPLETE 但人工 no：8 题。
- 原始非 COMPLETE 但人工 yes：30 题。

这对 benchmark 论文是有利结果：它说明我们不能只做“API status benchmark”，必须做 Lean-level validation 和 human audit。这可以成为方法论贡献：

- 自动 status 是弱标签。
- 编译检查、无 `sorry/sorryAx`、statement preservation、人工审题是强标签。
- Benchmark 发布时应同时给 raw outputs 和 audited labels。

### 4. 跨题 import 是一个需要明确标注的现实能力

aristotle 是逐题隔离；m2f 可以 `import` 其他 problem。这会影响成功率和耗时，但不一定是缺点。它反映两种不同评测 setting：

- isolated-problem setting：每题独立，不允许看其他题；更接近传统 contest benchmark。
- batch/library-building setting：同一批题可积累 lemma、复用基础设施；更接近真实 Lean 项目。

对我们有利的说法是：这个 benchmark 同时支持两种设置。若评测单题能力，可以禁止跨题 import；若评测库建设能力，可以允许 import 并记录依赖图。这样 benchmark 比单一设置更丰富。

## 正确率随时间变化图是否合理

合理，而且很适合凸显 benchmark 价值，但图的口径要设计好，避免被解读成单纯模型强弱。

推荐画法：

### 图 1：Anytime solve curve

横轴：时间阈值，例如 0.5h、1h、2h、4h、8h、12h、24h、48h。  
纵轴：在该时间阈值内已经成功的题数或成功率。

每个 agent 一条曲线：

- m2f：用 `minutes_total`，成功定义为 `reason_group == done`。
- aristotle：用人工审核 `yes*`，时间用 `精确记录.md` 的 `用时`。

这张图的价值：

- 显示 benchmark 的“anytime”性质：给更多时间能多解多少题。
- 显示长尾：哪些系统前期快、后期是否继续增长。
- 比单个总分更有信息。

但图注必须说明：

- aristotle 是 isolated setting。
- m2f 是 batch/library-building setting，且时间来源包括 `reported/history_log_sum/log_sum`。
- 因此曲线用于展示 benchmark 诊断能力，不作为严格同条件模型排名。

### 图 2：分层 anytime curve

更推荐在主图之外加分层曲线：

- all 200。
- clean subset：排除 `yes -xiu`、bad-statement、编译有错等题。
- hard-infrastructure subset：共同失败 16 题。
- statement-audit subset：m2f `bad_statement*` 14 题。

这样可以避免总曲线混合不同现象。比如 m2f 在 `<30m` 很高，可能来自跨题复用和快速工程修复；aristotle 在长时间后失败多，可能来自单题隔离下缺基础设施。分层后更容易解释。

### 图 3：失败类型随时间堆叠图

横轴同样是时间桶，纵轴为题数，颜色表示：

- success。
- remaining sorry。
- compile error。
- bad_statement。
- raw status mismatch。
- failed/no summary。

这张图更能凸显 benchmark 的质量：它展示的不只是“没做出来”，而是“为什么没做出来”。

## 为什么正确率随时间图对我们有利

这张图能突出几个结果：

1. m2f 很快解决大量题，说明 benchmark 有足够多工程型题，能测吞吐。
2. aristotle 分布更平滑，说明 isolated single-problem setting 下题目难度有自然梯度。
3. 两者长尾都存在，说明 benchmark 不饱和。
4. m2f 的极端分布说明 batch/library-building setting 与 isolated setting 的差异，这正好支持我们提出“双设置评测”的必要性。
5. 如果画 union curve，还能显示两个 agent 的互补性：单 agent 最高 173/200，但 union 是 184/200，说明 benchmark 能区分策略而非只给单一排名。

## 建议在论文/报告里的表达

可以用下面几句话作为主张：

1. Existing benchmarks emphasize cross-system formal statements, competition mathematics, undergraduate theorem proving, or repository-scale premise selection. Our benchmark complements them with human-audited Lean 4 proof-repair tasks from textbook-style optimization and matrix analysis.
2. The benchmark is intentionally diagnostic: each problem is labeled not only by success/failure, but also by failure mode, solve time, raw-status reliability, and whether the statement required repair.
3. The observed results show the benchmark is neither saturated nor impossible: 153 problems are solved by both agents, 31 are solved by exactly one, and 16 remain unsolved by both.
4. The gap between raw status and human audit shows that formal theorem proving benchmarks should report Lean-level validation rather than API-level completion alone.
5. Time-to-solve curves are a better summary than pass rate alone, because they reveal quick engineering wins, long-tail theorem infrastructure gaps, and the distinction between isolated-problem and batch-library settings.

## 参考资料

- miniF2F: a cross-system benchmark for formal Olympiad-level mathematics, ICLR 2022 / arXiv 2109.00110. https://github.com/openai/miniF2F and https://huggingface.co/papers/2109.00110
- ProofNet: Autoformalizing and Formally Proving Undergraduate-Level Mathematics, arXiv 2302.12433. https://huggingface.co/papers/2302.12433
- PutnamBench: Evaluating Neural Theorem-Provers on the Putnam Mathematical Competition, arXiv 2407.11214. https://huggingface.co/papers/2407.11214
- LeanDojo: Theorem Proving with Retrieval-Augmented Language Models, NeurIPS 2023 Datasets and Benchmarks. https://papers.nips.cc/paper_files/paper/2023/hash/4441469427094f8873d0fecb0c4e1cee-Abstract-Datasets_and_Benchmarks.html
- miniF2F-Lean Revisited: Reviewing Limitations and Charting a Path Forward, arXiv 2511.03108. https://huggingface.co/papers/2511.03108
