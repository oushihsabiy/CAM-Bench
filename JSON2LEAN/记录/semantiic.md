# 语义检查统计记录

## 统计范围

- 语义失败流：/root/workspace/benchmark/JSON2LEAN/logs/failure_reports/realtime_failures.jsonl
- 语义审查报告：/root/workspace/benchmark/JSON2LEAN/review_log
- 语义审查规则：/root/workspace/benchmark/JSON2LEAN/prompts/fixer/semantic_review.md
- 统计时间：2026-05-02

本次统计采用“每个声明取最后一次语义审查结果”的口径。

根据 semantic_review.md 的判定规则：

- usable：issues 为空，判定通过
- usable_with_revision：只有 P2 问题
- not_usable_yet：存在任意 P0 或 P1 问题，判定未通过

当前 review_log 中最终状态只有 usable 和 not_usable_yet，因此最终通过率按 usable 计算。

## 总体结果

- review_log 总审查记录数：7366
- 去重后声明数：2531
- 最终通过数：1899
- 最终未通过数：632
- 最终语义通过率：1899 / 2531 = 75.03%
- 最终语义未通过率：632 / 2531 = 24.97%

补充口径：如果把所有中间轮次也算进去，则

- 所有轮次通过数：2142
- 所有轮次未通过数：5224
- 轮次级通过率：2142 / 7366 = 29.08%

说明：29.08% 更接近“单次审查命中率”，不应替代最终通过率；最终通过率应以每个声明最后一次结果为准。

## 最终失败项的问题类型分布

以下统计对象为最终 not_usable_yet 的 632 个声明。

- 含 task_drift 的失败声明：623，占失败声明的 98.58%
- 含 missing_assumption 的失败声明：153，占失败声明的 24.21%
- 含 wrong_boundary_case 的失败声明：13，占失败声明的 2.06%

按最终 issue 条目数统计：

- task_drift：816
- missing_assumption：172
- wrong_boundary_case：13

按最终 severity 统计：

- P0：421
- P1：579
- P2：1

结论：主要丢失原因不是 Lean 编译层面的语法错误，而是声明与源注释之间的语义不一致，核心问题是 task_drift。

## 主要失败原因归纳

基于 review_log 中 summary、issues 和 top_priority_fix 的聚合，最终失败声明的高频原因如下：

1. 整体语义漂移：624
2. 量词或逻辑形状不一致：228
3. 审查输出无效，要求重新返回合法 JSON：182
4. 边界、不等式、索引范围错误：108
5. 只编码了注释的一部分，遗漏关键结论或定义：103
6. 形式化对象选错，和原题不是同一个数学对象：67
7. 占位式或空洞命题替代真实语义：46
8. 缺少源注释要求的前提或假设：19

这些高频原因和 semantic_review.md 的检查重点一致，尤其集中在以下几类：

- 缺少源注释要求的假设或 side condition
- 量词错误、逻辑方向错误
- 对象或类型选错，导致 formalization 与原题不同
- 边界条件、索引范围、不等式处理错误

## 对“哪里有问题”的直观解释

从失败样例看，语义主要在下面几类地方丢失：

### 1. 原题要表达的命题被改写成了别的命题

这是最主要的问题。常见表现：

- 原题要证明一个具体结论，结果 Lean 里变成了弱化版包装结构
- 原题讨论的是某个固定对象，Lean 里换成了更泛的另一个对象
- 原题要求等价、唯一性、最优性，Lean 里只保留了存在性或某个局部性质

### 2. 量词、逻辑方向、条件句丢了

常见表现：

- 把“存在”写成“任意”
- 把“当且仅当”写成单向蕴含
- 漏掉必要 binder constraint
- 多引入原题没有的自由参数

### 3. 关键前提被漏掉

常见表现：

- 漏掉正定、非零、可逆、可行性、一致性、边界点之类的前提
- 结论本身没问题，但少了这些前提后，命题就比原题更强，不再忠实

### 4. 边界条件和索引处理不准确

常见表现：

- 最后 m-r 个分量被写成了从 r 开始全部为零
- 严格不等式和非严格不等式混用
- 取值范围、索引范围、边界 case 写偏

### 5. 用占位式命题代替真实数学条件

典型危险信号：

- 把关键条件替换成恒真式，例如存在 lam 使得 0 ≤ 0
- 把目标替换成和原题无关的固定假命题
- 表面上结构完整，但核心数学约束并没有被表达出来

## realtime_failures.jsonl 中的语义失败分布

realtime_failures.jsonl 中识别出的语义相关失败事件共有 739 条，分布如下：

- semantic_not_usable_after_max_rounds：375，占 50.74%
- semantic_rewrite_no_output：262，占 35.45%
- semantic_rewrite_recovery_failed：81，占 10.96%
- semantic_block_not_found：19，占 2.57%
- semantic_rewrite_empty：2，占 0.27%

说明：

- 一半以上是多轮修复后仍未达到 usable
- 另有相当比例是语义重写阶段根本没有产出有效内容
- 因此“被丢掉”既包含真实语义错配，也包含语义修复链路本身的不稳定

## 简要结论

当前生成 Lean 之后的最终语义通过率约为 75.03%。

剩余 24.97% 的主要损失并不集中在语法或编译，而是集中在“形式化内容和源注释不一致”，其中最主要的是：

- task_drift
- 量词和逻辑形状错误
- 关键条件遗漏
- 边界和索引处理错误
- 审查或修复阶段输出无效 JSON 或无输出

如果后续要提高通过率，优先级应放在：

1. 降低 task_drift，确保声明表达的是原题本身而不是邻近命题
2. 强化量词、逻辑方向、条件句的保真
3. 针对常见 missing_assumption 建立检查模板
4. 稳定 semantic rewrite 的 JSON 输出和 block 定位




```tex
\subsection{Sources and scope.}
Our benchmark targets optimization-centric applied mathematics, a domain that
remains underrepresented in existing Lean-based formal reasoning benchmarks.
Recent datasets have expanded the scale and diversity of formal mathematics
evaluation. FormalMATH, for example, provides broad Lean~4 coverage over
olympiad problems and undergraduate mathematics across algebra, calculus,
number theory, discrete mathematics, and applied mathematics
\cite{yu2025formalmath}. Our benchmark instead adopts a domain-specific focus
on optimization problems drawn from textbook-style learning materials.

The source material is drawn from Boyd and Vandenberghe's \emph{Convex
Optimization} \cite{boyd2004convex}, textbook exercises in numerical
optimization \cite{nocedal1999numerical}, and Wen Zaiwen's optimization
modeling materials. This source choice is important because, unlike
library-extracted theorem collections, textbook exercises often contain
implicit assumptions, modeling context, references to equations or previous
results, proof hints, reformulation goals, and algorithmic descriptions. As a
result, the benchmark evaluates not only Lean proof completion, but also the
ability to reason over optimization problems after they have been converted
into self-contained and semantically faithful formal statements.

\subsection{Distribution.}
\paragraph{Main topical groups.}
The benchmark's distribution reflects this optimization-centered design. Its
largest component is convex analysis and generalized convexity (26.4\%),
including convexity and concavity verification, epigraphs, perspectives,
conjugates, support functions, separation, and closure properties. The second
largest component is conic, semidefinite, and spectral matrix optimization
(20.1\%), covering PSD cones, Loewner order, Schur complements, trace
inequalities, determinant and log-determinant objectives, and SDP
formulations. Another 14.5\% focuses on linear, quadratic, norm-based, and
approximation reformulations, including LP, QP, QCQP, SOCP, least-squares,
Chebyshev approximation, and epigraph transformations. Nonlinear programming,
KKT theory, active sets, and constraint qualifications account for 11.5\%.
Together, these groups show that the benchmark is centered on formal reasoning
about objectives, feasible sets, constraints, dual variables, matrix
inequalities, and equivalent optimization formulations.

\paragraph{Cross-cutting labels.}
A finer-grained view highlights the benchmark's applied-mathematics character.
More than half of the tasks involve convexity, concavity, log-concavity, or
quasiconvexity (57.4\%). Substantial portions involve LP/QP/QCQP/SOCP and norm
or least-squares reformulations (24.3\%), existence, boundedness, closure, and
certificates (21.4\%), SDP and PSD/PD matrix inequalities (19.0\%), and
spectral, trace, determinant, or log-determinant reasoning (13.7\%). The
benchmark also covers cones and generalized inequalities, statistical
estimation and likelihood models, KKT systems, robust and inverse
optimization, Lagrange duality, Newton-type methods, line search, barrier
functions, network models, and resource allocation. These overlapping labels
reflect a core feature of optimization: a single problem often combines
convexity, matrix analysis, duality, certificates, and reformulation
equivalence.

\subsection{Curation attrition.}
\paragraph{Acceptance standard.}
Our goal is not to maximize the number of retained exercises, but to construct
a semantically reliable Lean benchmark from textbook-style optimization
problems. Since such exercises often contain implicit assumptions, contextual
references, open-ended instructions, and informal modeling descriptions,
direct extraction is insufficient. We therefore analyze construction loss on
the audited subset with complete branching records and use it to characterize
how the pipeline filters a high-recall textbook extraction stage into
Lean-ready benchmark items.

The main loss occurs during semantic filtering rather than extraction. After
the first review round, only 24.3\% of reviewed items are accepted. This
acceptance rate reflects a strict retention criterion: an item is kept only if
it preserves the original mathematical task, contains the necessary
assumptions and definitions, is self-contained, and can serve as a precise
Lean theorem target. Many textbook exercises are mathematically meaningful but
fail this standard initially because they are open-ended, underspecified,
context-dependent, or not yet theorem-like.

\paragraph{Dependency-related rejection.}
Dependency handling is deliberately conservative. Although the pipeline performs
dependency completion before review, this step only folds dependencies that can
be recovered from explicit references, nearby context, or validated dependency
chains. If an item still requires unavailable chapter context, previous
exercises, or unstated definitions after this stage, we treat it as a hard
rejection rather than a repair target. We avoid speculative reconstruction,
because it could introduce unsupported assumptions, change the mathematical
task, or make the benchmark appear more complete than the source evidence
justifies.

\paragraph{Loss profile and bounded repair.}
The first-round loss profile supports this interpretation. Among held items,
65.1\% are blocked by unsuitable Lean phrasing, 21.7\% by missing
dependencies, and 13.2\% by parse errors. Among revised items, the dominant
issues are task drift (48.5\%) and missing definitions (47.1\%). Thus, the
bottleneck is not surface formatting, but the stricter requirement that each
problem be faithful to the source, self-contained, and formalizable.

To improve coverage without contaminating the dataset, each recoverable item
receives only one repair-and-review round. This repair is limited to bounded
local changes, such as converting open-ended exercise wording into theorem-style
statements, completing missing definitions, or correcting minor semantic
alignment issues. It raises the usable yield from 24.3\% to 60.7\%. However,
any item that remains non-accepted after this single pass is discarded. This
policy intentionally sacrifices recall for precision, limiting repeated
model-driven rewriting, unsupported answer embedding, reviewer overfitting,
and gradual task drift.

\subsection{Semantic reliability.}
\paragraph{Informal-level semantic fidelity.}
Since our benchmark is derived from textbook exercises rather than pre-existing
formal libraries, semantic fidelity is the central validity concern of the
dataset. A Lean declaration with \texttt{sorry} can be syntactically
well-formed while still failing to preserve the source exercise. We therefore
evaluate semantic fidelity before using an item as a benchmark target.

Our construction process is designed as conservative curation rather than
automatic generation. The preprocessing stages remove hints, remarks, and
background exposition while preserving mathematical symbols, assumptions,
references, formulas, and task objectives. The dependency-completion stage is
also evidence-bounded: it may add definitions, assumptions, or local context
only when they are supported by the standardized problem statement, nearby
context, or validated reference chains. It is not allowed to solve the
problem, change the task objective, introduce stronger assumptions, or
reconstruct missing context speculatively.

Each candidate \texttt{problem\_finally} is then reviewed against the original
textbook exercise. The review checks four core properties: assumption
preservation, task preservation, self-containedness, and Lean suitability.
Concretely, it flags lost or changed assumptions, altered quantifiers, changed
logical directions, shifted domains, dropped or added conclusions, unresolved
dependencies, missing definitions, and tasks that remain unsuitable as precise
Lean theorem targets. Hints, remarks, motivational text, and background
exposition are explicitly ignored as non-target material.

\paragraph{Repair and rejection policy.}
The review assigns items to \texttt{accept}, \texttt{revise}, or
	exttt{hold}. An item is accepted only when it is faithful to the source
problem, self-contained, mathematically well-specified, and suitable as a Lean
theorem target. Items with locally fixable issues, such as missing definitions,
missing assumptions, or bounded semantic misalignment, are sent to
	exttt{revise}. Items that remain open-ended, dependency-heavy, parse-failed,
or not yet theorem-like are assigned to \texttt{hold}. Remaining
missing-dependency cases are treated as hard rejections: if the required
context cannot be recovered with sufficient textual evidence, the item is
discarded rather than reconstructed speculatively.

Repair is not itself an acceptance step. The \texttt{revise} repair is
constrained to rewrite only \texttt{problem\_finally}, using the
reviewer-provided reasons and suggestions while preserving the original
mathematical meaning and leaving all other source fields unchanged. The
	exttt{hold} repair handles mathematically meaningful but non-theorem-like
exercises, such as prompts phrased as ``find'', ``compute'', ``determine'',
``describe'', or ``formulate''. It may convert them into explicit theorem-style
statements, inline necessary definitions, remove purely non-formalizable
subgoals such as plotting or sketching, or discard inherently non-formalizable
tasks. Every repaired item is reviewed again before it can enter the benchmark.

This second review is especially important for answer-embedding repairs. For
value-finding or condition-finding exercises, repair may convert an open-ended
prompt into a statement such as ``prove that the value is ...'' or ``prove that
the condition is ...''. The post-repair review must verify that the embedded
conclusion is mathematically correct and faithful to the original task. For
``determine whether'' or ``prove or give a counterexample'' tasks, the review is
counterexample-aware: the repaired statement must choose the correct
mathematical side. A false universal claim, missing counterexample,
unsupported embedded answer, strengthened assumption, weakened conclusion, or
changed task is rejected rather than retained.

\paragraph{Lean-level semantic validation.}
After JSON-to-Lean translation, we run a separate semantic validation stage to
check whether each Lean declaration preserves the reviewed informal target.
This stage is necessary because Lean compilation verifies syntactic and
type-theoretic well-formedness, but a declaration may still compile while
changing the original mathematical task.

Using the final review result for each declaration, the current audit snapshot
contains 2,531 deduplicated Lean declarations. Among them, 75.03\% are finally
classified as usable, while 24.97\% remain not usable yet. We use this
per-declaration final status as the main statistic. Counting all intermediate
rounds gives a much lower pass rate of 29.08\%, which reflects the difficulty
of individual repair attempts rather than the final retained benchmark yield.

The remaining semantic failures are dominated by task drift: 98.58\% of final
not-usable declarations contain task drift, 24.21\% contain missing
assumptions, and 2.06\% contain boundary-case errors. Typical failures include
changing the target theorem into a nearby statement, altering quantifiers or
logical direction, weakening equivalences, omitting side conditions,
mishandling boundary or index cases, and introducing vacuous placeholder
propositions.

\paragraph{Manual audit.}
Because the review process is model-assisted, we additionally conduct a
stratified manual audit over first-pass accepted items, repaired-and-accepted
items, discarded items, and a stratified sample of automatically accepted Lean
targets. The audit checks whether the final statement preserves the original
mathematical goal, keeps all necessary assumptions, avoids unsupported
strengthening or weakening, resolves definitions and dependencies, and remains
suitable for Lean formalization. Declarations that remain non-usable after
eight semantic review-and-repair attempts are sent to manual inspection rather
than automatically retained. This combines automatic semantic validation with
human inspection and reduces the risk that the released benchmark contains
declarations that are well-typed but semantically misaligned.


\subsection{Benchmark sources and domain coverage}
Existing formal mathematics benchmarks have covered a range of evaluation
settings, including olympiad problems, undergraduate mathematics, Putnam
problems, large-scale Lean theorem collections, and specialized domains such as
algebra and combinatorics. Our benchmark targets optimization-centric applied mathematics,
a domain that remains underrepresented in existing Lean-based formal reasoning benchmarks.

The benchmark is built from classical optimization textbooks and course
materials, including \emph{Numerical Optimization} \cite{nocedal1999numerical}, \emph{Convex Optimization} \cite{boyd2004convex}, and its accompanying exercise
materials, solutions manual, and additional exercises, as well as optimization modeling course materials from \emph{Optimization: Modeling, Algorithm and Theory}. These sources cover representative topics in convex optimization, numerical optimization, and optimization modeling.

After dependency completion, semantic review, and Lean formalization, the benchmark contains 803 self-contained textbook exercises in optimization,
corresponding to 1100 Lean proof targets. The number of exercises and the
number of Lean targets differ because a textbook exercise may contain multiple
subquestions, multiple conclusions, or several theorem-level claims after formal decomposition.

In terms of primary domain distribution, convex analysis and generalized
convexity account for 26.4\%, including convexity and concavity verification,
epigraphs, perspectives, conjugates, support functions, separation properties,
and closure properties. Conic, semidefinite, and spectral matrix optimization
account for 20.1\%, including positive semidefinite (PSD) cones, Loewner order, Schur complements,
trace inequalities, determinant and log-determinant objectives, and semidefinite programming (SDP)
formalizations. Linear, quadratic, norm-based, and approximation
reformulations account for 14.5\%, including linear programming (LP), quadratic programming (QP), quadratically constrained quadratic programming (QCQP), second-order cone programming (SOCP),
least-squares, Chebyshev approximation, and epigraph reformulation. Nonlinear
programming, Karush--Kuhn--Tucker (KKT) conditions, active sets, and constraint qualifications account
for 11.5\%. The remaining portion is distributed across numerical optimization
algorithms, Lagrange duality, statistical optimization, robust optimization,
inverse optimization, network models, resource allocation, and other
optimization modeling tasks.

Beyond the primary-domain distribution, we also annotate fine-grained
multi-label coverage. More than half of the Lean proof targets involve
convexity, concavity, log-concavity, or quasiconvexity (57.4\%). A substantial
fraction involves LP/QP/QCQP/SOCP, norm-based, or least-squares
reformulations (24.3\%), existence, boundedness, closure properties, and
certificates (21.4\%), SDP and positive semidefinite/positive definite (PSD/PD) matrix inequalities (19.0\%), and
spectral, trace, determinant, or log-determinant reasoning (13.7\%). These
fine-grained labels are non-exclusive,a single problem may simultaneously involve convexity, matrix analysis,
duality, certificate construction, and reformulation equivalence.
```