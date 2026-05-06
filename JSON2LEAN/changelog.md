# Changelog

## 2026-04-22 — realtime_failures 回填 error_problem/errors.json 并在成功后清空实时日志

- **目标**:
  - 运行结束后读取 `logs/failure_reports/realtime_failures.jsonl`（全事件类型）。
  - 基于 `lean_file` 反查 `data/*.json`，再用 `label`/`block_id`/`source_idx+index+kind` 匹配题目。
  - 若题目不在 `error_problem/errors.json` 中，则将题目的完整 JSON 记录追加写入。
  - 回填成功后清空 realtime 日志文件内容（保留文件）。

- **新增文件**:
  - `src/postprocess/error_problem_sync.py`
    - `sync_realtime_failures_to_errors(...)`:
      - 兼容解析两类 realtime 事件结构：`payload`（语义事件）与 `exercise`（编译/翻译失败事件）。
      - 按 `lean_file` 先做候选 data 文件筛选（精确 stem + chapter 模糊匹配），未命中再全量回退。
      - 匹配成功后将 data 中完整题目对象写入 `errors.json`。
      - 使用稳定键去重，避免重复写入。
    - `truncate_realtime_failures(...)`:
      - 将 `realtime_failures.jsonl` 截断为 0 字节。

- **修改文件**:
  - `main.py`
    - 在 Step 8a（failure report export）后新增 Step 8a.1：
      - 调用 `sync_realtime_failures_to_errors(...)` 同步失败题目到 `error_problem/errors.json`。
      - 打印 `events/matched/inserted/existing/unmatched` 统计。
      - 仅在同步步骤未抛异常时调用 `truncate_realtime_failures(...)` 清空 realtime 日志。
      - 若同步失败，仅告警，不清空日志，避免数据丢失。

## 2026-04-22 — 语义修复遇到 unchanged 时继续重试直到成功或达到最大轮次

- **问题**: 语义修复循环中，如果 semantic rewrite 返回的 block 与当前代码完全相同，会打印 `unchanged` 后直接 `break`，提前结束当前 item 的语义修复，导致还没到 `semantic_max_rounds` 就跳到下一个条目。
- **方案**: 调整 `main.py` 中 semantic loop 的控制流，将 `unchanged` 视为本轮未产生有效改写但仍可继续尝试的状态；仅 `empty` 输出保持立即停止，`unchanged` 则继续下一轮 review/rewrite，直到语义修复成功或达到最大轮次。
- **修改文件**:
  - `main.py`
    - 将 `new_chunk == code_chunk.strip()` 分支从 `break` 改为 `continue`
    - 日志文本明确标记为“continue until success or max rounds”

## 2026-04-20 — 去重 fallback 修复：避免跨 namespace 误删同名声明

- **问题**: 在 block 合并去重时，`frozen_context_in_section()` 一旦无法定位 namespace 边界，会 fallback 到 `frozen_context_before()`，把其他 namespace 的历史声明带入去重上下文，导致 `namespace A` 与 `namespace B` 下同名 `def` 被误判重复并删掉后者。
- **方案**: 将 `frozen_context_in_section()` 的 3 个 fallback 分支改为返回空上下文（skip dedup），不再回退到全局前文；并输出 warning 日志用于排查 namespace 命名或边界不匹配。
- **修改文件**:
  - `src/json2lean/block_parser.py`
    - 新增 `sys` 导入用于 warning 输出
    - `frozen_context_in_section()` 在以下场景返回 `""`：
      - 找不到 `namespace <section_name>`
      - 找不到 `end <section_name>`
      - 当前 block 不在该 namespace 边界内
- **测试**:
  - `test/test_block_parser.py`
    - 新增集成测试：`test_replace_block_code_keeps_same_name_in_other_namespace`
    - 新增 fallback 行为测试：`test_frozen_context_in_section_missing_namespace_returns_empty_context`
    - 新增同 namespace 回归测试：`test_dedupe_same_namespace_duplicate_still_removed`
  - 验证结果：`pytest test/test_block_parser.py -q` → `22 passed`

## 2026-04-20 — section → namespace 迁移，解决跨 section 同名定义冲突

- **问题**: Lean 4 的 `section X ... end X` 不创建命名空间，导致不同 section 内的同名 `def`（如 `def isconvex`）在文件级冲突，编译报 "has already been declared"，fixer 会错误删除第二个 section 的定义。
- **方案**: 将有名 `section X ... end X` 替换为 `namespace X ... end X`，利用 Lean 4 namespace 的自动前缀机制隔离定义。`noncomputable section`（无名 section）保持不变。
- **修改文件**:
  - `main.py` — `_build_scaffold()`, `_find_section_bounds()`, `_strip_lean_preamble()`, preamble 正则
  - `src/json2lean/block_parser.py` — `frozen_context_before()`, `frozen_context_in_section()`, `insert_block_comment()`
  - `src/json2lean/postprocess_lean.py` — `_SECTION_RE` 正则
  - `src/postprocess/fault_tolerance.py` — `comment_out_section()` open_pat
  - `src/postprocess/redundancy_cleanup.py` — `section_re` 正则
  - `src/utils/lean_splitter.py` — `section_pattern` 正则
  - `src/json2lean/semantic/build_semantic_review_input.py` — `_TOP_LEVEL_NEXT_RE` 正则
  - `src/json2lean/semantic/semantic_reviewer.py` — `_TOP_LEVEL_NEXT_RE` 正则
  - `prompts/translate/json_to_lean.md` — section wrapper 描述改为 namespace
  - `prompts/fixer/compiling_fixer.md` — Rule 31/35/36/37/38/54 更新为 namespace 语境，Rule 37 增加跨 namespace 说明
  - `prompts/fixer/semantic_review.md` — same-section reuse rule → same-namespace
  - `prompts/fixer/semantic_rewrite.md` — same-section reuse rule → same-namespace
  - `test/test_block_parser.py` — 测试数据 `section X` → `namespace X`
  - `test/test_fault_tolerance.py` — 测试数据 `section X` → `namespace X`

## 2026-04-20 — error_analyzer 新增语义聚类分析

- **`src/utils/error_analyzer.py`**
  - 新增 `_SEMANTIC_RULES`：基于 compile_errors 聚类结果定义的 13 条正则规则，覆盖 λ 保留字、矩阵符号 ⬝、重复声明、Unknown constant、类型不匹配等高频类别。
  - 新增 `_classify_message(msg)` → `(category, detail)`：对单条错误消息进行语义分类。
  - 新增 `classify_errors(log_dir, top_n)` → 按类别聚合的结果列表，含 count / details / examples。
  - CLI 新增 `--semantic` 选项，可切换语义分类输出模式。

## 2026-04-20 — 预处理输出顺序调整：technical-term 在 special block 之前

- **`src/json2lean/preprocess/pipeline.py`**
  - 调整 flat records 拼接顺序：由 `hints -> opt_prob/algo -> defn -> thm` 改为 `hints -> defn -> opt_prob/algo -> thm`。
  - 结果：提取出的 technical-term（`kind="defn"`）在输出 JSON 中会出现在 special block（`kind="opt_prob"/"algo"`）之前。
  - 同步修正文档注释中的阶段顺序描述，保持与实际执行一致（0b 定义提取，1 special-block 提取）。

## 2026-04-19 — 预处理 theorem 输出改为自然语言

- **`prompts/preprocess/construct_theorem.md`**
  - 移除“`content` 必须输出可编译 Lean 片段”的硬约束
  - 新增“`content` 必须为自然语言数学陈述，禁止 Lean 声明/战术代码”的硬约束
  - 保留原有占位符替换、分题拆分、变量名不替换、可见源内容完整保留等规则
  - 目的：让 `preprocessed_data/*.json` 中 `kind="thm"` 的 `content` 回归自然语言，Lean 代码生成留在后续翻译阶段

## 2026-04-18 — 编译修复时比对常见错误（支持开关控制）

- **`src/json2lean/models.py`**
  - 新增 `PipelineConfig.recovery_use_common_errors: bool = True` 配置字段
  - `from_dict` 方法中从 recovery 配置读取 `use_common_errors` 选项

- **`settings.json`**
  - 在 recovery 部分添加 `"use_common_errors": true` 开关（默认启用）

- **`src/json2lean/compile/compiling_fixer.py`**
  - `recover_exercise` 新增 `use_common_errors: bool = True` 参数
  - `recover_all` 新增 `use_common_errors: bool = True` 参数，在调用 `recover_exercise` 时传递
  - 修改 `_load_common_errors()` 的加载逻辑，仅当 `use_common_errors=True` 时才加载

- **`main.py`**
  - 两处 `recover_all` 调用均添加 `use_common_errors=cfg.recovery_use_common_errors` 参数

**使用说明**：在 `settings.json` 中 recovery 部分修改 `"use_common_errors": false` 可关闭常见错误提示。

## 2025-07-25 — 专有名词提取重构：重命名、调序、重写 prompt

- **`prompts/preprocess/extract_definition.md` → `extract_technical_term.md`**（重命名）
  - 只提取优化领域专有名词（如 "strongly convex"、"Armijo condition"），排除通用数学词汇（domain、function、set 等）和题目局部对象。
  - 新增两步提取流程：Pass 1 提取文中有严格定义的术语（`source: "in_text"`），Pass 2 为文中使用但未定义的术语补充标准定义（`source: "standard"`）。
  - 添加明确的"什么算/什么不算技术术语"判断标准和 key test。
- **`src/json2lean/preprocess/pipeline.py`**
  - 调换阶段顺序：专有名词提取（Stage 0b）现在在特殊块提取（Stage 1）之前执行。
  - 专有名词提取的输入从 `original_text` 改为 `hint_masked_text`。
- **`src/json2lean/preprocess/_common.py`**
  - `PROMPT_NAMES["definition"]` 值从 `"extract_definition"` 改为 `"extract_technical_term"`。
- **`src/json2lean/preprocess/definition.py`** — 更新模块和函数 docstring，反映新阶段编号和输入源。
- **`src/json2lean/preprocess/__init__.py`** — 更新阶段注释（0a → 0b → 1 → 2 → 3）。
- **`src/json2lean/preprocess/validators.py`** — 新增对 `source` 字段的可选验证（值须为 `"in_text"` 或 `"standard"`）。
- **`src/json2lean/preprocess/PIPELINE.md`** — 全面更新文档，反映新阶段顺序、新文件名、新输入源和两步提取逻辑。

## 2026-04-17 (续) — construct_theorem.md 强化原文保留规则与定理完整性

- **`prompts/preprocess/construct_theorem.md`**
  - 强化"Natural-language repair rules"：新增 CRITICAL 级别的规则，明确禁止替换、重命名或改变任何数学变量或符号。
  - 新增第6条硬约束（HARD CONSTRAINT）：禁止任何变量或符号替换。确保定理与原文完全一致，只有在语义不通顺时才进行修改。
  - 修改"Multi-part splitting"中的定理完整性要求：将 "include all necessary setup, definitions, and assumptions" 改为 "include all setup, definitions, and assumptions (whether necessary or not)"。
    - 目的：确保每个定理项都包含完整的设置和定义，提高定理的独立性和可读性。

## 2026-04-17 (续) — viewer LaTeX itemize 环境支持

- **`viewer/app.js`**
  - 新增 `processItemizeEnvironments(text)` 函数，递归处理 LaTeX `\begin{itemize}...\end{itemize}` 环境（支持嵌套）。
  - 修改 `renderMathText()` 函数，集成 itemize 处理：
    1. 预处理文本中的 itemize 环境，转换为 HTML `<ul>` / `<li>` 结构；
    2. 使用占位符机制避免转义冲突；
    3. 保留数学内容的 `$...$` / `\(...\)` 定界符，由后续 KaTeX 渲染。
  - `\item` 列表项中的数学公式仍可正常通过 KaTeX 渲染。

- **`viewer/styles.css`**
  - 新增 `.unit-text ul` / `ul ul` / `ul ul ul` 和 `.unit-text li` 样式，实现多层列表嵌套支持。
  - 列表层级缩进与符号：第一层 disc（●）、第二层 circle（○）、第三层 square（■）。

- 验证
  - 通过 `node --check viewer/app.js` 语法检查。

## 2026-04-17 (续) — viewer 左侧 PDF 导出优化

- **`viewer/app.js`**
  - 修改 `exportPanelPdf(side)` 函数：左侧（`side === 'left'`）PDF 导出现仅包含 **problem** 块内容；右侧保持不变，仍导出整个面板。
  - 右侧导出保留对面板长度自动调整的处理（设置 `height: auto` 等）。

- 验证
  - 通过 `node --check viewer/app.js` 语法检查。

## 2026-04-17 — viewer 渲染与 图片导出增强（JPG）

- **`viewer/app.js`**
  - 将面板导出格式由 PDF 更改为 JPG：`exportPanelPdf(side)` 现在导出 `.jpg` 文件；左侧只导出 `problem` 块，右侧导出整个面板。
  - 导出图片质量默认为 92%（`image/jpeg`，quality=0.92）。

- 验证
  - 通过 `node --check viewer/app.js` 语法检查。

## 2026-04-17 — viewer 渲染与 PDF 导出增强

- **`viewer/index.html`**
  - 新增 `html2canvas` 与 `jsPDF` CDN 依赖。
  - 工具栏新增 `Left PDF` / `Right PDF` 按钮，支持左右面板分别导出。

- **`viewer/app.js`**
  - `unit` 视图左侧卡片新增 `Direct Answer` 区块，并补充 `Additional Fields` 区块，确保题目对象内其它字段（如 `题目类型`、`预估难度`、`source`、`index` 等）也可见。
  - `source_idx` 匹配逻辑从“仅精确匹配”扩展为“先精确后宽松匹配”，可兼容 `Exercise 11.9` / `exercise_11_9` / `exercise-11-9` 等格式差异。
  - 新增 `exportPanelPdf(side)`：导出当前渲染结果为 PDF，支持跨页分页；左/右面板均可单独导出。

- 验证
  - 通过 `node --check viewer/app.js` 语法检查。

## 2026-04-16 (续) — 新增 Lean 文件拆分工具

- **`src/utils/lean_splitter.py`**：新增 Lean 文件拆分脚本，按 section 将原始 Lean 文件拆分为独立文件
  - 每个原始文件对应一个输出文件夹（以文件名命名）
  - 每个 `section` 生成一个单独的 `.lean` 文件
  - 自动在生成的文件头添加 `import Mathlib` 和 `noncomputable section`
  - 支持命令行参数指定输入/输出目录
  - 默认输入：`json2lean/lean/LeanProject`，默认输出：`LEAN/LeanProject`
- **`src/utils/LEAN_SPLITTER_README.md`**：添加使用说明文档
- 用法：`python3 lean_splitter.py` 或 `python3 lean_splitter.py --input-dir INPUT --output-dir OUTPUT`

## 2026-04-16 (续) — 统一编译日志落盘到 logs/compile_errors

- **`main.py`**：将管道中的所有直接 `compile_lean_file(...)` 调用统一替换为 `_compile_and_log(...)`，覆盖以下路径：
  - resume-only 校验
  - 翻译阶段逐题校验
  - baseline combined file 校验
  - final combined file 校验
  - semantic rewrite 后校验
  - block/section recovery 后校验
- 为各编译点增加 `run_label`（如 `baseline_combined_file`、`final_combined_file`、`semantic_rewrite_*`），便于在 `logs/compile_errors/*.jsonl` 中按阶段追踪错误来源。
- 结果：运行主流程时，编译结果（含错误/警告）将持续汇总到 `logs/compile_errors`。

## 2026-04-16 (续) — 全面检查与修复

- **`src/postprocess/__init__.py`**：新建缺失的包初始化文件。
- **`src/postprocess/fault_tolerance.py`**, **`math_comment_render.py`**：将错误的相对导入 `from ..json2lean.xxx` 改为绝对导入 `from json2lean.xxx`，修复 `ImportError`。
- **`main.py`**：`tag_preprocess_failure` 此前已导入但未使用，现已在预处理失败后调用，为失败的 exercise 写入失败元数据。
- **`test/test_fault_tolerance.py`**：导入路径从 `json2lean.fault_tolerance` 等改为 `postprocess.*`；删除依赖已移除函数 `cluster_error_messages` 的 `test_error_clustering` 测试。
- 所有 11 项测试 + 冒烟测试通过。

---

## 2026-04-16 — 管道重构：exercise-first、永不中断、后处理与错误分析

### 核心变更

#### 1. 永不中断执行 (fault-tolerance)
- **`main.py`**: 移除所有 `halted = True; break` 模式，改为：
  - 标记 exercise 为 `UNRECOVERABLE` + 注释掉对应 Lean block + `continue`
  - 翻译失败时在 Lean 文件中写入失败标注 + `continue`
  - 预处理失败时在 exercise JSON 中记录错误 + `continue`
- **`src/json2lean/models.py`**: 新增 `ExerciseStatus.UNRECOVERABLE` 状态及失败元数据字段 (`failure_type`, `failure_phase`, `failure_message`, `failure_exception`)
- **新增 `src/json2lean/fault_tolerance.py`**:
  - `annotate_lean_failure()`: 在 Lean 文件中标注失败 block（原代码行注释）
  - `comment_out_block()`: 注释掉不可修复 block 的代码区域
  - `comment_out_section()`: 注释掉整个 section
  - `tag_preprocess_failure()` / `tag_translation_failure()` / `tag_unrecoverable()`: 标记失败类型

#### 2. 后处理管道 (post-processing)
- **新增 `src/json2lean/failure_report.py`**: 按失败类型分组导出 JSON 报告 (`YYYYMMDD_<type>.json`)
- **新增 `src/json2lean/redundancy_cleanup.py`**: 去除重复 import/open/variable 声明
- **新增 `src/json2lean/math_comment_render.py`**: TeX → Lean Unicode 注释转换（规则 + LLM）

#### 3. 编译错误日志与分析 (src/utils/)
- **新增 `src/utils/compile_logger.py`**: 每次编译记录结构化 JSONL 日志
- **新增 `src/utils/error_analyzer.py`**: 高频错误模式分析（归一化 + 模糊聚类），CLI 命令：`python -m utils.error_analyzer`

#### 4. 测试
- **新增 `test/test_fault_tolerance.py`**: 12 项测试覆盖上述所有新功能

### 文件清单
- 修改: `main.py`, `src/json2lean/models.py`
- 新增: `src/json2lean/fault_tolerance.py`, `src/json2lean/failure_report.py`, `src/json2lean/redundancy_cleanup.py`, `src/json2lean/math_comment_render.py`
- 新增: `src/utils/__init__.py`, `src/utils/__main__.py`, `src/utils/compile_logger.py`, `src/utils/error_analyzer.py`
- 新增: `test/test_fault_tolerance.py`

## 2026-04-15 — 去重增加注释相关性LLM守卫（相关则保留）

### 变更
- **`src/json2lean/block_parser.py`**
  - 为 `dedupe_block_code_against_frozen()` 新增可选回调参数 `keep_if_related(kind, removed_text)`。
  - 去重前对每个候选删除片段进行守卫判断：
    - 返回 `True`：保留（不删除）
    - 返回 `False`：允许删除
  - 对回调异常采用保守策略：默认保留候选片段，避免误删与注释相关内容。
  - 为 `replace_block_code()` 透传新增 `keep_if_related` 参数。
  - 新增 `extract_block_comment_text()`，用于按 `block_id` 提取块注释文本，供相关性判定使用。

- **`main.py`**
  - 在 `run_pipeline()` 中新增 LLM 判定函数 `_dedupe_keep_if_related_by_llm()`：
    - 输入：`block_id`、块注释、候选删除片段（声明/命令）
    - 输出：是否相关（相关则保留）
    - 使用 `APIClient.chat(..., json_mode=True)`，`call_type="dedupe_relevance_check"`
  - 增加判定缓存 `dedupe_relevance_cache`，避免重复请求。
  - 在语义改写去重与 block-scoped recovery 去重两条路径接入该守卫。
  - 扩展 `_run_semantic_loop_on_combined_file()` 与 `_recover_combined_file_for_item()` 签名，支持注入 `dedupe_relevance_checker`。

- **`test/test_block_parser.py`**
  - 新增测试 `test_dedupe_guard_keeps_related_declaration`：相关声明不应被去重删除。
  - 新增测试 `test_dedupe_guard_allows_unrelated_declaration_removal`：无关重复声明可被删除。

### 验证
- 运行：`test/test_block_parser.py`，`19/19` 通过。
- 运行：`python -m py_compile main.py src/json2lean/block_parser.py test/test_block_parser.py`，无语法错误。

## 2026-04-15 — 重建并补全 README（对齐当前实现）

### 变更
- **`README.md`**
  - 从空文件重建为完整项目文档。
  - 按当前代码行为补充：
    - 单文件增量输出模式
    - `settings.json` 分层加载
    - `--semantic-only` / `--postprocess-only` / 续跑参数
    - 修复历史策略（严格最近 5 条）
    - 日志与产物位置、常见问题说明

### 说明
- 文档内容已与 `main.py`、`pyproject.toml`、`config.example.json`、`settings.json` 保持一致，便于直接上手和排查流程问题。

---
## 2026-04-15 — 修复历史记录严格保留5条、丢弃旧条目

### 变更
- **`src/json2lean/repair_history.py`**
  - 修改 `format_for_prompt()` 的摘要策略：严格只保留最近 N 条（`keep_recent`，默认=5），旧条目直接丢弃（不再摘要）。
  - 保留两部分：
    1. 最近 5 条尝试的完整细节（代码、错误、拒绝原因等）
    2. 所有历史中的失败模式汇总（错误签名、拒绝原因等）
  - 删除对 `max_prompt_chars` 的预算压缩逻辑（因为只保留最近 5 条，通常不会超长）
  - `_summarise_entry()` 保留但不再被 `format_for_prompt()` 调用（备用）

### 说明
此改动进一步降低了历史信息对 LLM 修复判断的干扰：
- 编译修复与语义修复都**严格只传入最近 5 条历史**（以完整细节形式）
- 更早的尝试完全被丢弃，避免分散 LLM 注意力
- `collect_failed_patterns()` 仍然汇总全局失败模式（失败原因、重复错误），帮助 LLM 识别"避免"的策略
- 总体 prompt 更精简、信号更直接

---
## 2026-04-15 — 修复历史记录保留数调整至5条

### 变更
- **`src/json2lean/repair_history.py`**
  - 修改默认常量 `_DEFAULT_KEEP_RECENT` 从 3 改为 5
  - 避免历史信息过多导致的 prompt 膨胀与 LLM 修复判断干扰

- **`main.py`**
  - 编译修复阶段：在两处 `compile_history_by_label.setdefault()` 改为 `RepairHistory(keep_recent=5)`
  - 语义修复阶段：`sem_history = RepairHistory(keep_recent=5)`

- **`src/json2lean/compile/compiling_fixer.py`**
  - `recover_exercise()` 中默认历史初始化：`RepairHistory(keep_recent=5)`
  - `recover_all()` 中每条目历史初始化：`RepairHistory(keep_recent=5)`

- **`test/test_smoke.py`**
  - 测试用例中历史初始化：`RepairHistory(keep_recent=5)`

### 说明
此次调整统一了编译修复与语义修复的历史记录策略：
- 将保留条数从默认的 3 调整为 5，降低历史信息对 LLM 判断的干扰风险
- 仍保留总体字符上限（`max_prompt_chars`）的约束，防止 prompt 过度膨胀
- 对较旧尝试自动进行摘要（`_SUMMARY_CHAR_BUDGET`）处理，保留关键失败模式列表

---
## 2026-04-14 — 修复 section 边界子串误匹配导致的块错投

### 变更
- **`src/json2lean/block_parser.py`**
  - 修复 `insert_block_comment()` 的 section 结束位置查找：
    - 由字符串 `rfind("end <section>")` 改为按整行正则匹配 `^end <section>$`
    - 避免 `Exercise_9_1` 误命中 `end Exercise_9_13` / `end Exercise_9_12`
  - 修复 `frozen_context_in_section()` 的 section 开闭边界查找：
    - 改为按整行正则匹配 `^section <section>$` 与 `^end <section>$`

- **`main.py`**
  - 修复 `_find_section_bounds()` 的 section 开闭边界查找：
    - 由子串 `find()` 改为整行正则匹配
    - 防止同前缀 section 名（如 `Exercise_9_1` 与 `Exercise_9_13`）发生边界错位

### 根因说明
- 原实现采用子串匹配，`end Exercise_9_1` 会错误匹配到 `end Exercise_9_13`（以及 `end Exercise_9_12`）。
- 导致块注释/代码在插入与边界计算时落到错误 section（典型表现：`Exercise 9.1` 内容被放进 `section Exercise_9_13`）。

---

## 2026-04-14 — 翻译提示词更新：algo和opt_prob统一要求必须使用structure

### 变更
- **`prompts/translate/json_to_lean.md`**
  - **修改 `kind = algo`（算法描述）规则**
    - 删除"简单算法可用def"的选项，统一要求**必须使用`structure`**定义
    - 适用于所有复杂度的算法，包括简单算法（单函数、无复杂状态）也必须用structure
    - 可在结构命名空间下定义辅助`def/lemma`
    - 更新描述为"Even for simple algorithms with minimal state, use `structure` as the primary declaration form"

  - **修改 `kind = opt_prob`（优化问题）规则**
    - 删除"简单优化问题可用def"的选项，统一要求**必须使用`structure`**定义
    - 适用于所有复杂度的优化问题，包括少量变量/约束也必须用structure
    - 可在结构命名空间下定义辅助`def/instance`
    - 更新描述为"Even for simple optimization problems with few variables or constraints, use `structure` as the primary declaration form"

### 说明
此次调整统一了algo和opt_prob的设计风格：
- 原先的分级设计（复杂用structure、简单用def）已放弃
- 新规则确保所有算法和优化问题都有统一的结构化表示，便于后续的检查、重用和语义修复
- 保留了在structure命名空间下定义辅助函数（def/lemma/instance）的灵活性

---

## 2026-04-14 — 翻译提示词优化：thm支持多def辅助 + algo/opt_prob分级设计

### 变更
- **`prompts/translate/json_to_lean.md`**
  - **修改 `kind = thm` 规则**
    - 允许定义多个top-level的`def`作为定理的辅助定义（不仅限于`let`）
    - 约束调整为：只能有**一个top-level `theorem`**，但可以在前面定义若干`def/lemma`
    - 示例：`def helper1 := ...`, `def helper2 := ...`, `theorem main_claim := ...`
    - 更新描述，强调"翻译的尽量清晰"

  - **新增 `kind = algo`（算法描述）分级规则**
    - **复杂算法**：使用`structure`作为主体，可在其命名空间下定义`def/lemma`
      - 示例：`structure AlgorithmA where ...`, `def AlgorithmA.step := ...`
    - **简单算法**：直接用`def`声明，无需structure包装
    - 更新规则说明和示例代码

  - **新增 `kind = opt_prob`（优化问题）分级规则**
    - **复杂优化问题**：使用`structure`作为主体，可在其命名空间下定义`def/instance`
      - 示例：`structure OptimizationProblem where ...`, `def OptimizationProblem.is_feasible := ...`
    - **简单优化问题**：直接用`def`声明，无需structure包装
    - 更新规则说明和示例代码

### 说明
此次优化提高了翻译的灵活性：
- 定理翻译可以通过多个辅助定义更清楚地表达复杂逻辑
- 算法和优化问题可根据复杂度选择用structure还是def，不再强制要求structure
- 支持在structure的命名空间下定义相关的def/lemma/instance，使代码结构更清晰

---

## 2026-04-13 — 预处理配置：添加规范化跳过定理选项

### 变更
- **`src/json2lean/models.py`**
  - 在 `PipelineConfig` 中新增属性 `preprocessing_normalize_skip_thm: bool = False`
  - 在 `from_dict()` 方法中添加映射 `pre.get("normalize_skip_thm", False)`
  - 在 `overlay_settings()` 的映射字典中添加 `"normalize_skip_thm": "preprocessing_normalize_skip_thm"`

- **`settings.json`**
  - 在 `preprocessing` 段添加 `"normalize_skip_thm": false` 配置项
  - 允许用户通过 settings.json 控制是否跳过对 `kind="thm"` 记录的规范化

- **`src/json2lean/preprocess/pipeline.py`**
  - `preprocess_exercise()` 函数新增参数 `normalize_skip_thm: bool = False`
  - `preprocess_all()` 函数新增参数 `normalize_skip_thm: bool = False`
  - 在调用 `_run_normalization()` 时传递 `normalize_skip_thm` 参数

- **`src/json2lean/preprocess/normalization.py`**
  - `_run_normalization()` 函数新增参数 `normalize_skip_thm: bool = False`
  - 当 `normalize_skip_thm=True` 时，将记录分离为定理和非定理两组
  - 仅对非定理记录（`kind != "thm"`）执行规范化处理
  - 定理记录保持原始内容，跳过 LLM 规范化步骤

- **`main.py`**
  - 在调用 `preprocess_all()` 时传递 `normalize_skip_thm=cfg.preprocessing_normalize_skip_thm`

### 说明
此功能允许在最后的规范化阶段选择性地跳过对定理（`kind="thm"`）的处理，同时保留对定义、优化问题、算法等其他记录类型的规范化。这对于某些情况下希望保留定理原始表述的使用场景很有帮助。

---

## 2026-04-13 — 提示词更新：禁止内积记号后带标量域下标


### 变更
- **`prompts/translate/json_to_lean.md`**
  - 在「Naming & Style Rules」中新增规则 3：**Inner product notation rule**
  - 禁止在 `⟪x, y⟫` 后面加显式标量域下标（如 `⟪g k, p k⟫_ℝ`）
  - 原因说明：当类型已唯一确定标量域（例如 `g k p k : EuclideanSpace ℝ (Fin n)` 时），Lean 可自动推断，无需显式 `_ℝ`
  - 规则：始终移除内积记号中的标量域后缀下标

- **`prompts/fixer/compiling_fixer.md`**
  - 在「Lean-specific heuristics」中新增规则 52：**Inner product notation subscripts**
  - 告知编译修复器识别并移除内积记号中的 `_ℝ` 等标量域下标
  - 例：`⟪g k, p k⟫_ℝ` 应改为 `⟪g k, p k⟫`
  - 重新编号后续规则 (53→54, 54→55 等)

### 背景
发现 Lean 4 中内积记号 `⟪x, y⟫` 不支持显式标量域下标 `_ℝ`：
- ❌ `⟪g k, p k⟫_ℝ` （parser 错误）
- ✅ `⟪g k, p k⟫` （标量域自动推断）

此规则确保生成和修复的 Lean 代码中不出现这类不受支持的记号用法。

---

## 2026-04-13 — 提示词更新：添加 Lean structure 字段语法规则

### 变更
- **`prompts/translate/json_to_lean.md`**
  - 在「Naming & Style Rules」中新增规则 2：**Structure field declaration rule**
  - 说明 `structure ... where` 中每个字段必须单独声明，不能用多 binder 简写 `c1 c2 : ℝ`
  - 标注原因：结构体字段声明不支持多 binder 语法（与 theorem/def 参数不同）
  - 这应用于所有 `kind = alg` 或 `kind = opt_prob` 的翻译

- **`prompts/fixer/compiling_fixer.md`**
  - 在「Lean-specific heuristics」中新增规则 51：**Structure field syntax**
  - 告知编译修复器：如果 structure 字段声明出现解析错误，应首先怀疑多 binder 简写，剥开成单行声明
  - 重新编号后续规则 (52→53, 53→54, 54→55 等)

### 背景
发现 Lean 4 中 `structure` 和 `theorem/def` 在字段/参数声明上的关键语法差异：
- ❌ `structure S where` 内：`c1 c2 : ℝ` （解析失败）
- ✅ `structure S where` 内：分行声明 `c1 : ℝ` 和 `c2 : ℝ`
- ✅ `theorem foo (c1 c2 : ℝ)` 中：多 binder 缩写有效（这是标准 binder 语法）

此规则便于翻译器和修复器处理涉及数学结构的题目时注意这一陷阱。

---

## 2026-04-13 — 去重逻辑改造：scope 收窄至当前 section + 只检查声明和 top-level 命令

### 变更
- **`src/json2lean/block_parser.py`**
  - 新增 `_TOP_LEVEL_CMD_RE`：匹配 `open`、`open scoped`、`variable`、`set_option` 等 top-level 命令。
  - 新增 `_collect_top_level_commands(text)`：收集 frozen context 中所有 top-level 命令的字符串集合。
  - 移除 `_is_dedup_candidate_line()`（已无用）。
  - `dedupe_block_code_against_frozen()` 第二阶段改造：不再对任意行做逐行去重（旧逻辑会误删 `sorry` 等证明体内容），改为只删除与 frozen context 重复的 top-level commands。
  - 新增 `frozen_context_in_section(lean_text, block_id, section_name)`：仅返回当前 section 内、当前 block comment 之前的文本作为 frozen context；找不到 section 边界时回退到 `frozen_context_before()`。
- **`main.py`**
  - 新增导入 `frozen_context_in_section`。
  - `_run_semantic_loop_on_combined_file()`：将 `section_context = frozen_context_before(...)` 改为 `frozen_context_in_section(..., section_name)`，去重只与当前 section 内的已有内容比对。
  - `_recover_combined_file_for_item()`：将 `frozen = frozen_context_before(...)` 改为 `frozen_context_in_section(..., section)`，同上。

### 测试
- 70 个单元测试全部通过。
## 2026-04-13 — 编译/语义修复时只传入当前 section 的内容作为上下文

### 变更
- **`main.py` — `_recover_combined_file_for_item()`（block-scoped 路径）**：
  - 不再将完整合并文件（`full_text`）作为 LLM 上下文，改为只提取当前 `section` 的内容构建独立可编译片段（`context_text`）。
  - 若找不到 section 边界则回退到 `full_text`（兼容旧逻辑）。
  - 编译目标从 `output_file` 改为专用临时文件 `recover_section_file`，避免修复过程覆盖完整合并文件。
- **`main.py` — `_recover_combined_file_for_item()`（legacy section 路径）**：
  - 修复一个已存在的 bug：原代码在 `section_mode=True` 时将 section 作用域的内容写入 `output_file`，导致合并文件被破坏。
  - 现在 `section_mode=True` 时同样使用专用临时文件（`_legacy_src_file`）作为编译目标；`section_mode=False` 时继续使用 `output_file`（行为不变）。

## 2026-04-13 — 推送到远程分支 `semantic_fix`

### 变更
- 提交并推送本地更改（提交信息："Update local changes"）。包含对 `changelog.md`、`main.py`、若干 `prompts` 与 `src/` 下文件的修改。

## 2026-04-13 — 编译修复直接修改源文件，不再创建临时文件

### 变更
- **`src/json2lean/compile/compiling_fixer.py`**：
  - `recover_exercise()` 新增可选参数 `source_file: Path | None`。当提供时，修复后的代码直接写入该文件并编译，不再通过 `write_lean_file` 创建临时文件。
  - MCP 上下文路径也相应使用 `source_file`（如已提供）。
  - `recover_all()` 新增 `source_file` 参数并透传给 `recover_exercise()`。
  - 未传 `source_file` 时行为不变（向后兼容）。

- **`main.py`**：
  - `_recover_combined_file_for_item()` 的 block-scoped 和 legacy section-based 两条恢复路径均传入 `source_file=output_file`，使修复过程直接在合并 Lean 源文件上操作。

## 2026-04-12 — 将去重处理集成到临时文件替换阶段

### 架构重构
- **块代码替换与临时文件去重一体化**
  - `src/json2lean/block_parser.py`：
    - 新增辅助函数 `_collect_decl_names()`、`_is_dedup_candidate_line()` 用于去重检测。
    - 新增导出函数 `dedupe_block_code_against_frozen()`，实现标准化的块级去重逻辑。
    - **重构 `replace_block_code()` 签名**：从 `(lean_text, block_id, new_code) -> str` 改为 `(lean_text, block_id, new_code, frozen_context=None) -> tuple[str, Dict]`。
      - 当 `frozen_context` 参数提供时，新代码块在被插入到文件前自动进行去重。
      - 返回值为 `(updated_file_text, dedup_stats)` 元组，其中 `dedup_stats` 包含 `removed_declarations` 和 `removed_lines` 计数。
      - 这确保了去重发生在"内存临时文件阶段"，即代码块实际写入文件之前就已经清除了冗余。

- **main.py**：
  - 移除重复的去重函数定义 `_dedupe_block_code_against_frozen()`、`_collect_decl_names()`、`_is_dedup_candidate_line()`。
  - 从 `block_parser` 导入新的 `dedupe_block_code_against_frozen`。
  - 更新所有调用 `replace_block_code()` 的地方（语义循环和恢复路径）以使用新签名，传入 `frozen_context` 参数。
  - 简化代码：去重逻辑现在由 `replace_block_code()` 内部完成，不需要在调用前额外调用。

- **test/test_block_parser.py**：
  - 更新 `test_replace_block_code()` 以处理返回的元组。
  - 新增 `test_replace_block_code_with_dedup()` 测试，验证在提供 `frozen_context` 时自动去重的行为。

### 效果与意义
- **更安全的临时文件处理**：去重发生在内存中的代码块替换操作，确保任何块级修改（翻译、修复、语义重写）都自动清除冗余。
- **更清晰的职责分离**：`replace_block_code()` 现在承担"块替换 + 自动防护性去重"的完整职责，调用方不需要额外的去重逻辑。
- **防守性编程**：即使上游代码忘记了去重，块替换时也会自动清除冗余，降低了冗余声明进入文件的风险。

---
## 2026-04-12 — 修复后按 block 自动去重 + translate 阶段接入 MCP

### 行为新增
- `main.py`
  - 新增 `_dedupe_block_code_against_frozen(...)`：在“当前 block vs 冻结前序 block”维度执行两步去重：
    - 删除当前 block 中与前序 block 重名的顶层声明（`def/theorem/lemma/...`）。
    - 删除当前 block 中与前序 block 完全相同的重复语句行（保留结构行与注释行）。
  - 在 `_recover_combined_file_for_item(...)` 中，编译修复成功后、写回当前 block 前执行上述去重。
  - 在 `_run_semantic_loop_on_combined_file(...)` 的每次 rewrite 后、替换当前 block 代码前执行上述去重。
  - 新增 `_gather_translation_mcp_context(...)`，在翻译阶段调用 MCP 工具上下文并作为只读辅助信息注入到翻译请求。
  - 翻译主循环 Step 2b 调用 `translate_exercise(...)` 时新增 `mcp_context` 透传。

- `src/json2lean/translater.py`
  - `_build_prompt(...)` 增加 `mcp_context` 参数，并将 MCP 上下文以只读提示块加入 prompt。
  - `translate_exercise(...)` / `translate_all(...)` 增加 `mcp_context` 相关参数。

- `src/json2lean/models.py`
  - `PipelineConfig.translation` 新增 MCP 配置项：
    - `mcp_enabled`
    - `mcp_pool_size`
    - `mcp_repo_path`
    - `mcp_tool_mode`
    - `mcp_tools`
  - `from_dict(...)` 与 `overlay_settings(...)` 同步支持上述字段。

- `settings.example.json`
  - `translation` 节新增 MCP 相关示例配置字段。

## 2026-04-12 — recovery 严格遵循 settings.recovery.mcp_tools

### 行为修正
- `src/json2lean/compile/compiling_fixer.py`
  - 当 `settings.json` 中 `recovery.mcp_tools` 非 `null` 时，恢复阶段的 MCP 工具选择改为**严格按该列表**，不再按 `mcp_tool_mode` 推导默认工具集合。
  - `recover_all(...)` 现在将 `mcp_tools` 显式透传给 `recover_exercise(...)`，保证日志展示与实际配置一致。

### 验证
- 新增 `test/test_recovery_mcp_tools.py`：
  - 验证 `_mcp_tool_names(...)` 在 `configured_tools` 非空时按配置去重并原序返回。
  - 验证 `recover_all(...)` 在开启 MCP 恢复时，会把 `mcp_tools` 透传给 `gather_recovery_context(..., enabled_tools=...)`。

## 2026-04-12 — Tighten compiling_fixer prompt for block-scoped recovery

### Prompt update
- `prompts/fixer/compiling_fixer.md` 新增针对当前 pipeline 的硬约束：
  - 明确 block-scoped recovery 虽然会收到完整 Lean 文件，但前序 block 只是冻结上下文，只有当前 block 可修改。
  - 明确要求输出完整文件时不得复制、重述、移动、重命名前序 block 的代码。
  - 增加 `already declared` 的优先处理策略：先判定当前 block 是否错误复制了前序声明；若是，删除重复声明，而不是加撇号改名。
  - 补充不得重复 `import Mathlib`、`noncomputable section`、`section/end` 或前序 block 内容。
  - 明确 MCP context 仅是只读辅助上下文，不得据此重写冻结 block。

## 2026-04-12 — MCP selective tool loading + settings.json 配置支持

### Feature
1. **终端只打印实际成功加载的 MCP 工具**  
   `MCPHelper._load_tools` 重构为逐模块按需导入：只导入 `enabled_tools` 所需的 `lean_tools_mcp.tools.*` 子模块，模块导入失败时静默跳过，最后打印一行汇总：  
   `[mcp_helper] Loaded tools (N): lean_leansearch, lean_unified_search, ...`

2. **`settings.json` 中可配置加载哪些 MCP 工具**  
   `recovery.mcp_tools` 新字段，接受工具名列表（`null` 表示加载全部）：

   ```json
   "recovery": {
     "mcp_tools": ["lean_unified_search", "lean_leansearch", "lean_loogle"]
   }
   ```

### Changed files
- `src/json2lean/config/mcp_helper.py`：添加 `_MODULE_PATHS` / `_ALL_TOOL_DEFS` 常量；`_load_tools(enabled_tools)` 重构；`MCPHelper.__init__`、`call_all_tools_async`、`call_all_tools`、`gather_recovery_context` 新增 `enabled_tools` 参数。
- `src/json2lean/models.py`：`PipelineConfig` 新增 `recovery_mcp_tools: list[str] | None = None`；`from_dict` / `overlay_settings` 同步更新。
- `src/json2lean/compile/compiling_fixer.py`：`recover_all` 新增 `mcp_tools` 参数并透传给 `gather_recovery_context`。
- `main.py`：两处 `recover_all` 调用新增 `mcp_tools=cfg.recovery_mcp_tools`。
- `settings.json` / `settings.example.json`：`recovery` 节下增加 `"mcp_tools": null`。

## 2026-04-12 — Fix block duplication in semantic rewrite loop

### Bug
语义重写循环 (`_run_semantic_loop_on_combined_file`) 中，`rewrite_from_report` 返回的 LLM 输出可能是包含 `section_context`（冻结的前序 block）+ 当前 block 的完整 Lean 文件。
原来的 `_strip_lean_preamble(new_code)` 只剥离 `import Mathlib` / `noncomputable section`，
**未传入 `section_name`**，所以 `section Exercise_2_12` / `end Exercise_2_12` 残留；
剩余内容包含前序 block 代码，`replace_block_code` 用这段巨型文本替换当前 block 的代码区域，
导致前序 block 在文件中出现多次（好多个 defn/thm 块）。

### Fix  
- **main.py** `_run_semantic_loop_on_combined_file`：`_strip_lean_preamble` 改为传入 `section_name=section_name`；之后用 `extract_block_by_id(new_chunk, bid)` 从结果中精确提取当前 block 的代码（只有代码部分，不含 comment），从根本上防止冻结内容进入 `replace_block_code`。

## 2026-04-13 — Fix duplicate `end` in block-scoped recovery path

### Bug
`_recover_combined_file_for_item` 的 block-scoped 修复路径将 `frozen + block_code` 拼成不完整的 Lean 文件（缺少 `end {section}`），导致 fixer 自动补 `end`。提取修复后的 block 代码时 `end` 残留，再写回 scaffold 后产生双重 `end`，编译报错 `Unexpected name after 'end'`。

### Fix
- **main.py** `_recover_combined_file_for_item`：block-scoped 路径改为将 **完整文件**（`full_text`）发送给 `recover_all`，修复后用 `extract_block_by_id` 从结果中只提取当前 block 的代码。semantic guard 已约束 fixer 仅修改当前 block。
- **lean/LeanProject/exe2_12.lean**：移除多余的 `end Exercise_2_12`，文件现已通过编译。

## 2026-04-13 — Block-based incremental pipeline refactor

### 概述
将翻译/语义/修复流程从"全量翻译→合并→注释→修复"改为"scaffold→逐block：插入注释→翻译→插入代码→编译修复→冻结→下一个block"。block comment 由 orchestrator 唯一生成，全流程不可变。

### 新增文件
- `src/json2lean/block_parser.py` — 单一权威的 block comment 生成器与解析器
- `settings.example.json` — 运行时 settings 模板（不含凭证）
- `test/test_block_parser.py` — block_parser 单元测试（15 项）
- `test/test_config_split.py` — config split 单元测试（7 项）

### 变更文件
- **main.py**
  - 翻译主循环：替换为 block-by-block 增量流程 (`_build_scaffold` → `generate_block_comment` → `insert_block_comment` → `translate_exercise` with `frozen_context_before` → `insert_code_after_comment` → compile → optional block-scoped recovery)
  - 语义循环 `_run_semantic_loop_on_combined_file`：替换为基于 `parse_blocks` / `extract_block_by_id` / `replace_block_code` / `frozen_context_before` 的 block-based 逻辑
  - `_recover_combined_file_for_item`：新增 `current_block_id` 参数，支持 block-scoped 修复路径
  - 删除 9 个废弃辅助函数：`_replace_item_chunk`, `_build_declaration_hints_for_targets`, `_find_semantic_chunk_bounds`, `_fallback_declaration_name_in_section`, `_extract_semantic_chunk`, `_build_section_context_for_review`, `_build_combined_lean_file_text`, `_append_exercise_to_combined_file`, `_section_declaration_entries`, `_extract_declaration_entries`, `_build_section_context_for_translation`, `_safe_label`
  - 移除 `enforce_exact_source_comments` 导入和 `_TOP_LEVEL_BOUNDARY_RE` 正则
  - 新增 `--settings` CLI 参数
- **src/json2lean/loader.py** — 新增 `load_settings()` 函数
- **src/json2lean/models.py** — `PipelineConfig` 新增 `overlay_settings()` 方法
- **src/json2lean/translater.py** — `_kind_hint()` 移除 source comment 生成指令，改为"Do NOT generate block comments"；`translate_exercise()` 不再调用 `enforce_exact_source_comments`
- **src/json2lean/config/mcp_helper.py** — `_READ_ONLY_ALLOWLIST` 和 `_LSP_BOUND_TOOLS` 新增 `lean_hover` 别名
- **prompts/translate/json_to_lean.md** — 移除 source-comment 生成规则，新增 block-comment 禁止条款
- **prompts/fixer/compiling_fixer.md** — 新增 block comment 不可变约束和 current-block-only 修复范围
- **prompts/fixer/semantic_review.md** — 审查单元改为 block 级别，block comment 为不可变锚点
- **prompts/fixer/semantic_rewrite.md** — 新增 block comment 不可变约束和 current-block-only 重写范围

## 2026-04-12 — 修复 semantic loop 使用错误的 exercises 列表

### 变更文件
- `main.py`

### 变更内容
- `semantic_targets` 改为使用 `exercises_to_translate`（含 `kind` 字段的预处理记录列表），而非原始 `exercises`（无 `kind`）。
- 修复了 `[semantic] no defn/thm/opt_prob/algo items; semantic loop skipped.` 的问题。

## 2026-04-12 — definition 抽取改为 Lean 可直译形式

### 变更文件
- `prompts/preprocess/extract_definition.md`

### 变更内容
- 收紧 Stage 1 的 definition 输出要求：
  - 每个 definition 必须能直接翻译成 Lean 里的谓词、命题、等式、不等式或等价关系。
  - 禁止使用 `differ greatly in magnitude`、`much larger`、`highly unbalanced` 这类模糊比较词。
  - 如果原文只给出结论性 characterization，也要改写成精确的数学条件。

## 2026-04-12 — theorem 构造改为“多问/多 statement 必拆分”

### 变更文件
- `prompts/preprocess/construct_theorem.md`

### 变更内容
- 收紧 Stage 2 的 theorem 构造规则：
  - 只要题目里出现多个分问、多个 proof statement，或多个逻辑上独立的 theorem-like claim，就分别输出为独立 theorem items。
  - 不再因为它们共享上下文就合并成一条 theorem。
  - 继续要求每条 theorem 自包含，并重复共享设定。

## 2026-04-12 — 放宽 definition 抽取规则，允许结论性特征词

### 变更文件
- `prompts/preprocess/extract_definition.md`

### 变更内容
- 放宽 Stage 1 的 definition 抽取规则：
  - 允许抽取原文中“明确 characterizes / concludes about”的术语，即使它不是以标准定义句式出现。
  - 允许保留题目里的结论性特征词，例如 `ill-conditioned` 这类在证明结论中出现的术语。
  - 继续要求每个 definition 保持简短，最多 1 到 2 句，只保留核心判定条件。

## 2026-04-11 — 改为逐条翻译预处理记录（per flat record translation）

### 变更文件
- `src/json2lean/preprocess/pipeline.py`
- `main.py`

### 核心改动
#### 预处理阶段（pipeline.py）
- **移除记录合并逻辑**（之前第 200-209 行）：
  - 之前：生成 flat records → 再合并回 `exercise.problem` 单一文本（为向后兼容）
  - 现在：生成 flat records 后保存为 `exercise.preprocessed_problem`，不再合并
- `records` 现在是预处理的"主单位"，而不是附注物

#### 翻译阶段（main.py）
- **新增预处理记录加载逻辑**（第 347-387 行）：
  - 检查预处理流程是否已运行（`do_preprocess=True`）
  - 尝试从 `{log_dir}/{input_stem}.json` 或 `{workspace}/preprocessed_data/{input_stem}.json` 加载
  - 如果 JSON 存在且非空，把每条 record 转换为临时 `Exercise` 对象
  - 过滤掉 `kind="hints"` 的记录，其他类型的记录都变成单独的翻译目标
- **修改翻译循环**：
  - 新增变量 `exercises_to_translate`，默认值为 `exercises`（向后兼容）
  - 如果加载到预处理记录，则 `exercises_to_translate = temp_exercises`
  - 翻译循环现在遍历 `exercises_to_translate` 而非 `exercises`
  - 所有日志消息改为显示 `{i}/{len(exercises_to_translate)}` 而非 `{i}/{total}`

### 翻译顺序改变
- **旧流程**：每个 exercise（可能含多条 defn/thm/opt_prob 等）→ 一次 prompt（整块翻译）
- **新流程**：每条 flat record（单独的 defn/thm/opt_prob 等）→ 一次 prompt（逐条翻译）

### 向后兼容
- 如果未启用预处理（`do_preprocess=False`），或预处理 JSON 不存在，自动回退到原来的 exercise-based 流程
- 现有的 config、translate_exercise 等函数无需改动

## 2026-04-09 — 预处理可选过滤 hints 记录

### 变更文件
- `config.example.json`
- `src/json2lean/models.py`
- `src/json2lean/preprocess/pipeline.py`
- `main.py`

### 新增功能
- 在预处理后整合 JSON 时，可选过滤掉 `kind="hints"` 的记录。
- 配置文件中 `preprocessing.exclude_hints` 字段（默认 `false`）：
  - 设为 `true` 时，输出 JSON 中将不包含 hints 记录。
  - 同时在标准输出中显示被过滤的记录数量。
- `preprocess_all()` 函数新增 `exclude_hints` 参数。

## 2026-04-09 — source_idx 一致性修复 & 前端匹配逻辑升级

### 变更文件
- `src/json2lean/preprocess/pipeline.py`
- `viewer/app.js`

### 后端
- 修复 `pipeline.py` 中 `source_idx` 提取逻辑：
  - 支持从 `content` 嵌套对象中提取 `source_idx`（兼容旧 wrapper 格式）。
  - 修复 `or` 链中 `index=0` 被误判为 falsy 的问题，改用显式 `None`/空检查。
  - 优先级：`raw.source_idx` → `raw.content.source_idx` → `raw.index` → `exercise.index`。
  - 确保输出 JSON 的 `source_idx` 与输入 JSON 的 `source_idx` 保持一致（如 `"Exercise 2.5"`）。

### 前端
- `Unit` 视图左右匹配改为按 **source_idx 字符串值** 配对（而非按数组位置的数字序号）。
  - 左侧条目的 `source_idx`（如 `"Exercise 2.5"`）用于查找右侧 `source_idx` 相同的所有条目。
- 侧边栏题号标签使用左侧条目的原始 `source_idx` 值。
- 右侧空匹配提示改为显示具体 `source_idx` 值。

## 2026-04-09 — viewer 单元匹配规则与 term 展示增强

### 变更文件
- `viewer/app.js`

### 变更内容
- `Unit` 视图改为“按题号单题浏览”：
	- 左侧仅显示第 `n` 题（`n` 为左侧 JSON 数组的第 `n` 个条目）。
	- 右侧显示所有满足 `source_idx == "n"` 的条目。
- 左边栏在 `Unit` 视图中改为“题号列表”：
	- 列表标签使用左侧 JSON 对应条目的 `source_idx`（无则回退为 `n`）。
	- 每项右侧徽标显示当前题号在右侧匹配到的条目数。
- 对 `kind` 为 `algo` / `opt_prob` / `defn` 的右侧条目新增 `term` 显示区块（缺失时显示 `absent`）。
- 启动后若存在可配对文件，自动加载第一组文件并初始化题号列表。

## 2026-04-08 — viewer 新增题目单元视图与 LaTeX 渲染

### 变更文件
- `viewer/index.html`：新增 KaTeX CDN（`katex.min.css` + `katex.min.js` + `auto-render.min.js`），工具栏新增 `Unit` 视图按钮。
- `viewer/app.js`：新增 `unit` 视图模式（默认），将 JSON 按条目渲染为题目卡片：
	- 左侧每题展示 `problem` 与 `proof`（兼容 `item.content.problem/proof` 与顶层字段）。
	- 右侧每题展示 `content`（若无 `content` 则回退展示整个条目）。
	- 对上述文本启用 KaTeX 自动渲染，支持 `$...$`、`$$...$$`、`\(...\)`、`\[...\]`。
- `viewer/styles.css`：新增题目卡片样式（`unit-list`、`unit-card`、`unit-body` 等）与 KaTeX 显示优化样式。

### 行为变化
- 打开文件后默认进入 `Unit` 视图，可按“每道题一个单元”浏览。
- `Tree` 与 `Raw` 视图保留，可继续用于结构化比对与原始文本查看。

## 2026-04-08 — 新增 viewer 前端（JSON Diff Viewer）

### 新增文件
- `viewer/index.html` — 单页应用入口，CDN 引入 jsondiffpatch 0.6.0 + highlight.js 11.9.0
- `viewer/app.js` — 应用逻辑：目录自动扫描、文件配对、JSON 树渲染、差异计算、导出 diff
- `viewer/styles.css` — 暗色主题样式，含差异高亮（新增/删除/修改/含嵌套变化）
- `viewer/README.md` — 快速启动、功能说明、UI 操作指南

### 功能概述
- 通过 `python -m http.server 8000` 从仓库根启动，自动扫描 `data/` 与 `preprocessed_data/` 中的 JSON 文件并按文件名配对；无法自动加载时回退到手动上传。
- 并列树形视图 + 原始文本视图；差异高亮（绿/红/黄色左边框）；"仅显示差异"开关；点击字段可在底部信息栏查看完整路径与左右值对比；导出 diff 为 JSON。

## 2026-04-08 — 预处理模块拆分与清理

### 删除的无用文件
- `src/json2lean/preprocessor.py.bak` — 旧版备份
- `prompts/preprocess/extract_assumption.md` — 旧 pipeline 阶段
- `prompts/preprocess/extract_goal.md` — 旧 pipeline 阶段
- `prompts/preprocess/refine_assumption.md` — 旧 pipeline 阶段
- `prompts/preprocess/refine_goal.md` — 旧 pipeline 阶段
- `prompts/preprocess/reorder_blocks.md` — 旧 pipeline 阶段
- `test/test_validation.py` — 引用已不存在的旧函数（`_STAGES`、`_merge_stages` 等）

### 模块拆分
将 `src/json2lean/preprocessor.py`（~940 行）按 pipeline 阶段拆为 `src/json2lean/preprocess/` 包：

| 文件 | 内容 |
|------|------|
| `__init__.py` | 包入口，re-export 全部公共 API |
| `_common.py` | 共享常量 `PROMPT_NAMES` + 工具函数 `build_stage_prompt` |
| `models.py` | `StageResult`, `Placeholder`, `MaskingResult`, `FlatRecord` |
| `validators.py` | 5 个验证函数 |
| `hint_extraction.py` | Stage 0a: 提示语提取 |
| `masking.py` | Stage 0b: 特殊块提取 |
| `definition.py` | Stage 1: 定义提取 |
| `theorem.py` | Stage 2: 定理构造 |
| `normalization.py` | Stage 3: 归一化 |
| `pipeline.py` | 编排器 `preprocess_exercise` / `preprocess_all` / `reindex_records` |
| `PIPELINE.md` | 中文版 pipeline 详细文档 |

### Import 路径更新
- `main.py`: `json2lean.preprocessor` → `json2lean.preprocess`
- `test/test_preprocessor.py`: 同上
- `test/run_preprocessor_test.py`: 同上
- 旧 `src/json2lean/preprocessor.py` 已删除

### 验证
- 44/44 预处理器测试通过
- Smoke test 通过

## 2025-07-17 — Preprocessing Pipeline Refactor

### Summary
Complete rewrite of the preprocessing pipeline to produce flat-record JSON output under `preprocessed_data/`. Six major behavioral changes implemented.

### Changed Files
- **src/json2lean/preprocessor.py** — Fully rewritten (~800 lines). New pipeline stages: indexed hint masking → special block extraction with assigned names → definition extraction (optimization-domain only, no masking) → theorem construction with placeholder filling + NL repair → optional normalization. Output: `List[FlatRecord]` per exercise, written to `preprocessed_data/<stem>.json`.
- **prompts/preprocess/extract_hint.md** — Indexed markers `[HINT1_EXTRACTED]`, `[HINT2_EXTRACTED]` etc. instead of single `[HINT_EXTRACTED]`.
- **prompts/preprocess/identify_special_blocks.md** — Added `assigned_name` requirement for each extracted block.
- **prompts/preprocess/extract_definition.md** — Rewritten: only optimization-domain terms, no source masking.
- **prompts/preprocess/construct_theorem.md** — New prompt: theorem construction with placeholder filling + NL repair.
- **prompts/preprocess/normalize_record.md** — New prompt: optional normalization pass.
- **src/json2lean/translater.py** — `_kind_hint()` handles `algo`/`alg`, `opt_prob`, `hints`.
- **src/json2lean/semantic/declaration_policy.py** — `validate_top_level_contract()` updated for new kinds.
- **main.py** — `preprocess_all()` receives `input_stem`; translation loop skips `hints`; section context + semantic targets expanded.

### New Files
- **test/test_preprocessor.py** — 44 tests across 9 test classes covering all validation, output format, downstream compatibility, and integration requirements.

### Output Schema
Each flat record: `{index, source, source_idx, kind, content, term?}` where `kind ∈ {thm, defn, opt_prob, algo, hints}`.

### Verification
- 44/44 new preprocessor tests passed
- Existing smoke tests passed (no regressions)


## 2026-04-08 — 根治 setup-file 导致的 olean 删除问题

### 根因
Lake 5.0.0 的 `lake setup-file` 需要遍历所有 8000+ 个 Mathlib 模块验证 trace 一致性，
结构性地耗时 10+ 分钟。VS Code Lean 扩展调用 `lake setup-file --no-build --no-cache` 时：
- 超时报错 "Failed to build module dependencies"
- 遍历过程中会尝试写入/替换 olean 文件，若中断则 olean 丢失

### 修复
**`scripts/vscode-bin/lake` wrapper + `scripts/vscode-bin/fast_setup_file.py`**

拦截 `lake setup-file` 请求，用 Python 脚本直接从缓存的 LEAN_PATH 构造 ModuleSetup JSON 响应，
完全跳过 Lake 的 8000+ 模块遍历。

- 首次调用通过 `lake env` 获取 LEAN_PATH（~5s），后续调用使用缓存（~50ms）
- 从文件路径自动推导模块名
- 从 stdin 读取 header JSON，解析 import 列表并在 LEAN_PATH 中定位 olean/ir/server 文件
- 响应格式与原生 `lake setup-file` 完全兼容

其他 lake 命令（build、serve 等）不受影响，直接透传给真实 lake。

**工具链级替换**：由于 `lean --server` 通过 `IO.appDir / "lake"` 直接定位 lake 二进制文件
（忽略 PATH 和 LAKE 环境变量），wrapper 安装在工具链目录
`~/.elan/toolchains/leanprover--lean4---v4.28.0/bin/lake`，原始二进制备份为 `lake.real`。

### 2026-04-08 修复 — ModuleSetup JSON 格式

- `package` 字段：从 `["LeanProject", 0]`（元组）修正为 `"LeanProject"`（字符串，`PkgId = String`）
- `options` 字段：从 `[["name", value], ...]`（数组）修正为 `{"name": value, ...}`（JSON 对象，`NameMap LeanOptionValue`）
- `imports` 字段：`None` 时省略该字段（`Option` 类型对应 JSON key 缺失）

## 2026-04-06 — 禁止 MCP 恢复上下文启动 Lean LSP，避免修改 lean/.lake

### 变更

#### `src/json2lean/config/mcp_helper.py`
- 根因进一步确认：真正会动 `lean/.lake` 的不是 `leansearch` 这类远程/搜索工具，而是 `call_all_tools_async()` 无条件启动的 Lean LSP。
- `MCPHelper` 改为惰性初始化：`LSPPool`、`LeanProjectManager`、`LLMClient` 只在对应工具真正被调用时才创建。
- `call_all_tools_async()` 改为按工具集合判断是否需要启动 Lean LSP；如果只调用搜索类工具，则完全不启动 LSP，也不触碰 `.lake`。
- `gather_recovery_context()` 改为默认只使用 search-only 工具：`lean_unified_search`、`lean_leansearch`、`lean_loogle`、`lean_leanfinder`，`all` 模式下仅额外加入 `lean_file_contents` 和 `lean_local_search`。
- 保留原有 `.lake` 目录写保护逻辑，但只在确实需要启动 LSP 的工具集合下才启用。

#### `src/json2lean/compile/compiling_fixer.py`
- MCP 工具日志列表与新的 search-only 策略保持一致，不再宣称会调用 `diagnostic/goal/hover/code_actions` 这类会触发 Lean LSP 的工具。

## 2026-04-06 — 修复 MCP 启动时 .lake/packages 被 Lean LSP 触发重建导致 .olean 删除问题

### 变更

#### `src/json2lean/config/mcp_helper.py`
- **根本原因**：`MCPHelper.start()` 启动 Lean LSP 服务器（`lake env lean --server`），LSP 检测到项目文件变动后触发 Lake 增量构建，删除/重建包依赖的 `.olean` 文件（如 Mathlib）。
- **修复**：调用 `call_all_tools_async` 前，递归收集 `project_root/.lake/packages/*/` 下所有 `lib/` 子目录，通过 `chmod a-w` 移除写权限；MCP 操作全部完成（含异常路径）后恢复原始权限。
  - 新增函数 `_collect_lake_package_lib_dirs()` — 收集需保护的目录列表（限 5000 目录）。
  - 新增函数 `_apply_lake_write_protection()` — 批量去除写权限，打印锁定数量日志。
  - 新增函数`_restore_lake_write_protection()` — 批量恢复写权限，确保 `finally` 路径必然执行。
  - `call_all_tools_async` 用外层 `try/finally` 包装，保护范围覆盖 MCPHelper 初始化、`start()`、工具调用、`shutdown()` 全阶段。
- **只保护包依赖目录**：不保护项目自身的 `.lake/build/`，LSP 仍可写入项目文件对应的构建产物。
- 新增 `import stat`。

---

## 2026-04-06 — 修复循环历史上下文 + MCP 只读安全 + 提示词更新

### 变更

#### 1. 新增 `src/json2lean/repair_history.py`
- 新模块：`RepairHistory` 类，按 entry 追踪编译修复和语义修复循环的完整历史。
- 记录每次尝试的 Lean 代码版本、错误信息、错误签名、拒绝原因、语义报告摘要。
- 格式化输出：最近 N 次（可配置，默认 3）保留完整细节，更早的历史自动摘要化。
- 内置 anti-repeat 指令：禁止重复失败策略、禁止重新引入已见错误。
- Token 预算安全：总字符量超限时渐进裁剪旧历史。

#### 2. 修改 `src/json2lean/compile/compiling_fixer.py`
- `recover_exercise()` 和 `recover_all()` 新增 `history` / `history_by_label` 参数。
- 每次尝试前将当前代码+错误记录到历史；拒绝（空输出/合约违反/语义弱化）也记录。
- `_build_prompt()` 新增 `history_block` 参数，将历史上下文注入 LLM 提示。
- 日志输出包含历史条目数。

#### 3. 修改 `src/json2lean/semantic/semantic_rewriter.py`
- `rewrite_from_report()` 新增 `history` 参数。
- `_build_prompt()` 新增 `history_block` 参数，将语义修复历史注入提示。

#### 4. 修改 `src/json2lean/config/mcp_helper.py`
- **只读安全**：新增 `_READ_ONLY_ALLOWLIST`（20 个工具）和 `_MUTATING_TOOLS`（4 个工具）。
- `call_tool()` 在调度前检查工具名，阻止 `lean_build`/`lean_apply_patch`/`lean_run_code`/`lean_multi_attempt`。
- **搜索优化**：`_extract_search_queries_from_errors()` 从编译错误文本提取搜索关键词。
- **分阶段回退策略**：诊断+聚焦上下文 → 统一搜索 → 附加搜索提供者（仅 all 模式）。
- **缓存/去重**：`_SearchCache` 在单次恢复尝试内防止重复查询。
- **调用上限**：单次恢复最多 20 个 MCP 调用。
- `gather_recovery_context()` 新增 `errors` 参数，支持错误驱动的搜索查询。

#### 5. 修改 `prompts/fixer/compiling_fixer.md`
- 新增"History"作为第 5 项输入说明。
- 新增 History 使用指令：研究先前尝试、不重复失败修复、切换策略。

#### 6. 修改 `prompts/fixer/semantic_rewrite.md`
- 新增"History section"作为第 3 项输入说明。
- Goal 部分新增 History 使用指令。

#### 7. 修改 `main.py`
- 导入 `RepairHistory`。
- 翻译阶段恢复：维护 `compile_history_by_label` dict，传递到 `_recover_combined_file_for_item()`。
- 语义循环：每个 entry 创建独立 `sem_history`，记录每个 pass 的代码/报告/拒绝，传递到 `rewrite_from_report()` 和 `_recover_combined_file_for_item()`。
- `_recover_combined_file_for_item()` 新增 `history` 参数，透传到 `recover_all()`。

### 验证
- 所有修改文件语法检查通过。
- `test/test_smoke.py` 验证：导入、RepairHistory 基本操作、摘要化、MCP 工具阻止列表均通过。
- 向后兼容：所有新参数均有默认值，现有 config 无需修改。

---

## 2026-04-05 — 稳定化修复：避免运行期 `.olean` 缺失/被重写

### 背景
- 运行 `python3 main.py ...` 时偶发出现 `Mathlib.olean does not exist`。
- 现场现象表现为 `Mathlib.ilean` 存在但 `Mathlib.olean` 缺失，导致 `import Mathlib` 失败。

### 变更
- `src/json2lean/compile/compiling_checker.py`
  - 新增 `_stable_lake_env()`，统一为 Lake 子进程注入稳定环境：
    - `LAKE_ARTIFACT_CACHE=false`
  - 以下调用统一使用该环境：
    - `lake env lean ...`（主编译）
    - `lake exe cache get!`（自动缓存恢复）
    - 恢复后的重试编译
  - 目的：避免只落地接口产物（`.ilean`）而缺失可加载目标产物（`.olean`）的失配状态。

- `src/json2lean/config/mcp_helper.py`
  - 在 `gather_recovery_context(..., tool_mode="all")` 中移除 `lean_build` 调用。
  - 目的：避免恢复上下文采集阶段触发额外构建行为，降低运行期对 `.lake` 产物的干扰。

- `config.json`
  - `recovery.mcp_tool_mode`: `dynamic` → `targeted`
  - `compile.auto_cache_recovery`: `false` → `true`
  - 目的：减少高侵入上下文操作并开启缺失产物自动恢复。

### 验证
- 语法检查通过：
  - `python3 -m py_compile src/json2lean/compile/compiling_checker.py src/json2lean/config/mcp_helper.py main.py src/json2lean/compile/compiling_fixer.py src/json2lean/models.py`
- 运行验证中，`compile-check` 错误已从 `Mathlib.olean does not exist` 转为正常 Lean 代码语义错误（如 `Unknown constant Matrix.dotProduct`），表明库产物缺失问题已解除。

## 2026-04-05 — 移除 `lake build` 编译选项

### 变更
- 删除 `lake build` 相关配置和代码路径，保留 `lake env lean` 作为唯一编译执行方式。

- `src/json2lean/compile/compiling_checker.py`
  - `compile_lean_file()` 移除参数：`use_lake_build`、`lake_build_target`
  - 删除 `use_lake_env=False` 时回退到 `lake build` 的分支
  - 删除 `build_lake_target()` 函数
  - `.olean` 自动恢复仅保留 `lake exe cache get!`，不再触发 `lake build`

- `src/json2lean/models.py`
  - `PipelineConfig` 删除字段：`compile_use_lake_build`、`compile_lake_build_target`
  - `from_dict()` 删除上述字段读取逻辑

- `main.py`
  - 所有 `compile_lean_file()` 调用移除参数：`use_lake_build`、`lake_build_target`

- `config.json`
  - `compile` 段删除键：`use_lake_build`、`lake_build_target`

### 验证
- 已执行语法检查：
  - `python3 -m py_compile main.py src/json2lean/compile/compiling_checker.py src/json2lean/models.py src/json2lean/compile/compiling_fixer.py`
  - 结果：通过

## 2026-04-05 — 实现 lake env / lake build 编译模式开关

### 变更
- `config.json` → `"compile"` 段
  - `"use_lake_env"`: 是否使用 `lake env lean` 编译（默认 `true`）
  - `"use_lake_build"`: `lake env` 禁用时是否回退到 `lake build`（默认 `false`）
  - `"lake_build_target"`: `lake build` 的目标名（默认 `"LeanProject"`）
  - `"auto_cache_recovery"`: `.olean` 缺失时自动运行 `lake exe cache get!`（默认 `true`）

- `src/json2lean/models.py`
  - `PipelineConfig` 新增字段：`compile_use_lake_env`、`compile_use_lake_build`、`compile_lake_build_target`、`compile_auto_cache_recovery`
  - `from_dict()` 从 `config["compile"]` 读取以上字段

- `src/json2lean/compile/compiling_checker.py`
  - `compile_lean_file()` 新增参数：`use_lake_build: bool = False`、`lake_build_target: str = "LeanProject"`
  - `if not use_lake_env` 分支改为：
    - `use_lake_build=True` → 调用 `build_lake_target()` 并返回其 `CompileResult`
    - 两者均为 `False` → 跳过编译，返回 `returncode=0`、无错误的成功结果

- `main.py`（5 处 `compile_lean_file()` 调用）
  - 均补充传入 `cfg.compile_use_lake_env`、`cfg.compile_use_lake_build`、`cfg.compile_lake_build_target`、`cfg.compile_auto_cache_recovery`

## 2026-04-13 — 支持 resume-only: `--no-preprocess --resume-from N`

### 变更
- `main.py`: 添加“resume-only 编译/修复”模式：当使用 `--no-preprocess` 且已存在合并的 Lean 文件并指定 `--resume-from` 时，跳过翻译，直接对每个块运行编译并在失败时尝试恢复。

### 说明
- 运行示例：`python3 main.py data/ch5.json --no-preprocess --resume-from 8` 会在已存在的合并文件上从第 8 项开始依次执行编译与恢复循环；成功/失败会写入 `logs/resume_<input>.json` 检查点。


### 编译模式对照表
| `use_lake_env` | `use_lake_build` | 行为 |
|---|---|---|
| `true` | 任意 | `lake env lean <file>`（原有行为） |
| `false` | `true` | `lake build <lake_build_target>` |
| `false` | `false` | 跳过编译，视为成功（returncode=0） |

## 2026-04-05 — 修复 Lean Mathlib .olean 文件缺失问题

### 问题
运行 `python3 main.py ...` 时持续出现：
```
object file 'Batteries/Data/Array/Match.olean' of module ... does not exist
```

### 根因分析
1. `lake exe cache get` 使用 `.ltar` 档案的 hash 与 `.trace` 文件的 hash 对比来判断"已解压"
2. `lake update` 会为所有模块创建合成的 `.trace` 文件（`"synthetic": true`），hash 与对应 `.ltar` 中的值相符
3. 这导致 `lake exe cache get` 认为 8010 个模块"已解压"，实际上 `.olean` 文件从未写入磁盘
4. `lake build Mathlib` 虽然显示"8025 jobs Fetched"，但实际 `.olean` 在内存中使用后不持久化
5. `lake env lean` 编译用户文件时需要磁盘上存在真实的 `.olean` 文件

### 修复方案
运行带强制标志的 cache 命令重新下载并解压所有 `.olean` 文件：
```bash
cd lean
lake exe cache get!
```
`get!`（带感叹号）等同于 `get --force`，强制重新解压所有 8010 个文件（含 `Batteries.Data.Array.Match` 等 FFI 模块）。

### 验证
- `lake env lean test_mathlib.lean` 退出码 0
- `python3 main.py data/Numerical_Optimization_Chp2.json --resume-from 2` 不再有 `.olean does not exist` 错误

## 2026-04-04 — 添加编译检查详细错误输出

### 变更
- `main.py`
  - 新增 `_print_compile_result()` 辅助函数，用于格式化输出编译结果的详细信息（错误数量、行号、错误消息、源代码行）
  - 在所有 `compile_lean_file()` 调用点之后添加 `_print_compile_result()` 调用，包括：
    - 第 350 行：逐项合并验证 (step_result)
    - 第 423 行：基线合并文件验证 (base_result)
    - 第 483 行：最终组合文件验证 (final_result)
    - 第 765 行：语义重写后验证 (post)
    - 第 1457 行：语义恢复后最终验证 (post)
  - 输出格式：`[compile-check] <context> ✓ OK` 或 `✗ FAIL`，后跟详细的错误/警告列表

### 效果
每次编译检查时，会输出清晰的错误诊断信息：
```
[compile-check] [item 3/11] combined file ✗ FAIL
[compile-check] Errors (1):
  [1] Line 1:0
      object file '...' of module Mathlib does not exist
      Source: import Mathlib
```

## 2026-04-01 — 调整提取顺序：hint 优先提取、最终排在末尾

### 动机
原流程最后才提取 hint，导致 definition/assumption/goal 等阶段有可能误抽取 hint 章节中的文本。改为优先提取 hint，使后续阶段只处理非 hint 的剩余文本，更彻底地隔离各种语义块。

### 修改
- `src/json2lean/preprocessor.py`
  - `_STAGES` 顺序从 `(definition, assumption, goal, hint)` 改为 `(hint, definition, assumption, goal)`；hint 成为第一个提取阶段，在 pre-masking 之后立即运行。
  - `_sort_blocks_by_position` 中"逆序查找最后一个有效 masked_text"的扫描顺序更新为 `(goal, assumption, definition, hint)`，以匹配新的阶段链顺序。
  - 模块文档字符串及 `preprocess_exercise` 的注释同步更新。
  - `_merge_stages` 的合并顺序（definition→assumption→goal→hint）保持不变，确保 hint 在初始合并列表中仍位于末尾，并由后续 `_reorder_blocks` 做最终语义排序。
- `prompts/extract_hint.md`
  - 重写为"第一提取阶段"语境：移除对先前阶段提取标记的引用，改为说明当前输入只含 `<<PLACEHOLDER>>` token；调整边界规则，改为"definitions/assumptions/goals 将在后续阶段处理"。
- `prompts/extract_definition.md`
  - 新增第 11 条：输入文本可能含有 `[HINT_EXTRACTED]` 标记（来自前置 hint 阶段），应在 `masked_text` 中原样保留。
- `prompts/extract_assumption.md`
  - Rule 2 扩展：同样忽略并保留 `[HINT_EXTRACTED]` 标记。
- `prompts/extract_goal.md`
  - Rule 2 扩展：同样忽略并保留 `[HINT_EXTRACTED]` 标记。

## 2026-04-01 — 修复重复 definition 的合并逻辑

### 问题定位
- 重复的 `definition` 主要不是因为 Stage 0 masking 失效，而是因为 `refine_assumption` / `refine_goal` 允许输出 split form（`definition` + `assumption` / `goal`），而 `_merge_stages()` 之前会无条件把其中的 `definition` 再追加一次。
- 另外，当 pre-masking 的 placeholder 恢复文本与 definition stage 的 LLM 输出归一化后相同，`_build_ordered_definitions()` 也会同时保留两份 definition。

### 修改
- `src/json2lean/preprocessor.py`
  - 在 `_merge_stages()` 中为 split form 新增 definition 去重：如果归一化后与已有 definition 等价，则跳过追加，只保留 assumption/goal 本体。
  - 在 `_build_ordered_definitions()` 中过滤与 placeholder 恢复文本重复的 LLM definition，并顺带去除 definition stage 内部的重复定义。
  - 新增 `_definition_norm_set()`、`_dedupe_definitions()`、`_append_definition_if_new()` 三个辅助函数，用统一的归一化规则处理 definition 去重。
- `test/test_validation.py`
  - 新增回归测试，覆盖 assumption/goal split form 造成的重复 definition。
  - 新增回归测试，覆盖 placeholder 恢复与 LLM definition 重复时应优先保留 placeholder 原文。

## 2026-04-01 — 用 LLM 语义重排取代启发式排序

### 变更
- `src/json2lean/preprocessor.py`
  - 删除 `_merge_stages()` 中对 `_sort_blocks_by_position()` 的调用（但保留函数本身作为内部工具，以便未来参考）。
  - 新增 `_build_reorder_prompt()`、`_validate_reorder_output()`、`_reorder_blocks()` 三个函数，实现由 LLM 判断 blocks 正确语义顺序的新 post-stage。
  - 在 `preprocess_exercise()` 合并后、校验前插入 `reorder_blocks` stage：调用 `_reorder_blocks()` 让 LLM 返回 `ordered_indices` 列表，对 `structured.blocks` 进行重排；若 LLM 多次失败则保持原顺序（graceful degradation）。
  - `preprocess_all()` 也预加载 `reorder_blocks` prompt。
  - 更新 `preprocess_exercise()` docstring 以反映新 post-stage。
- `prompts/reorder_blocks.md`：新增 reorder_blocks prompt，要求 LLM 输出 `{"ordered_indices": [...]}` 格式，依据阅读顺序与依赖顺序对 blocks 排序。

## 2026-04-01 — 修复 _sort_blocks_by_position 排序错误

### 问题
当原文一个句子（如 `"Let \(f_0,...\) be convex"`）被 definition 阶段提取出数学表达式后，assumption 阶段再次将整句（含 `[DEFINITION_EXTRACTED]` 标记）作为一整个 assumption 消耗掉。此时最终 masked_text 中只剩 `[ASSUMPTION_EXTRACTED]`，definition block 因找不到对应标记而被归入 unknown 列表追加至末尾，导致 assumption 排在 definition 前面，顺序错误。

### 修改
- `src/json2lean/preprocessor.py`：重写 `_sort_blocks_by_position()` 的 unknown 块处理逻辑。对每个无法在最终 masked_text 中定位的 block，检查其文本是否是某个已知位置 block 文本的子串；若是，则将其排在那个 block 之前（使用 `known_ordinal - 0.5` 作为虚拟序号）。无法匹配的 block 保底按 stage 顺序（definition < assumption < goal < hint）排在所有已知 block 之后。同步将 `Optional` 加入 `from typing import` 导入。

## 2026-03-31 — 按原文顺序排序提取 Block

### 修改
- `src/json2lean/preprocessor.py`：新增 `_sort_blocks_by_position()` 辅助函数，利用最后一个阶段（hint）产生的 `masked_text` 中 `[KIND_EXTRACTED]` 标记的出现顺序，对所有 block 进行全局排序，使最终的 `blocks` 列表与它们在原文中的先后顺序一致，而不再固定为"definition → assumption → goal → hint"阶段顺序。
- `_merge_stages()`：在返回 `StructuredExercise` 前调用 `_sort_blocks_by_position()` 对已合并的 blocks 排序；若无法确定顺序的 block（masked_text 缺失标记时）追加在末尾。
- `prompts/refine_assumption.md`：新增"concise splitting"规则，允许将"f: R^n → R be convex"类的混合条目拆分为 `definition` 和 `assumption` 两个字段，使 refine 产出更简洁；更新输出格式说明，支持 `{id, definition, assumption}` 和原有 `{id, text}` 两种 item 形式。

## 2026-03-31 — 强化特殊块识别 Prompt

### 修改
- 更新 `prompts/identify_special_blocks.md`，融合更细粒度的算法与优化问题抽取规则，同时保持当前预处理第 0 阶段所需的输出格式不变：仍然只返回 `blocks` 与 `masked_text`。
- 强化 optimization problem 的完整性边界要求：除了 `minimize/maximize`、目标函数、变量和约束外，还要求在同一连续块中一并吸收显式给出的定义域条件、feasible set、等价改写和直接附着的局部假设。
- 强化 algorithm 的完整性边界要求：要求尽量覆盖算法名、输入、初始化、迭代/循环结构、更新规则、停止条件和输出；同时避免把只有方法名但没有步骤内容的文字误识别为算法块。
- 明确该 prompt 在项目中的职责是“先掩码、后进入 definition/assumption/goal/hint 多阶段抽取”，因此规则侧重于块边界完整性与原文保真，而不是输出更复杂的结构化字段。

## 2026-03-31 — 删除未使用 Prompt

### 删除
- 删除 `prompts/concise_to_lean.md`（未在代码中引用）

## 2025-03-26 — 项目构建 & 端到端修复

### 新增
- **完整项目架构**：按 `src/json2lean/` 包结构重构，共 14 个模块
  - `parser.py` — JSON 解析（支持中英文字段名自动映射）
  - `preprocessor.py` — LLM 预处理（将题目改写为 Definition/Hypothesis/Goal 格式）
  - `translater.py` — LLM 翻译（Lean 4 代码生成）
  - `validator.py` — Lean 编译验证（`lake env lean`）
  - `recover.py` — LLM 自动修复循环（最多 N 次重试）
  - `api_client.py` — OpenAI API 封装（token 跟踪、流式传输自动检测）
  - `models.py` — 数据模型（Exercise, CompileResult, TokenUsage, PipelineConfig）
  - `loader.py` — JSON / 配置 / Prompt 文件加载
  - `writer.py` — .lean 文件写入
  - `comment_builder.py` — Lean 注释头构建
  - `lean_env.py` — Lean 4 环境检测
  - `main.py` — 流水线调度 & CLI 入口
  - `__main__.py` / `__init__.py` — 包入口
- **Prompt 模板**：`prompts/concise_to_lean.md`、`prompts/json_to_lean.md`、`prompts/recovery.md`
- **Lean 4 项目**：`lean/` 目录，依赖 Mathlib v4.28.0，已下载完整 oleans 缓存
- **配置示例**：`config.example.json`
- **构建配置**：`pyproject.toml`（setuptools）、`requirements.txt`
- **文档**：`README.md`（使用指南 + CLI 参数 + 架构说明）
- **示例数据**：`data/sample_math.json`（4 道中文数学题）

### 修复
- **parser.py**：新增 `_FIELD_ALIASES` 字典，自动将中文字段名（题目内容 → problem、题目ID → source_idx 等）映射为英文规范名
- **models.py**：`Exercise.__post_init__` 增加 `题目ID` / `题目内容` 回退逻辑
- **preprocessor.py**：放宽 `_validate_candidate` 校验（仅检查 `problem` 字段存在），避免因 JSON schema 差异导致预处理失败
- **validator.py**：修复只解析 stdout 的问题，现在同时解析 `stderr`，确保正确捕获编译错误
- **pyproject.toml**：修复 `build-backend` 为 `setuptools.build_meta`（原值 `setuptools.backends._legacy:_Backend` 不可用）

### 验证结果
使用 `python3 -m json2lean data/sample_math.json -o outputs` 运行全流水线：

| 文件 | 题型 | 编译状态 |
|------|------|----------|
| C001.lean | 计算题（∫₀¹ x²dx = 1/3） | ✅ 通过（完整证明） |
| P001.lean | 证明题（立方和公式） | ✅ 通过（sorry 占位） |
| P002.lean | 证明题（介值定理） | ✅ 通过（sorry 占位） |
| F001.lean | 填空题（sinx/x → 1） | ✅ 通过（sorry 占位） |

### .gitignore 更新
- 新增排除：`lean/.lake/`、`lean/lake-packages/`、`lean/build/`（Mathlib 缓存 ~6.8GB）

## 2026-03-30 — 小修改

### 修改
- 在 `src/json2lean/models.py` 中新增 `Block` 和 `StructuredExercise` 两个 dataclass，用于表示结构化 JSON 块（包含 `id`, `kind`, `text`），并添加 `from_dict()` 构造器与 `get_blocks_by_kind(kind)` 辅助方法，方便从如下格式的 JSON 数据加载和按类型筛选块。

## 2026-03-30 — 预处理输出重构为 StructuredExercise

### 修改
- **`prompts/concise_to_lean.md`**：完全重写 prompt，不再要求 LLM 改写原 JSON 的 `problem` 字段，改为要求输出 `StructuredExercise` 格式的独立 JSON，包含 `index`、`source_document` 和 `blocks` 列表（每个 block 有 `id`、`kind`、`text`）。
- **`src/json2lean/preprocessor.py`**：
  - 新增 `StructuredExercise` 的导入
  - `_build_prompt`：简化为直接拼接 base prompt 与输入 JSON，不再插入内联指令
  - `_validate_candidate`：改为校验 `StructuredExercise` 结构（`index`、`source_document`、`blocks` 字段；每个 block 需有 `id`、`kind`、`text`；至少含一个 `kind="goal"` 的块）
  - `preprocess_exercise`：解析 LLM 输出为 `StructuredExercise` 对象，赋值给 `exercise.structured`，并将 block 内容序列化为纯文本写回 `exercise.preprocessed_problem`
- **`src/json2lean/models.py`**：`Exercise` 新增 `structured: Optional[StructuredExercise] = None` 字段，由预处理步骤填充。
- **`test/run_preprocessor_test.py`**：`FakeAPIClient` 改为返回 `StructuredExercise` 格式 JSON；新增断言验证 `exercise.structured` 非空、含 blocks、含 goal 块；输出 JSON 中新增 `structured` 字段。

## 2026-03-30 — 前端 Viewer & 测试脚本增强（修订）

### 新增
- **`viewer/index.html`**：自包含 HTML 前端查看器，用于渲染 `preprocessor_output.json`。功能包括：
  - KaTeX 数学公式渲染（支持 `problem_before` 中的 LaTeX）
  - 按 block kind（definition / assumption / goal / hint）颜色标注
  - 全文搜索 & kind 过滤
  - 全部展开 / 折叠
  - 文件拖拽或手动选择加载 JSON
  - 自动从 `test/preprocessor_output.json` 加载
- **`viewer/serve.py`**：Python 本地 HTTP 服务器启动脚本，支持 `--port` 和 `--no-open` 参数

### 修改
- **`test/run_preprocessor_test.py`**：
  - `build_exercises` 改进以正确处理嵌套的 `content` 字段（从 `picks.json` 等数据源）
  - 确保 `problem_before` 输出字段填充了原始输入 JSON 中的 `problem` 内容（若存在）
  - 支持通过环境变量 `REAL_API=1` 切换使用真实 API 调用（从 `config.json` 加载配置）
  - 使用真实 API 时自动将 token 使用日志写入 `logs/token_usage_<timestamp>.json`
- **`viewer/index.html`**：优化 `problem_before` 渲染逻辑，自动检测其中的 LaTeX 命令并包装在 `$$...$$` 中以供 KaTeX 渲染

## 2026-03-30 — 预处理：四阶段串行抽取与校验增强

### 新增
- 新增四个阶段化的 Prompt 模板（每个阶段单独调用模型）：
  - `prompts/extract_definition.md` — 仅抽取 definition 并返回 `items` + `masked_text`
  - `prompts/extract_assumption.md` — 仅抽取 assumption（在 definition 掩码后的文本上运行）
  - `prompts/extract_goal.md` — 仅抽取 goal（在 assumption 掩码后的文本上运行）
  - `prompts/extract_hint.md` — 仅抽取 hint（在 goal 掩码后的文本上运行）

### 修改
- **`src/json2lean/preprocessor.py`**：重写为四阶段串行调用实现（definition → assumption → goal → hint），每阶段独立发起一次模型调用并返回结构化 `items` 与 `masked_text`；阶段间使用掩码标记（例如 `[DEFINITION_EXTRACTED]`）以防止重复抽取。
- 增加 `StageResult` dataclass 表示单阶段输出；增加 `_run_stage()`（包含重试与阶段级别校验）、`_merge_stages()`（将四阶段结果合并为 `StructuredExercise`）及 `_validate_merged()`（合并后跨 kind 校验与去重检测）。
- **校验强化**：阶段输出与合并后结果均有严格校验（字段存在性、类型、非空、goal 必须存在、跨 kind 重复检测等），不满足时触发重试或在批处理层记录失败并继续下一个题目。
- **向后兼容**：合并后的 `StructuredExercise` 与 `exercise.preprocessed_problem` 格式保持与现有 pipeline 兼容，后续 `translater.py` / `writer.py` / `validator.py` 无需改动。

### 测试
- 更新 `test/run_preprocessor_test.py` 的 `FakeAPIClient`，以模拟四阶段返回（每次调用返回 `items` + `masked_text`）。
- 新增/更新单元测试 `test/test_validation.py`，覆盖阶段输出校验与合并校验规则。

### 影响与注意事项
- 现在预处理由单次调用升级为四次串行调用，能显著降低不同 kind 之间的语义混淆，但会增加预处理阶段的 API 调用次数与延迟；建议在 config 中根据成本调整 `preprocessing_max_attempts` 与 `preprocessing_max_tokens`。
- 跨 kind 重复检测基于简单文本归一化，极端重述或同义替换可能无法完全检测到，需要模型端的高遵从性以保证理想结果。

## 2026-04-04 — 新增 `--no-mcp` 与缺失 Mathlib 的早期检测

### 变更
- **CLI**：新增 `--no-mcp` 选项以显式禁用 MCP 上下文收集（覆盖配置项 `recovery_mcp_enabled`）。
- **恢复流程**：在 `main.py` 中对合并验证（combined validation）增加对 Mathlib 相关错误的早期检测（匹配 `Mathlib`、`Mathlib.olean`、`unknown module prefix`、`object file ... does not exist` 等关键字）。当检测到项目依赖缺失时，流水线会提前 HALT 并输出可操作提示，而不是进入每题的自动修复循环（避免产生误导性的 repeated-error 报告）。

### 理由
在未配置或未安装 Mathlib 的环境中，Lean 编译会因缺少依赖而失败；此类错误不是单题的语法或证明问题，自动 recovery 循环无法修复，且会产生重复错误签名的误判。本次改动使得用户能更快发现并修复项目级依赖问题。


