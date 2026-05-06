# code_clean

面向“提交 / 重试 / 判定”的干净脚本副本，便于后续改造成可复用工具。

## 目录

- `submit/`: 提交与调度
  - `run_batch.py`: 顺序执行一个 experiments-batch JSON
  - `run_parallel.py`: 并行运行（`slurm` / `local`）
  - `submit_batches.py`: 将大配置切分成 N 个 SLURM job
  - `submit_batches_socks.py`: SOCKS 隧道版本
  - `slurm_templates/`: `run_plan*.slurm` 模板备份

- `retry/`: 缺失与重跑
  - `check_missing.py`: 扫描缺失实验
  - `find_sorry_exps.py`: 找 only-sorry 通过样本并生成重跑列表
  - `submit_rerun_sorry.py`: 提交重跑任务

- `judge/`: 结果判定与质量检查
  - `show_results.py`: 结果总览
  - `report.py`: 按 plan/model/domain 聚合统计
  - `check_cheating.py`: 抽样检测 `sorry/axiom` 等可疑证明
  - `plan12_results.py`: strict clean pass 统计（plan1/2）

- `eval/`: 难度评测 Pipeline
  - `run_eval.py`: 主入口 CLI（复用现有 experiments JSON 格式）
  - `problem_loader.py`: 加载 Lean 文件，按 theorem/lemma 切分 sorry 块
  - `llm_client.py`: OpenAI-compatible LLM 调用封装
  - `lean_verifier.py`: 单文件 Lean CLI 验证器
  - `solver.py`: 逐一修复 sorry 的多轮 LLM 证明循环
  - `evaluator.py`: 多模型/多次运行聚合 → 难度系数计算
  - `reporter.py`: JSON 报告 + 终端表格输出
  - `examples/`: 示例配置与 demo 题目

## 设计约定

- 所有脚本去掉了项目绝对路径硬编码，默认根据当前文件位置自动定位项目根目录。
- `submit/*` 默认仍调用现有运行入口：`code/run_experiment.py`。
  - 如果你后续做完全可复用版本，可通过 `--runner` / `--exp-runner` 指向新入口。

## 快速示例

```bash
cd /public/home/ias_zwwen/wzy/icml_rebutal_2026

# 1) 提交：把 experiments 分成 20 个 job
python code_clean/submit/submit_batches.py \
  --config experiments_full.json \
  --n-jobs 20 \
  --hours 8 \
  --tag full_clean

# 2) 重试：找 only-sorry 实验并提交
python code_clean/retry/find_sorry_exps.py \
  --output experiments_rerun_sorry.json
python code_clean/retry/submit_rerun_sorry.py \
  --config experiments_rerun_sorry.json

# 3) 判定：查看汇总
python code_clean/judge/show_results.py
python code_clean/judge/report.py
python code_clean/judge/check_cheating.py --sample-size 30

# 4) 难度评测：用 eval pipeline
# 推荐流程：先生成任务（`eval/task.json`），再 dry-run，最后正式运行。
python -m eval.run_eval \
  --config eval/task.json \
  --max-turns 5 \
  --output eval/eval_report.json

# 默认不做 prior/posterior 难度评测；如需启用，显式加开关
python -m eval.run_eval \
  --config eval/task.json \
  --difficulty-assessment

# 4-1) 可显式指定 Markdown 输出（默认与 --output 同名 .md）
python -m eval.run_eval \
  --config eval/task.json \
  --output eval/eval_report.json \
  --markdown-output eval/eval_report.md

# 4a) dry-run 预览
python -m eval.run_eval \
  --config eval/task.json --dry-run

# 4b) 并行评测
python -m eval.run_eval \
  --config eval/task.json \
  --parallel 4

# 4c) 启用 Lean MCP（仅在编译失败轮次补充 goals/上下文）
python -m eval.run_eval \
  --config eval/task.json \
  --lean-mcp-enabled

# 4d) 使用 stdio 方式接入 Lean MCP
python -m eval.run_eval \
  --config eval/task.json \
  --lean-mcp-enabled \
  --lean-mcp-transport stdio \
  --lean-mcp-command "python -m your_lean_mcp_server" \
  --lean-mcp-timeout 5

# 4d-2) 使用 json2lean 风格（python 直调 lean-tools-mcp）
python -m eval.run_eval \
  --config eval/task.json \
  --lean-mcp-enabled \
  --lean-mcp-transport python

# 4e) 指定多工具选择策略（优先从 eval/mcp_config.json 读取工具列表）
python -m eval.run_eval \
  --config eval/task.json \
  --lean-mcp-enabled \
  --lean-mcp-tool-selection-strategy error_based

# 5) 三阶段难度评估（自动生成 JSON + Excel 明细）
python -m eval.run_difficulty \
  --config eval/task.json \
  --eval-report eval/eval_report.json \
  --log-dir LOG \
  --output eval/difficulty_report.json

# 可选：指定 Excel 输出路径
python -m eval.run_difficulty \
  --config eval/task.json \
  --eval-report eval/eval_report.json \
  --excel-output eval/difficulty_report_details.xlsx
```

说明：
- `run_eval` 每次完整运行后会自动导出 3 份报告：JSON（`--output`）、Excel（`--excel-output`，默认同名 `.xlsx`）和 Markdown（`--markdown-output`，默认同名 `.md`）。
- `run_eval` 默认关闭难度评测（prior/posterior）；可通过 CLI `--difficulty-assessment` 启用，或在 `task.json` 顶层配置 `"difficulty_assessment": true`。
- `run_difficulty` 每次运行后会自动导出一个 Excel（默认与 `--output` 同名 `.xlsx`）。
- Excel 除了终端展示字段外，还包含每题的先验各维度分数和后验各维度分数（并额外附带 actual 各维度）。
- Lean MCP 为可选增强：仅当前缀编译失败时调用，成功轮次不调用；若 MCP 超时/异常会自动降级为原始编译错误重试，不会中断题目流程。
- `eval/mcp_config.json` 会作为 Lean MCP 默认配置自动加载；优先级为 CLI > `task.json` 单题字段 > `eval/mcp_config.json`。
- `tool_selection_strategy` 支持 `single`、`fallback`、`sequential`、`error_based`；`lean_mcp_tools` 用于声明每个工具的 `enabled` / `method` / `extra_params`。
- 当 `lean_mcp_transport=python` 时，支持 json2lean 风格配置：
  - `lean_mcp_tools` 可直接使用工具名列表（例如 `lean_unified_search`）
  - `lean_mcp_tool_mode` 支持 `focused`/`targeted`/`all`
  - `lean_mcp_pool_size` 控制 LSP 池大小，`lean_mcp_repo_path` 可指定本地 `lean-tools-mcp` 仓库路径
- 现在也支持 `search` 类 MCP 工具；客户端会自动附带 `query` 和 `search_query` 参数，默认从 Lean 错误摘要中提炼搜索词。

示例：启用 search 类工具

```json
{
  "lean_mcp_tools": {
    "analyze_prefix": {"enabled": true, "method": "analyze_prefix", "extra_params": {}},
    "search": {"enabled": true, "method": "search", "extra_params": {}},
    "verify_proof": {"enabled": true, "method": "verify_proof", "extra_params": {}}
  },
  "tool_selection_strategy": "error_based"
}
```

## 提示词翻译模板

- 模板文件：`eval/examples/translation_prompt_template.txt`
- 适用范围：
  - `eval/solver.py` 中的 `_SYSTEM_PROMPT` / `_FIRST_TURN_USER` / `_RETRY_TURN_USER`
  - `eval/prior_scorer.py` 与 `eval/posterior_scorer.py` 的评分提示词
- 使用要点：
  - 不可改动占位符：`{block_code}` / `{prev_code}` / `{errors}`
  - 不可改动标记：`/- FILL_PROOF_HERE -/`
  - 不可改动代码块标签：```lean / ```lean4
  - 评分 JSON key 与数值范围必须保持不变

## 详细难度评分流程

`eval/run_difficulty.py` 使用“三阶段 + 排名归一化”流程对题目打分，整体分为 5 步：

### 1) 输入与数据来源

- 题目列表：来自 `--config`（`eval/task.json`）中的 experiments，按题目路径去重。
- 实际阶段数据：来自 `--eval-report`（通常是 `eval/eval_report.json`）。
- 后验阶段证明代码：从 `--log-dir`（默认 `LOG/`）里自动收集该题对应的 block 证明。

### 2) 阶段 A：先验难度 Prior（`eval/prior_scorer.py`）

对“尚未求解”的 Lean 题面（含 sorry）评分，包含静态特征 + LLM 判分：

- 静态维度
  - `hypothesis_count`
  - `sorry_block_count`
  - `statement_length`
- LLM 维度（0~4）
  - `structural_complexity`
  - `concept_complexity`
  - `formalization_gap`
  - `type_sophistication`

同一题若有多个 block，先逐 block 评分，再取“最难 block”作为该题先验分。

### 3) 阶段 B：实际难度 Actual（`eval/evaluator.py`）

从已完成评测的聚合指标中计算原始难度分（raw score），不做截断：

- `pass_rate_inv`
- `turns_norm`
- `time_norm`
- `error_div_norm`
- `model_gap`

实现入口是 `compute_raw_actual_score(pm, max_turns, weights)`，返回：

- 实际阶段原始分 `actual_raw`
- 各维度明细 `actual_dimensions`

### 4) 阶段 C：后验难度 Posterior（`eval/posterior_scorer.py`）

对“完成后的证明代码”做 LLM 评分（0~4）：

- `structure`
- `semantic`
- `library`
- `type`
- `search`

用于衡量证明的结构复杂度、语义跨度、库技巧依赖、类型系统复杂度和搜索/回溯强度。

### 5) 聚合与归一化（`eval/difficulty_aggregator.py`）

每个阶段先保留原始分，再做 rank-based normalization：

- 对每题 raw score 计算平均名次（处理并列）。
- 将名次映射到百分位区间 `[0,1]`，得到 `prior_norm` / `actual_norm` / `posterior_norm`。

然后做三阶段加权求和得到最终分数：

- 默认权重：`prior=0.20, actual=0.50, posterior=0.30`
- 支持通过 `--stage-weights` 覆盖

最终得到：

- `final_score`
- `difficulty_level`（`Easy` / `Medium` / `Hard` / `Very Hard`）

## 输出文件说明

每次运行 `run_difficulty` 会输出两份报告：

- JSON：`--output` 指定路径（默认 `eval/difficulty_report.json`）
- Excel：默认与 JSON 同名 `.xlsx`，可用 `--excel-output` 单独指定

Excel 的 `difficulty_details` 工作表包含：

- 终端汇总字段：`prior_raw`, `prior_norm`, `actual_raw`, `actual_norm`, `posterior_raw`, `posterior_norm`, `final_score`, `difficulty_level`
- Prior 全维度：`prior_hypothesis_count`, `prior_sorry_block_count`, `prior_statement_length`, `prior_structural_complexity`, `prior_concept_complexity`, `prior_formalization_gap`, `prior_type_sophistication`
- Posterior 全维度：`posterior_structure`, `posterior_semantic`, `posterior_library`, `posterior_type`, `posterior_search`
- Actual 维度：`actual_pass_rate_inv`, `actual_turns_norm`, `actual_time_norm`, `actual_error_div_norm`, `actual_model_gap`

另含 `summary` 工作表，记录生成时间、样本数、阶段权重与难度分布。
