# Changelog

## 2026-04-22 — 端到端评测报告增强（JSON + Excel + Markdown）

### 修改
- `eval/reporter.py`
	- 新增 `_build_eval_summary(metrics)`：生成全局评测汇总，包含
		- `run_pass_rate` 与 `block_pass_rate`
		- 总运行数/通过数、总块数/通过块数、总尝试数、总耗时
		- token 汇总（prompt/completion/total）与均值
		- `termination_reasons` 分布
		- `final_verify` 通过/失败/未知统计
		- `per_model` 维度汇总（runs、run pass rate、block pass rate）
	- `save_eval_report()` 顶层新增 `evaluation_summary` 字段。
	- 扩展每个 `problem.runs[]` 条目，新增 run 级字段：
		- `prompt_tokens`
		- `completion_tokens`
		- `total_tokens`
		- `termination_reason`
		- `final_verify_passed`
		- `final_verify_issues`
	- 新增 `save_eval_markdown_report()`：自动生成可读性 Markdown 报告，覆盖全局汇总、按模型汇总、问题级汇总、运行级明细，以及 prior/posterior token 汇总。

- `eval/run_eval.py`
	- 新增 CLI 参数 `--markdown-output`（默认与 `--output` 同名 `.md`）。
	- 主流程在 JSON/Excel 之后自动调用 `save_eval_markdown_report()`，每次运行完成后统一产出三份报告。
	- 终端新增 Markdown 输出路径提示。

- `README.md`
	- 新增 `--markdown-output` 示例。
	- 明确 `run_eval` 现在会自动生成 JSON + Excel + Markdown 三种报告。

### 兼容性
- 保持原有 JSON 结构主体不变；新增字段为向后兼容扩展。
- `--markdown-output` 不传时自动推导默认路径，不影响旧命令使用。

## 2026-04-22 — 修复声明块识别错乱导致 sorry 拼接污染

### 根因
`eval/problem_loader.py` 之前只用行首正则识别 `theorem/lemma/def`，遇到 `-/theorem`（注释闭合后紧贴声明）或部分缩进场景会漏识别声明起点，继而让 `block_char_end` 漂移到错误位置。该错误边界被 `eval/solver.py` 消费后，会把后续定理头拼进当前块，出现 `...hsumtheorem...` 这类粘连并污染 `sorryN_turnM.lean` 与 `_final_verify.lean`。

### 修改
- `eval/problem_loader.py`
	- `_DECL_RE` 改为声明关键字扫描，不再依赖行首锚点。
	- 新增 `_find_decl_starts()`：仅在“非注释区域 + 合法行上下文”下识别声明。
	- 新增 `_is_decl_line_context()`：支持行首/缩进声明，以及注释闭合后紧贴声明（如 `-/theorem`、`/-- ... -/theorem`）。
	- `_find_block_ranges()` 改为基于声明起点列表切分，并加入防御性裁剪：若块内再次出现声明头，截断到最早嵌套声明，避免跨块吞并。
- `eval/solver.py`
	- `_solve_one_sorry()` 增加防御性诊断日志：当目标块文本内检测到多个声明头时，输出 warning，便于快速定位边界回归。

### 验证
- 通过最小复现实验验证 `detect_sorry_items()`：
	- `-/theorem` 场景下，声明名可正确识别；
	- 声明序列不再错位。
- 对 `problem_loader.py` 与 `solver.py` 运行编辑器错误检查，均无新错误。

## 2026-04-22 — 修复块边界换行缺失导致下一个定理块无法识别

### 根因
`_find_block_ranges` 以 `^theorem/lemma/def` 正则识别块起点（`re.MULTILINE`）。当 LLM 输出的 `new_block_text` 末尾不带换行（如结尾为 `-/`），而 `working_text[block_end:]` 直接以 `theorem` 开头时，拼接后形成 `-/theorem`，导致正则无法匹配第二个定理，错误地把两个定理当成同一块处理。

### 修改
- `eval/solver.py`
	- 在 `updated_working = working_text[:block_start] + new_block_text + working_text[block_end:]` 处，当 `new_block_text` 末尾不以 `\n` 结尾且 `working_text[block_end:]` 不以 `\n` 或空字符串开头时，自动插入一个换行符作为分隔。

### 影响
- 修复 Exercise_2_21 等题目中"sorry0 通过后，sorry1 仍被识别为同一个块"导致第一个定理证明丢失的问题。
- 已手动将 `LOG/_tmp/Exercise_2_21_gpt-5.4/_final_verify.lean` 补回缺失的 `separationSet_isConvexCone` 证明。
- 已清理 Exercise_2_21_gpt-5.4 的损坏续跑状态（progress.json、working_state_after_sorry*.lean），下次运行将从 sorry0 重新开始。

## 2026-04-22 — 修复 llm_error 快速重试耗尽 max_turns

### 修改
- `eval/solver.py`
	- `_solve_one_sorry(...)` 的回合循环由 `for turn in range(...)` 改为 `while turn <= max_turns`，仅在一次有效 LLM 返回后才推进 `turn`。
	- `llm_error` 分支不再增加 `running.turns`，实现“llm_error 不计入 max_turns”。
	- 新增每个 sorry 的 LLM 错误预算：`RunningTotals.llm_error_budget_per_sorry = 10`。
	- `llm_error` 重试增加指数退避：`1s, 2s, 4s, 8s, 16s`（上限 16 秒）。
	- 当连续 LLM 错误达到预算上限时，终止原因为 `llm_error_budget_exceeded`，避免误判为 `max_turns` 耗尽。
	- 成功拿到一次 LLM 输出后会重置连续 `llm_error` 计数。
	- `solve_problem(...)` 新增对 `llm_error_budget_exceeded` 的题目级终止原因聚合。

### 效果
- API 抖动/限流时不会在极短时间内刷完 `max_turns` 并跳过当前 sorry。
- 重试节奏受控，能给后续恢复留出时间窗口；同时保留证明轮次预算给有效生成。

## 2026-04-22 — 修复 sorry 索引漂移导致无法切换到下一个 sorry

### 修改
- `eval/solver.py`
	- `_solve_one_sorry(...)` 新增参数 `global_sorry_index`，由 `solve_problem()` 外层循环索引 `i` 传入。
	- 将失败续跑、临时文件命名、`ERR_LOG`/`MCP_LOG` 记录、`BlockResult.sorry_index` 全部改为使用稳定的全局索引，而非每轮 `detect_sorry_items(working_text)` 重新编号后的局部索引。
	- `solve_problem()` 调用 `_solve_one_sorry(...)` 时显式传入 `i`，保证同一题内第 0/1/2 个 sorry 的编号在整个运行与续跑过程中保持一致。

### 效果
- 修复“`sorry0` 跑通后仍继续写到 `sorry0_turn*.lean`”问题。
- 跑完第一个 sorry 后，后续轮次会正确落到 `sorry1_turn*.lean`（及对应 `ERR_LOG/.../sorry_1/...`），可继续修第二个 sorry。

## 2026-04-22 — 续跑基准改为“最近无sorry失败轮次”

### 修改
- `eval/solver.py`
	- 调整 `_load_failed_turn_resume(...)`：
		- `next_turn` 仍取最近一轮有错误日志的失败轮次 + 1，保证不中断续跑。
		- `prev_code` / `last_compile_errors` 不再直接取最新轮次，而是从新到旧回溯到“最近一个不含 `sorry` 的失败轮次”。
		- 若最新轮次含 `sorry`，下一轮会回看更早的不含 `sorry` 版本及其错误信息。

### 效果
- 满足策略：当第 21 轮含 `sorry` 失败时，第 22 轮看到第 20 轮（或更早）最近不含 `sorry` 的源码与错误。
- 保持续跑轮次连续，不会因为基准回溯而回退执行轮次编号。

## 2026-04-22 — 失败轮次回溯到最后完整性通过版本

### 修改
- `eval/solver.py`
	- 添加追踪变量 `last_integrity_passed_code` 和 `last_integrity_passed_errors`，记录最后一个通过完整性检查的轮次。
	- 修改 `prev_code` 更新策略：
		- **通过完整性检查**（not integrity_issues）：更新基准版本，这成为后续回溯的参考点。
		- **完整性检查失败**（含sorry）：使用上次基准版本，不再传递失败的中间尝试。
	- 恢复 failed_turn_resume 时，同步初始化基准变量，保证回溯链完整。

### 效果
- **turn20**（编译失败但完整✓）→ 成为基准
- **turn21**（完整性失败）→ turn22 仍然看 turn20 的代码和错误，而不是 turn21 的
- **turn22** → LLM 在 turn20 基础上继续改进，不被失败的中间尝试迷惑

### 影响
避免"失败尝试污染后续上下文"问题，LLM 总是在最后有效的完整版本上继续，稳定地逼近正确证明。

## 2026-04-22 — 含 sorry 代码保存及上下文传递（修复质量下降问题）


### 修改
- `eval/solver.py`
	- 每轮 LLM 生成的代码都被保存到 `_tmp/sorry{i}_turn{n}.lean`，**无论是否通过完整性检查**。之前只有通过编译的代码被保存，包含 `sorry` 的代码会被丢弃，导致后续轮次无法继续改进。
	- 改变 `prev_code` 更新策略：现在**总是更新** `prev_code` 为本轮生成代码，即使包含 `sorry`。这样 LLM 在下一轮能看到上一轮的完整代码和具体错误，而不是被迫"重新思考"。

### 影响
- **修复质量下降**：turn20（编译通过）→ turn21（包含 sorry）→ turn22 时，turn22 现在能看到 turn21 的代码和错误，能继续优化而不是彻底换思路。
- 后续轮次能利用 `_load_failed_turn_resume` 从任何一轮失败点继续，而不仅是编译通过的轮次。
- LLM 的迭代过程更加连贯，避免"大幅度倒退"现象。

## 2026-04-22 — 支持从失败 turn 文件继续续跑


### 修改
- `eval/solver.py`
	- 新增 `_load_failed_turn_resume(...)`：当 `_tmp` 中存在 `sorry{i}_turn{n}.lean` 且 `ERR_LOG/.../turn_{n}.json` 存在失败记录时，自动把该轮代码和错误信息作为下一轮 LLM 输入。
	- `_solve_one_sorry(...)` 现在会从最近失败轮次的下一轮开始继续，而不是总是从 `/- FILL_PROOF_HERE -/` 模板重新开始。
	- 若已从失败轮次恢复，则跳过首轮 MCP 预取，避免把“继续第 n+1 轮”误当成首轮处理。
- `LOG/_tmp/Exercise_2_10_gpt-5.4/progress.json`
	- 删除之前误写的“已完成”进度文件，避免把尚未编译通过的 `Exercise_2_10` 直接跳过。

### 影响
- 现在执行 `python3 -m eval.run_eval --config eval/task.json --lean-mcp-enabled` 时，会把现有 `LOG/_tmp/Exercise_2_10_gpt-5.4/sorry0_turn14.lean` 视为上一轮失败结果，并从第 15 轮继续让 LLM 修改。
- 续跑依赖两类已有文件：`_tmp/sorry{i}_turn{n}.lean` 和 `ERR_LOG/{problem}/sorry_{i}/turn_{n}.json`。若两者缺一，仍会退回从模板重新开始。

## 2026-04-22 — 断点续传（Resume from LOG）

### 修改
- `eval/solver.py`
  - 新增 `_save_working_state(tmp_dir, sorry_idx, working_text)`：每个 sorry 处理完毕后，将当前 `working_text` 快照写入 `tmp_dir/working_state_after_sorry{i}.lean`。
  - 新增 `_load_resume_state(tmp_dir, problem_full_text, n_sorry_found)`：从 `progress.json` 和 `working_state` 快照重建续跑起始索引、`working_text` 与已完成的 `block_results`；`n_sorry_found` 不匹配时自动放弃续跑。
  - `solve_problem` 新增 `resume: bool = True` 参数：启用时自动尝试续跑，否则从头开始。
- `eval/run_eval.py`
  - `_run_one` 新增 `resume: bool = True` 参数并透传至 `solve_problem`。
  - CLI 新增 `--no-resume` 标志（默认启用续跑，传入该标志则从头开始）。

### 影响
- 运行中断（超时、kill、限额）后，重新执行相同配置可从上次完成的 sorry 继续，无需重算已通过的轮次。
- 旧有 `_tmp` 目录如缺少 `working_state_after_sorry*.lean` 快照，代码会自动回退到从头重建（向后兼容）。

## 2026-04-22 — Exercise_2_10 参数调优（降回合 + 单轮更深）

### 修改
- `eval/task.json`
	- 仅对 `Exercise_2_10.lean` 调整：
		- `max_turns`: `999999 -> 14`
		- 新增 `temperature: 0.4`
		- 新增 `max_tokens_per_call: 50000`

### 影响
- 限制无效长回合重试，减少总 turns。
- 提升单轮输出预算，让每轮证明有更大展开空间。
- 降低随机性，减少发散式试错。

## 2026-04-22 — 关闭 Lean 编译时间上限（verify timeout unlimited）

### 修改
- `eval/lean_verifier.py`
	- `verify_lean_file()` / `verify_lean_string()` 支持 `timeout <= 0` 或 `None` 视为不限时（传给 `subprocess.run(timeout=None)`）。
	- 修复了 `timeout=0` 会立刻超时的问题。
- `eval/run_eval.py`
	- `--verify-timeout` 默认值改为 `0`（不限时）。
	- 支持按实验条目覆盖：`task.json` 中可写 `"verify_timeout": 0`（或任意秒数）。
	- 启动日志改为在 `verify_timeout <= 0` 时显示 `verify timeout: unlimited`。

### 影响
- 不再出现 `L0:0 [error] TIMEOUT after 120.0s` 这类由默认 120s 限制引发的超时。
- 如需恢复上限，可在 CLI 传 `--verify-timeout <秒数>` 或在任务条目中配置 `verify_timeout`。

## 2026-04-22 — 首轮翻译前接入 MCP（first-turn prefetch）

### 修改
- `eval/solver.py`
	- `_solve_one_sorry()` 新增首轮 MCP 预取：进入 turn loop 前先调用 `lean_mcp_client.gather_failure_context()`，并将返回上下文写入 `last_mcp_ctx`。
	- `_FIRST_TURN_USER` 模板新增 `{mcp_sections}` 占位，首轮 prompt 也可注入 MCP 上下文，而不是仅 retry 轮次可用。
	- 新增 turn1 去重逻辑：若已执行首轮预取，则 turn1 失败后不再重复调用一次 MCP，避免同轮双调用。
	- 首轮预取的 MCP 统计和失败信息会计入本轮 attempt 记录（`mcp_call_count/mcp_failure_count/mcp_failed_tools/mcp_error_msg`）。

### 影响
- MCP 不再只在失败后才参与；首轮生成即具备检索上下文。
- 减少 turn1 重复 MCP 调用，降低无效开销。
- 首轮 MCP 超时或异常仍会降级到原流程，不中断求解主链。

## 2026-04-22 — Python MCP 上下文结构化解析（不再全部落入 raw）

### 修改
- `eval/lean_mcp_client.py`
	- 在 python transport 分支中，将 `mcp_helper` 返回的 section 文本解析为结构化 `LeanMCPContext`：
		- 检索内容写入 `search_results`
		- provider/backend 错误写入 `diagnostics`
		- 仅无法归类内容保留在 `raw`
	- 新增对 `Backend errors` 前缀的剥离逻辑：避免该错误段落混入 `search_results` 顶部。

### 影响
- `MCP_LOG` 中 `mcp_context` 字段更可读，`search_results` 不再被错误文本污染。
- 传给 LLM 的 MCP 段落更聚焦，减少噪声。

## 2026-04-22 — MCP 调用链降噪与查询修复（python/mcp_helper）

### 修改
- `eval/mcp_helper.py`
	- 搜索词提取时忽略临时文件标识（如 `mcp_prefix_xxx`），避免把无意义标识送入检索。
	- `gather_recovery_context()` 新增 `query_seed` 参数，优先使用语义种子（如 block 名）而非临时文件名。
	- 对 `lean_leansearch/lean_loogle/lean_leanfinder` 的每工具查询条数从 3 降到 2，降低噪声与冗余。
	- 将 provider 文本错误（如 `[Loogle] Error:`）计入失败工具统计，并避免把错误正文注入最终上下文小节。
- `eval/lean_mcp_client.py`
	- Python transport 调用 `gather_recovery_context()` 时传入 `query_seed=block_name`。
- `eval/mcp_config.json`
	- 默认 MCP 工具调整为 `lean_unified_search + lean_leansearch`，去除高噪声默认项。

### 影响
- MCP 检索关键词更贴近当前证明块语义，减少跑偏结果。
- MCP 上下文中错误文本污染减少，`failed_tools` 统计更准确。
- 重试提示词更聚焦，降低无关 theorem 噪声。

## 2026-04-22 — 强制通过 mcp_helper.py 调用 MCP

### 修改
- `eval/run_eval.py`
	- `_resolve_mcp_defaults()` 增加规则：当仅传入 `--lean-mcp-enabled` 且未显式指定 `--lean-mcp-transport` 时，默认强制使用 `python` transport（即走 `mcp_helper.py`）。
	- 运行日志新增 `mcp_transport` 字段，便于确认每次评测实际使用的 MCP 调用路径。

### 验证
- `--dry-run` 输出已显示：`mcp_transport=python`。

## 2026-04-22 — LeanBenchmark 接入 json2lean 风格 MCP 调用

### 修改
	- 新增 json2lean 同风格的 MCP helper，直接通过 `lean-tools-mcp` Python 包调用工具
	- 采用只读工具白名单，阻断 mutating 工具调用
	- 支持 `focused/targeted/all` 三种工具收集模式
	- 支持 `lean_mcp_tools` 精确工具列表（列表形式）
	- 新增 `transport=python` 分支，走 helper 模式调用 MCP
	- 为 Python 模式新增配置字段：`tool_mode`、`pool_size`、`mcp_repo_path`
	- Python 模式下会将当前 prefix 写入临时 `.lean` 文件，再按失败上下文采集 MCP 结果
	- 调用 MCP 时传入真实 `problem_path`，用于解析 lake 项目根目录与文件上下文
	- `--lean-mcp-transport` 新增 `python` 选项
	- 默认配置解析支持 json2lean 风格字段：`lean_mcp_tool_mode`、`lean_mcp_pool_size`、`lean_mcp_repo_path`
	- `lean_mcp_tools` 同时支持 `dict`（旧格式）和 `list`（新格式）
	- 默认切换为 `lean_mcp_transport: python`
	- 默认工具改为 json2lean 常用搜索组合：`lean_unified_search/lean_leansearch/lean_loogle/lean_leanfinder/lean_hover`
	- 新增 `lean-tools-mcp` 依赖

### 影响

## 2026-04-22 — MCP 内容完整记录到 MCP_LOG

- `eval/solver.py`
	- 新增 `_log_mcp_record()` 函数，记录 MCP 调用和返回内容
	- `_solve_one_sorry()` 添加 `mcp_log_dir` 参数
	- 当 MCP 有可用上下文时（`mcp_context_used=true`），完整记录到 `MCP_LOG/{problem_id}/sorry_{index}/turn_{turn}.json`
		- MCP 调用的工具列表（used_tools, failed_tools）
		- MCP 调用统计（call_count, failure_count）
		- MCP 返回的完整上下文（goals, diagnostics, search_results, tactics, raw）
		- 最终渲染给 LLM 的文本（mcp_rendered_for_llm）

### 影响
- 便于调试：可直观看到 MCP 每次返回了什么内容
- 观测性提升：可精确区分"没调用"vs"调用但返回空"vs"调用成功有内容"
- 不影响逻辑：MCP_LOG 仅为记录，不改变求解行为

## 2026-04-21 — 完整性检查前置，避免生成含 sorry 的临时文件

### 修改
- `eval/solver.py`
	- `_solve_one_sorry()` 中调整检查顺序：完整性检查移到编译验证之前
		- 若检测到任何 `sorry`，立即拒绝，构造失败结果，**不进行 Lean 编译**
		- 仅当完整性检查通过时（零 sorry）才进行编译验证
		- 移除了之前的 `re.sub()` 标记逻辑（不再需要）

### 影响
- 临时 Lean 文件只包含已通过完整性检查的代码（零 sorry）
- 避免生成"含 sorry + PENDING_TODO 标记"的混合临时文件
- 性能提升：含 sorry 的输出直接拒绝，不进行编译操作

## 2026-04-21 — 严格完整性检查：任何时候都禁止 sorry

### 修改
- `eval/solver.py`
	- `_check_fill_integrity()` 从"超过预期才违规"改为"任何 sorry 都违规"
		- 即使是后续占位符的 sorry，只要出现就被标记为 `contains_sorry`
		- 这确保 LLM 输出的填补部分是完整且独立的，不依赖后续待填占位符
	- `_solve_one_sorry()` 中 `prev_code` 更新逻辑改为有条件更新
		- 仅当本轮通过完整性检查时（`not integrity_issues`）才将 LLM 输出传给下一轮
		- 防止含 `sorry` 的低质代码被下一轮复用，强制模型每轮都要改进

### 影响
- 任何模型输出若包含 `sorry`（无论何处），立即被拒绝并重试
- 模型无法通过"保留待填 sorry"的策略来混过验证
- 强制模型在填补时提供完整、有效的证明片段
- 预期会增加重试轮次，但输出质量更高

## 2026-04-21 — 编译验证时移除后续待填 sorry 占位符

### 修改
- `eval/solver.py`
	- `_solve_one_sorry()` 中编译前缀处理逻辑调整：
		- 在验证 LLM 输出时，移除块内后续待填的 `sorry` 标记
		- 用 `sorry -- PENDING_TODO` 替代，防止后续占位符干扰当前填充部分的验证
		- MCP 调用仍基于完整的 `prefix_for_compile`（含后续 sorry），以便诊断上下文完整

### 影响
- 编译验证只针对当前填充部分，减少虚假编译失败（因为后续 sorry 导致的失败）
- 提高单轮修复的验证准确性：若当前填充正确，即使后续有 sorry 占位符也会通过

## 2026-04-21 — Prompt 增强：禁止新 sorry + 名称可解析性约束

### 修改
- `eval/solver.py`
	- `_SYSTEM_PROMPT` 新增硬约束：当前填充的证明中禁止使用 `sorry`。
	- `_SYSTEM_PROMPT` / `_FIRST_TURN_USER` / `_RETRY_TURN_USER` 新增名称可解析性规则：
		- 使用任意标识符前，必须可在本地上下文或 Mathlib 中解析。
		- 若名称不可解析，必须先在当前证明中定义或先证明辅助引理，再使用。
	- `_build_mcp_sections` 中 `## Relevant Theorems` 警告补充相同约束，避免 search 结果被直接误用。

### 影响
- 降低模型在修复中再次引入 `sorry` 的概率。
- 降低“臆造名称/未知常量”类错误；若名称不存在，模型被明确引导先定义或先证明。

## 2026-04-21 — 修复 Retry 时占位符丢失问题

### 问题
在多轮修复流程中，第二轮及以后的 retry 提示词中，`prev_code` 已被 LLM 上一轮的输出替换，不再包含 `/- FILL_PROOF_HERE -/` 占位符。
这导致：
- 提示词指示 LLM "Fix ONLY the `/- FILL_PROOF_HERE -/` proof"，但给出的代码中根本没有这个占位符
- 两者形成逻辑矛盾，可能导致 LLM 困惑和错误修复

### 修改
- `eval/solver.py`
	- 扩展 `_RETRY_TURN_USER` 提示词模板，同时显示原始 `block_template`（含占位符）和上一轮的 `prev_code`（不含占位符）
	- 修改 prompt.format() 调用，传入 `block_template=block_template` 参数
	- 提示词改为："## Original Template (with placeholder)" + "## Your Previous Attempt"，使 LLM 能清晰看到占位符位置及上一轮的错误尝试

### 影响
- LLM 在 retry 时获得完整的参考信息：既知道占位符在哪里，又知道上一轮的错误
- 指令与代码一致，避免因信息不对称导致的模型困惑
- 预期可提高多轮修复的成功率

## 2026-04-21 — 添加 ERR_LOG 日志记录功能

### 修改
- `eval/solver.py`
	- 添加 `_get_problem_id()` / `_log_attempt_record()` 辅助函数。
	- `_solve_one_sorry()` 新增参数：`problem: Problem` / `err_log_dir: Path`。
	- 每轮尝试后立即调用 `_log_attempt_record()` 将完整报错信息写入 `ERR_LOG/{problem_id}/sorry_{index}/turn_{turn}.json`。
	- `solve_problem()` 调用时传入 `problem` 和 `err_log_dir=Path("ERR_LOG")`。

### 日志结构
```
ERR_LOG/
├── Exercise_2_1/
│   ├── sorry_0/
│   │   ├── turn_1.json
│   │   ├── turn_2.json
│   │   └── ...
│   ├── sorry_1/
│   │   └── ...
└── Exercise_3_12/
    └── ...
```
每个 JSON 文件包含：turn / passed / elapsed_sec / token 计数 / error_types / mcp_context_used / 代码与错误内容。

### 影响
- 每次证明尝试的完整报错信息自动持久化，便于事后分析失败原因。
- 按题目和 sorry 分层组织，便于快速定位特定问题的错误模式。

## 2026-04-21 — integrity_issues 也触发 MCP 失败上下文增强

### 修改
- `eval/solver.py`
	- MCP 触发条件从“仅 `vr.passed == False`”扩展为“`vr.passed == False` 或存在 `integrity_issues`”。
	- 当出现完整性问题（如 `introduced_sorry`）时，会将其追加到 `retry_errors`，并作为 `gather_failure_context(..., error_summary=...)` 的输入。
	- 下一轮重试的 `last_compile_errors` 改为保存合并后的 `retry_errors`（包含完整性问题），让模型可见并利用该反馈。

### 影响
- 即使前缀编译通过，但输出引入了 `sorry` / 禁止关键字等完整性问题，MCP 也会被调用。
- `error_based` 策略可利用 `integrity_issues` 关键词做更有针对性的工具路由与检索。

## 2026-04-21 — MCP 默认策略与提示词约束调优

### 修改
- `eval/mcp_config.json`
	- `tool_selection_strategy` 从 `all` 调整为 `error_based`。
	- 启用 `suggest_tactics`，形成 `analyze_prefix + search + suggest_tactics` 的默认组合。
- `eval/solver.py`
	- `_SYSTEM_PROMPT` / `_FIRST_TURN_USER` / `_RETRY_TURN_USER` 新增约束：禁止输出解释性注释、自然语言推理和代码块外文本。

### 影响
- MCP 调用顺序会按错误类型动态路由，减少不必要的全工具串行调用。
- 首轮与重试轮都更偏向“纯 Lean 代码输出”，降低出现大段说明性注释与占位文本的概率。

## 2026-04-21 — 增加 search 类 MCP 工具选项

### 修改
- `eval/lean_mcp_client.py`
	- 默认工具列表新增 `search`。
	- 在失败上下文采集时自动生成 `query` / `search_query` 参数，供 search 类 MCP 直接使用。
	- `error_based` 策略新增对 `search` 的优先级选择，特别用于 `unknown constant`、`failed to synthesize` 等更像检索类的问题。
- `eval/mcp_config.json`
	- 新增 `search` 工具模板项，可直接启用。
- `README.md`
	- 补充 search 类 MCP 的说明和配置示例。

### 影响
- 现在可以在不改代码的前提下，通过 `lean_mcp_tools.search.enabled=true` 接入搜索型 MCP 工具。
- search 工具会收到更适合检索的查询参数，不再只拿到前缀源码。

## 2026-04-21 — run_eval 接入 mcp_config.json 并支持多工具选择策略

### 修改
- `eval/run_eval.py`
	- 新增 `--lean-mcp-config`，默认自动读取 `eval/mcp_config.json` 作为 MCP 默认配置。
	- 新增 `--lean-mcp-tool-selection-strategy`。
	- MCP 配置优先级改为：CLI > `task.json` 单题字段 > `eval/mcp_config.json`。
	- 支持从配置中读取 `lean_mcp_tools` 与 `tool_selection_strategy`，并透传给 `LeanMCPClient`。
- `eval/lean_mcp_client.py`
	- 新增多工具配置：`tools` / `tool_selection_strategy`。
	- 支持 `single` / `fallback` / `sequential` / `error_based` 策略。
	- 新增通用工具调用与失败聚合逻辑，可按策略调用 `analyze_prefix` / `suggest_tactics` / `verify_proof`。
- `eval/solver.py`
	- 前缀编译失败后改为通过 `gather_failure_context()` 获取 MCP 上下文。
	- 统计真实工具调用次数与失败次数，并打印失败工具列表。
- `eval/mcp_config.json`
	- 新增 `lean_mcp_tools` 与 `tool_selection_strategy` 模板字段。
- `README.md`
	- 补充 `mcp_config.json` 自动加载、多工具配置和策略说明。

### 影响
- 现在可以在 `eval/mcp_config.json` 统一声明 MCP 工具集合，再由 `task.json` 单题覆盖。
- 多工具策略已经实际生效，不再局限于固定调用 `analyze_prefix`。

## 2026-04-21 — 新增 MCP 配置模板文件

### 修改
- `eval/mcp_config.json`（新增）
	- 新增一份 Lean MCP 配置模板，覆盖当前 `mcp_helper` / `LeanMCPConfig` 的全部可配置项：
		- `lean_mcp_enabled`
		- `lean_mcp_transport`
		- `lean_mcp_endpoint`
		- `lean_mcp_command`
		- `lean_mcp_timeout`
	- 字段名与 `eval/run_eval.py` 当前支持的实验配置覆盖字段保持一致，便于直接复制到 `eval/task.json` 的单题配置中使用。

### 说明
- 当前程序不会自动读取 `eval/mcp_config.json`；该文件作为统一模板存在。
- 若需要自动加载该文件并与 CLI / `task.json` 合并，可以在后续继续接入。

## 2026-04-21 — 证明阶段接入 Lean MCP + 新增翻译提示词模板

### 修改
- `eval/lean_mcp_client.py`（新增）
	- 新增 Lean MCP 适配层，支持 `http` 与 `stdio` 两种传输。
	- 统一请求协议：`method=analyze_prefix`，携带 `prefix_text` 与定位信息。
	- 返回结构化上下文：`goals` / `diagnostics` / `raw`，并提供 prompt 文本裁剪。
- `eval/solver.py`
	- `_solve_one_sorry()` 新增可选参数 `lean_mcp_client`。
	- 仅在前缀编译失败时调用 MCP，获取上下文并拼接到下一轮重试错误信息。
	- MCP 失败时仅打印 warning 并降级，不中断题目。
	- 新增 attempt 级字段 `mcp_context_used`，新增题目级 MCP 统计字段（调用次数/失败次数/耗时）。
- `eval/run_eval.py`
	- 新增 CLI 参数：
		- `--lean-mcp-enabled`
		- `--lean-mcp-transport {http,stdio}`
		- `--lean-mcp-endpoint`
		- `--lean-mcp-command`
		- `--lean-mcp-timeout`
	- 支持从实验配置按题覆盖 `lean_mcp_*` 字段。
	- 将 MCP 客户端透传到 `solve_problem()`。
- `eval/reporter.py`
	- `summary.json` 新增 MCP 字段：`mcp_enabled` / `mcp_calls` / `mcp_failures` / `mcp_time_ms`。
	- `eval_report` 的 run 明细与 timeline 新增 MCP 使用信息。
- `eval/examples/translation_prompt_template.txt`（新增）
	- 新增面向本项目的翻译提示词模板：
		- Solver 提示词翻译模板（system/first-turn/retry）
		- Prior/Posterior 评分提示词翻译模板
	- 明确保留规则：占位符、Lean 代码块标签、`/- FILL_PROOF_HERE -/`、JSON key 与分数范围。
- `README.md`
	- 新增 Lean MCP 使用示例（HTTP/stdio）。
	- 新增翻译提示词模板说明与使用要点。

### 影响
- 证明重试在失败轮次可获得更丰富的 Lean 上下文（goals/diagnostics），提高修复针对性。
- MCP 属于可选增强，默认关闭，不影响现有流程。
- 提示词翻译可复用统一模板，降低误译占位符与输出约束的风险。

## 2026-04-21 — 修复 LLM 报错后 retry 时 prompt 构建 bug

### 修改
- `eval/solver.py`
  - `_solve_one_sorry()` 中，`prev_code` / `last_compile_errors` 仅在 LLM **正常返回代码**后更新。
  - LLM 报错（API 429、超时等）时两者保持不变，导致下一轮 retry 自动退化为 first-turn prompt（重新提出原始任务）。
  - 原有 bug：把 `"LLM_ERROR: HTTP 429..."` 当 Lean 编译错误传给模型，导致模型误改证明。

### 影响
- LLM API 临时故障后 retry 时，模型收到的上下文与第一次提问完全一致，不会被无意义的 API 错误信息干扰。

---

## 2026-04-21 — LLM 报错时输出堆栈并继续重试（不跳过题目）

### 修改
- `eval/solver.py`
	- 在 `_solve_one_sorry()` 的 LLM 调用异常分支中，新增完整 traceback 终端输出：
		- 打印 `[Solver] LLM ERROR - sorry <idx>, turn <turn>`
		- 打印 `traceback.format_exc()` 的完整堆栈。
	- 行为改为：`LLM_ERROR` 不再 `break` 当前 `sorry`，而是 `continue` 到下一轮重试。
	- 仅当全局限额触发（`max_tokens` / `problem_timeout`）时才停止该 `sorry`。
	- 若后续全部 `sorry` 修复成功且最终全文件验证通过，题目级 `termination_reason` 统一回写为 `completed`，避免被中途的 `llm_error` 误标。

### 影响
- API 波动（如 429、超时、临时网络错误）时，流程会自动重试当前题目，不会因为一次 LLM 异常直接放弃该题。
- 终端可直接看到具体异常堆栈，便于定位问题来源。

## 2026-04-21 — 重构为顺序前缀编译模式（Sequential Prefix-Compilation）

### 背景
重新设计整个"填补 sorry + 验证"流程，改为严格的**顺序前缀编译**模式：对每个 sorry token
单独编译从文件头到该 sorry 所在块末尾的前缀文件（`lake env lean`），不依赖错误过滤。

### 修改

#### `eval/problem_loader.py`
- 新增 `SorryItem` dataclass：单个 sorry 出现位置（char_offset, line_no, col_no, block 范围）。
- 新增 `_build_comment_mask(text)`：字符级注释掩码，支持 `--` 行注释和 `/- -/` 嵌套块注释。
- 新增 `detect_sorry_items(text) -> list[SorryItem]`：检测所有非注释 sorry，返回源码顺序列表。
- 保持原有 `SorryBlock`、`load_problem()`、`replace_block()` 完全不变（向后兼容）。

#### `eval/solver.py`（完整重写）
- 新增 `RunningTotals` dataclass：文件级跨所有 sorry 的累计计数器
  （turns、tokens、elapsed），用于实时进度和限额检测。
- `BlockResult`：新增 `sorry_index`、`termination_reason` 字段。
- `SolveResult`：新增 `n_sorry_found`、`termination_reason` 字段。
- **新增 `_solve_one_sorry()`**：对单个 sorry token 做多轮 LLM 修复。
  - 仅将本 sorry 替换为 `/- FILL_PROOF_HERE -/`，块内其余 sorry 保持原样。
  - 编译目标为**前缀文件** = `working_text[:block_start] + new_block_text`（不含后续声明）。
  - 通过判定：`vr.passed AND _check_fill_integrity(...)` 同时满足。
  - 通过后更新 `working_text`；失败则保持不变。
  - 每轮更新 `RunningTotals` 并检查 token/time 限额。
- **重写 `solve_problem()`**：
  - 调用 `detect_sorry_items()` 获取 n 个 sorry。
  - 每次迭代重新检测 `working_text` 中的剩余 sorry，通过 `target_idx = i - passed_so_far` 精确定位当前目标（支持失败跳过和 LLM 顺带多填）。
  - 每个 sorry 尝试后写 `tmp_dir/progress.json`（实时进度）。
  - 全部解决后执行最终全文件重验证（`_final_verify.lean`）。
- **移除 `_solve_one_block()`**（已被 `_solve_one_sorry()` 取代）。
- 更新 prompt 模板：明确要求仅填充占位符，不触碰块内其他 sorry。

#### `eval/run_eval.py`
- `_build_model_cfg()`：per-call token 限额改从 `max_tokens_per_call` 字段读取（默认 32768），
  `max_tokens` 字段语义变更为文件级 token 总预算。
- `_run_one()`：新增 `default_max_tokens` 参数；从 exp 读取 `max_tokens` 作为总预算传给 `solve_problem()`。
- 新增 `--max-tokens` CLI 参数（默认 0 = 不限）。
- 日志输出新增 `sorry=`、`tokens=`、`reason=` 字段。

#### `eval/reporter.py`
- `save_solve_result()` 写出的 `summary.json` 新增字段：
  - `n_sorry_found`（检测到的 sorry 总数）
  - `termination_reason`（结束原因：completed / limit_exceeded / compile_stuck / llm_error）
  - 每个 `block_details` 条目新增 `sorry_index`、`termination_reason`。

### 关键行为变化

| 方面 | 旧行为 | 新行为 |
|---|---|---|
| 验证范围 | 全文件（过滤其他 block 的错误） | 前缀文件（不过滤，直接以编译结果为准） |
| sorry 粒度 | 按 theorem/lemma 块（一块含多个 sorry 整体修复） | 按单个 sorry token（每个 sorry 独立一轮 LLM + 编译） |
| token 预算 | max_tokens = per-call 限制 | max_tokens = 文件级总预算；per-call 由 max_tokens_per_call 控制 |
| 进度持久化 | 仅完成后写 summary.json | 每个 sorry 完成后实时写 progress.json |
| termination_reason | 无 | completed / limit_exceeded / compile_stuck / llm_error / auto_solved |

### 运行示例

```bash
# dry-run（不调用 LLM）
python -m eval.run_eval --config eval/task.json --dry-run --log-dir /tmp/test_eval

# 真实运行（单并发，限 3 轮/sorry）
python -m eval.run_eval --config eval/task.json --log-dir LOG --max-turns 3 --parallel 1
```

## 2026-04-21 — 局部编译也优先使用 `lake env lean`

### 需求
- 局部编译（每轮 block 验证）与最终编译保持一致，优先走 Lake 环境，避免依赖路径差异。

### 修改
- `eval/lean_verifier.py`
	- 新增 `_find_lake_root()`：当未显式传入 `lean_cwd` 时，从待验证文件目录向上自动查找 `lakefile.lean` / `lakefile.toml`。
	- `verify_lean_file()` 改为：
		- 有 `lean_cwd` 或可自动探测到 Lake 根目录时，统一使用 `lake env lean <file>`。
		- 仅在完全找不到 Lake 项目根时才回退到 `lean <file>`。

### 影响
- 局部验证与 `final verification` 的编译环境更一致，减少“局部看起来通过、整体因依赖环境差异失败”的概率。

## 2026-04-21 — 移除 API 请求和证明轮次限制

### 问题
- 评测和评分阶段默认对 API 请求、Lean 验证、单题求解都设了超时和轮次上限（`timeout=120s`、`max_turns=5`、`problem_timeout=300s` 等），在复杂题目或网络延迟场景下容易被打断。

### 修改
- `eval/llm_client.py`
  - `generate_with_usage()` 和 `generate()` 的 `timeout` 参数改为 `float | None = None`（默认无超时）。
  - 调用 `urllib.request.urlopen(req, timeout=timeout)` 时，若 `timeout=None` 则阻塞等待（无限等待）。
- `eval/solver.py`、`eval/prior_scorer.py`、`eval/posterior_scorer.py`
  - 所有 `generate_with_usage()` 调用显式传入 `timeout=None`，确保 LLM 请求不被中断。
- `eval/generate_task/config.json`
  - `max_turns`: 5 → 999999
  - `problem_timeout`: 300 → 1000000000

### 影响
- 评测和评分阶段对长时间 API 请求、多轮修复、Lean 编译都不再设强制超时，允许充分尝试。用户仍可通过 Ctrl+C 手动中断或在命令行用 `--max-turns` / `--problem-timeout` / `--verify-timeout` 覆盖。

## 2026-04-21
- `eval/lean_verifier.py`: `error_summary` 回退路径改为合并 stderr+stdout 取最后 20 条非空行，避免只展示 warning 行而隐藏真实 error。

## 2026-04-21 — Lean 验证改为 `lake env lean`

### 问题
- 评测阶段验证 Lean 文件时，直接调用 `lean <file>`，在部分环境下不会自动带上 Lake 依赖路径，出现 `No directory 'Mathlib' or file 'Mathlib.olean'`。

### 修改
- `eval/lean_verifier.py`
	- `verify_lean_file()` 在提供 `lean_cwd` 时，优先改为调用 `lake env lean <file>`。
	- 无 `lean_cwd` 场景保留 `lean <file>` 兜底。
	- 缺少可执行文件时，错误提示从 `lean executable not found` 扩展为 `lean/lake executable not found`。

### 影响
- 在正确的 Lean 项目目录（含 `lakefile.lean`）下执行时，Mathlib 与项目依赖将通过 Lake 环境自动注入，减少导入路径错误。

## 2026-04-21 — `final_verify_issues` 输出具体编译失败细节

### 问题
- 部分 `summary.json` 中出现 `"final_verify_issues": ["compile errors: "]`，没有具体错误内容，难以定位失败原因。

### 修改
- `eval/lean_verifier.py`
	- 增强 `VerifyResult.error_summary`：
		- 优先输出可解析的 Lean 错误行；
		- 若没有可解析错误，回退输出进程级细节（`returncode`、`stderr`、`stdout` 截断内容）；
		- 兜底返回 `unknown verifier failure`，避免空字符串。
- `eval/solver.py`
	- `final_verify_issues` 中 `compile errors` 的错误摘要截断长度由 200 提升到 2000，保留更多上下文。

### 影响
- `summary.json` 的 `final_verify_issues` 将更稳定地包含具体失败信息（例如 return code、stderr 片段或 Lean 具体报错），便于快速排查。

## 2026-04-21 — 严格证明验证：杜绝假阳性

### 问题
- `solver.py` 的 `block_passed` 判定有兜底条件 `vr.passed or (len(block_errors)==0 and not sorry)`，导致 Lean 编译实际失败的证明也可能被标记为通过（如 Exercise_2_15 中模型幻觉了不存在的 lemma 名称 `convex_monotoneExtension` 等，但 block 仍被判定为 passed）。

### 修改
- `eval/lean_verifier.py`
  - 新增 `_CHEAT_PATTERNS` 正则列表和 `check_proof_integrity(code)` 函数（借鉴 `judge/check_cheating.py` 的 `check_lean_file()` 检测逻辑），逐行检测 `sorry`/`axiom`/`admit`/`native_decide`（跳过注释行）。
- `eval/solver.py`
  - **块级判定严格化**：删除 `vr.passed or (...)` 兜底分支，改为 `len(block_errors)==0 and len(integrity_issues)==0`，即本 block 零编译错误且代码无可疑关键字才算通过。
  - **全文件最终重编译**：所有 block 各自通过后，对完整文件做一次 `verify_lean_string()` + `check_proof_integrity()` 的最终验证。如果不通过则将全部 block 降级为失败，打印明确原因。
  - `SolveResult` 新增 `final_verify_passed` 和 `final_verify_issues` 字段。
- `eval/reporter.py`
  - `save_solve_result()` 的 `summary.json` 新增 `final_verify_passed` 和 `final_verify_issues` 字段。

## 2026-04-21 — eval_report 与 Excel 增加每题 token 消耗统计

### 需求
- 在 `eval_report.json` 与对应 Excel 中输出每道题的 token 消耗。

### 修改
- `eval/llm_client.py`
	- 新增 `Usage` 数据结构与 `generate_with_usage()`，在兼容流式与非流式响应时解析 `usage` 字段。
	- 保留原 `generate()`，内部调用 `generate_with_usage()` 以保持兼容。
- `eval/solver.py`
	- `AttemptRecord`、`BlockResult`、`SolveResult` 新增 `prompt_tokens` / `completion_tokens` / `total_tokens`。
	- 每轮调用 LLM 后累计 token，按 block、按题目汇总。
- `eval/evaluator.py`
	- `ProblemMetrics` 新增 token 聚合字段：`total_prompt_tokens`、`total_completion_tokens`、`total_tokens`、`avg_tokens`、`max_tokens`。
	- 在 `compute_metrics()` 中按该题全部 runs 聚合 token 统计。
- `eval/prior_scorer.py`、`eval/posterior_scorer.py`
	- 切换为 `generate_with_usage()`，记录先验/后验评分阶段的 token 用量。
- `eval/run_eval.py`
	- `_compute_prior_posterior_details()` 输出先验与后验 token 字段。
- `eval/reporter.py`
	- `save_eval_report()` 输出每题 solve token、prior/posterior token 以及 `total_tokens_all`。
	- `save_eval_excel()` 在 `problems` 表新增 token 列；在 `block_details` 表新增 run 级 token 列。
	- `save_solve_result()` 的 LOG `summary.json` 同步加入 token 字段。

### 影响
- 评测后可直接在 JSON 和 Excel 中查看每道题 token 成本，并区分 solve 阶段与先验/后验评分阶段消耗。

## 2026-04-21 — eval_report 增加先验/后验维度评分输出

### 需求
- 在 `eval_report.json` 与对应 Excel 中，补充先验与后验难度的每一项维度评分。

### 修改
- `eval/run_eval.py`
	- 新增先验/后验评分 LLM 配置参数：`--judge-model`、`--judge-base-url`、`--judge-api-key`、`--judge-temperature`。
	- 新增 `_build_judge_cfg()`：优先使用上述参数；未提供时回退到 `task.json` 第一条实验的模型配置。
	- 新增 `_build_best_proof_code()`：从同题多次运行中选最佳结果并拼接 block 最终代码用于后验评分。
	- 新增 `_compute_prior_posterior_details()`：对每道题计算先验 raw + 7 维、后验 raw + 5 维，并汇总为报告附加字段。
	- 输出阶段将该附加字段传入 `save_eval_report()` / `save_eval_excel()`。
- `eval/reporter.py`
	- `save_eval_report()` 新增参数 `prior_posterior_by_problem`，每题写入：
		- `prior.raw_score` + `prior.dimensions`
		- `posterior.raw_score` + `posterior.dimensions`
	- `save_eval_excel()` 新增参数 `prior_posterior_by_problem`，在 `problems` sheet 增加列：
		- 先验：`prior_raw`、`prior_hypothesis_count`、`prior_sorry_block_count`、`prior_statement_length`、`prior_structural_complexity`、`prior_concept_complexity`、`prior_formalization_gap`、`prior_type_sophistication`
		- 后验：`posterior_raw`、`posterior_structure`、`posterior_semantic`、`posterior_library`、`posterior_type`、`posterior_search`

### 影响
- 运行 `run_eval` 后，`eval_report.json` 与 `.xlsx` 均包含先验/后验每个维度的评分，便于直接做维度级分析与排查。

## 2026-04-20 — 评测结果增加完整明细 JSON + Excel 输出

### 问题
- `run_eval.py` 评测完成后仅输出聚合指标 JSON，缺少每次运行、每个 block 的具体数据（通过轮次、耗时、错误类型等），不便排查和分析。
- 没有 Excel 输出，不方便筛选和对比。

### 修改
- `eval/reporter.py`
  - `save_eval_report()`: JSON 报告新增 `runs` 字段，包含每次运行的 model、all_passed、elapsed 及每个 block 的 passed/attempts/first_pass_turn/timeline 等完整明细。
  - 新增 `save_eval_excel()`: 输出 Excel 表格，Sheet 1 "problems" 每题一行含所有聚合指标，Sheet 2 "block_details" 每 block 每次运行一行含 block 级别详情。
- `eval/run_eval.py`
  - 新增 `--excel-output` 参数（默认与 `--output` 同名 `.xlsx`）。
  - 评测结束后自动调用 `save_eval_excel()` 输出 Excel。

### 影响
- 评测后同时生成 `eval_report.json`（含完整明细）和 `eval_report.xlsx`（双 Sheet），可直接用于分析和排查。

## 2026-04-20 — 修复 run_difficulty 路径解析与实际阶段静默全零问题

### 问题
- `eval/run_difficulty.py` 在汇总题目列表时，仅使用命令行 `--lean-cwd` 作为默认值；当 `task.json` 里每条实验单独提供 `lean_cwd` 且未传 `--lean-cwd` 时，相对路径题目不会被正确拼接，先验阶段可能大量 `file not found` 并回退为 0 分。
- 实际阶段读取 `eval_report.json` 时路径风格不一致（相对/绝对或未标准化）会导致匹配失败，题目被标记 `NOT FOUND` 并静默回退 0 分，容易出现整批 `actual.raw_score = 0`。

### 修改
- `eval/run_difficulty.py`
	- 新增 `_canonical_problem_path()`，统一题目路径规范化（按每条实验自己的 `lean_cwd` 解析并输出稳定绝对路径）。
	- 修复 `_unique_problems()`：按每条实验配置读取 `lean_cwd`，不再只依赖全局 `--lean-cwd`。
	- 强化 `_load_eval_report()`：同时建立“原始路径键 + 规范化路径键”映射，提高 `eval_report` 匹配鲁棒性。
	- 实际阶段新增缺失统计告警：当题目不在 `eval_report` 中时，输出汇总 warning，明确提示回退为 0 分的数量。

### 影响
- 避免由于路径解析错误造成先验阶段全 0。
- 降低实际阶段因路径不一致导致的大面积 `NOT FOUND`。
- 当 `eval_report` 与当前任务集不一致时，日志会明确提示缺失比例，便于快速定位数据来源问题。

## 2026-04-20 — 解题 token 上限限制为 1M

### 修改
- `eval/llm_client.py`
	- 新增常量 `MAX_SOLVE_TOKENS = 1_000_000`。
	- 在 `ModelConfig.__post_init__()` 中对 `max_tokens` 做标准化并强制截断到 1M。
	- 在 `generate()` 发起请求前再次执行上限保护，确保实际发送给 API 的 `max_tokens` 不超过 1M。
- `eval/generate_task/generate.py`
	- 生成 `task.json` 时新增 `max_tokens` 字段透传，默认值为 `1000000`。
- `eval/generate_task/config.json`
	- 配置样例新增 `"max_tokens": 1000000`。
- `eval/generate_task/README.md`
	- 补充 `max_tokens` 与 `problem_timeout` 参数说明。
	- 输出 JSON 示例中新增 `max_tokens` 字段。

## 2026-04-20 — README 补充详细难度评分流程文档

### 修改
- `README.md`
	- 新增“详细难度评分流程”章节，完整说明：
		- 输入来源（`task.json` / `eval_report.json` / `LOG`）
		- 阶段 A 先验评分（静态维度 + LLM 维度）
		- 阶段 B 实际评分（`compute_raw_actual_score` 与 actual 维度）
		- 阶段 C 后验评分（证明代码 LLM 五维）
		- rank-based normalization 与三阶段加权聚合
		- 最终等级划分与输出字段
	- 新增“输出文件说明”，明确 JSON/Excel 输出路径规则和 Excel 全部列字段。

## 2026-04-19 — 难度评估自动导出 Excel 明细

### 需求
- 每次运行难度评估后，除终端汇总外，自动生成 Excel 表格。
- Excel 需包含每道题先验与后验每一个维度的评分。

### 修改
- `eval/reporter.py`
	- 清理重复定义，保留单一版本的 `save_difficulty_report()` / `print_difficulty_report()`。
	- 新增 `save_difficulty_excel()`：导出 `.xlsx`，包含：
		- 终端表格字段（Prior/Actual/Posterior raw+norm、Final、Level）
		- 先验 7 维：`hypothesis_count`、`sorry_block_count`、`statement_length`、`structural_complexity`、`concept_complexity`、`formalization_gap`、`type_sophistication`
		- 后验 5 维：`structure`、`semantic`、`library`、`type`、`search`
		- 附加 actual 各维度（便于分析）
	- 增加 `summary` 工作表记录权重与难度分布。
- `eval/run_difficulty.py`
	- 新增参数 `--excel-output`。
	- 每次运行自动调用 `save_difficulty_excel()` 导出 Excel。
	- 未指定时默认输出到与 `--output` 同名 `.xlsx`。
- `README.md`
	- 新增 `run_difficulty` 示例与 Excel 输出说明。
- `requirements.txt`
	- 新增 `openpyxl>=3.1.0` 依赖声明。

### 说明
- Excel 导出依赖 `openpyxl`（已通过安装并实际运行验证）。

## 2026-04-17 — 三阶段难度评估系统 (Prior / Actual / Posterior)

### 新增文件

- `eval/prior_scorer.py` — **先验评分器**：对含 `sorry` 的 Lean 源文件做静态分析（假设数量、sorry block 数、语句长度）及 LLM 四维度评分（structural_complexity / concept_complexity / formalization_gap / type_sophistication，各 0-4），取各 block 最大值后加权生成 raw score。
- `eval/posterior_scorer.py` — **后验评分器**：对完成证明后的代码做 LLM 五维度评分（structure / semantic / library / type / search，各 0-4），从 LOG 目录自动收集最优证明代码。
- `eval/difficulty_aggregator.py` — **三阶段聚合器**：rank-based normalization（average rank → percentile 映射到 [0,1]）；三阶段加权 `prior:0.20, actual:0.50, posterior:0.30`；输出 `DifficultyResult` 含各阶段原始/归一化分数及最终分级（Easy/Medium/Hard/Very Hard）。
- `eval/run_difficulty.py` — **主入口 CLI**：argparse 命令行工具，支持 `--stage prior,actual,posterior` 选择阶段、`--eval-report` 复用已有评测结果、`--judge-model/--judge-base-url` 指定 LLM judge、`--stage-weights` 覆盖权重、`--dry-run` 预览。
- `eval/examples/difficulty_stage_weights.json` — 三阶段权重示例配置。

### 修改文件

- `eval/evaluator.py` — 新增 `compute_raw_actual_score(pm, max_turns, weights)` 函数，从已有 `ProblemMetrics` 提取五维度原始分（不截断），供聚合器使用。
- `eval/reporter.py` — 新增 `save_difficulty_report()` 和 `print_difficulty_report()` 函数，输出三阶段难度报告 JSON 及终端汇总表。

---

## 2026-04-16 — 修复 LLM 调用失败导致评测 0% 通过率

### 问题
`eval/llm_client.py` 的 `generate()` 函数存在两个问题导致所有 LLM 调用返回 403 (Cloudflare 1010)：
1. 缺少 `User-Agent` header，被 Cloudflare bot 检测拦截。
2. API 端点强制要求 `stream: true`，但原代码发送的是非流式请求，导致 400 错误。

### 修复 (`eval/llm_client.py`)
- 请求 header 中增加 `User-Agent`。
- payload 中增加 `"stream": True`。
- 新增 SSE（Server-Sent Events）流式响应解析逻辑，拼接所有 `data:` 行中的 `delta.content`。
- 保留对非流式响应的兼容回退。

### 修复 (`eval/run_eval.py`)
- `_run_one()` 中 `problem` 为相对路径时，自动基于 `lean_cwd` 解析为绝对路径。

---

## 2026-04-16 (更新)

### 新增 `eval/generate_task/` 任务配置生成工具

在 `eval/` 目录下新增 `generate_task/` 子文件夹，包含自动生成 `task.json` 的工具：

- `generate_task/config.json` — 配置文件示例，包含 model、base_url、api_key、lean_cwd、pass_n、max_turns、workers 等参数
- `generate_task/generate.py` — 主生成脚本，读取 config.json 并扫描 lean_cwd/lean/LeanProject 目录下的所有 .lean 文件，自动生成 task.json
- `generate_task/README.md` — 使用说明文档
- `generate_task/__init__.py` — 包初始化

使用方法：编辑 `config.json` 配置参数，运行 `python3 generate.py` 即可自动生成 task.json。

---

## 2026-04-16

### 新增 `eval/` 难度评测 Pipeline

新增完整的 Lean 题目难度评测模块 `eval/`，包含以下文件：

- `eval/__init__.py` — 包初始化
- `eval/problem_loader.py` — 加载 Lean 文件，按 theorem/lemma 切分 sorry 块（排除注释行）
- `eval/llm_client.py` — OpenAI-compatible LLM 调用封装（纯标准库 urllib）
- `eval/lean_verifier.py` — 单文件 Lean CLI 验证器，解析错误类型/位置
- `eval/solver.py` — 逐一修复 sorry 的多轮证明循环（每块独立 max_turns 轮）
- `eval/evaluator.py` — 多模型/多次运行聚合，计算 6 维难度指标 + 综合难度系数
- `eval/reporter.py` — JSON 持久化 + 终端富文本表格输出
- `eval/run_eval.py` — 主 CLI 入口，复用现有 experiments JSON 格式
- `eval/examples/experiments_eval.json` — 实验配置示例
- `eval/examples/demo_problem.lean` — 含 sorry 的 demo Lean 文件
- `eval/examples/difficulty_weights.json` — 难度权重配置示例

评测维度：pass_rate、avg_turns、time、error_diversity、proof_length、model_gap。

同步更新了 `README.md` 中的目录说明与快速示例。
