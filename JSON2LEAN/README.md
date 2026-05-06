# json2lean

将 JSON 格式数学题数据转换为 Lean 4 文件，并提供编译修复与语义修复循环。

## 功能概览

- 单文件增量生成：将一个输入 JSON 产出为一个合并 Lean 文件（默认在 `lean/LeanProject/<input_stem>.lean`）。
- 可恢复运行：支持 checkpoint 续跑（`--resume`、`--resume-from`、`--resume-translate`）。
- 编译修复循环：编译失败时自动进入 LLM 修复（可结合 MCP 检索上下文）。
- 语义审查循环：对 block 做 semantic review + rewrite，并可再次触发编译修复。
- 后处理：支持仅后处理模式与 LLM 注释重写策略。
- Token 追踪：记录每次调用和按题目聚合统计。

## 目录结构（核心）

```text
json2lean/
├── main.py
├── config.example.json
├── settings.json
├── prompts/
├── src/json2lean/
│   ├── __main__.py
│   ├── block_parser.py
│   ├── loader.py
│   ├── models.py
│   ├── parser.py
│   ├── translater.py
│   ├── writer.py
│   ├── repair_history.py
│   ├── postprocess_lean.py
│   ├── preprocess/
│   ├── compile/
│   ├── semantic/
│   └── config/
├── data/
├── lean/
└── logs/
```

## 环境要求

- Python: `>=3.10`（`pyproject.toml`）
- Lean 4 + Lake
- 可选 MCP 依赖：`lean-tools-mcp`（建议 Python 3.11+）

## 安装

```bash
pip install -r requirements.txt
# 或
pip install -e .
```

若启用 MCP（`settings.json` 的 `recovery.mcp_enabled` 或 `translation.mcp_enabled` 为 `true`），建议：

```bash
python3.11 -m venv .venv3.11
source .venv3.11/bin/activate
pip install -r requirements.txt
# 或安装可选依赖
pip install -e ".[mcp]"
```

## Lean 初始化

```bash
# 安装 elan
curl https://elan-init.trycloudflare.com/elan/elan-init.sh -sSf | sh

# 安装稳定工具链
elan default leanprover/lean4:stable

# 验证
lean --version
lake --version
```

初始化 Lean 项目（若尚未创建）：

```bash
mkdir lean && cd lean
lake init LeanProject math
lake build
cd ..
```

## 配置文件

### 1) `config.json`（凭据）

从模板复制：

```bash
cp config.example.json config.json
```

字段示例：

```json
{
	"api_key": "YOUR_API_KEY_HERE",
	"base_url": "https://api.openai.com/v1",
	"model": "YOUR_MODEL_HERE",
	"llm_backend": "api",
	"codex_cli": {
		"bin": "bin/codex",
		"workdir": "lean",
		"model": "YOUR_CODEX_MODEL_HERE",
		"reasoning_effort": "high",
		"disable_plugins": true,
		"max_retries": 3,
		"retry_backoff_base_seconds": 1.0,
		"retry_backoff_max_seconds": 8.0,
		"call_log_dir": "logs/codex_cli_calls",
		"stages": ["recovery"]
	}
}
```

说明：

- `llm_backend = "api"`：全部阶段走当前 OpenAI-compatible HTTP API。
- `llm_backend = "codex_cli"`：当前版本只把 `recovery` 与 `semantic` 两个阶段切到 repo-local `codex` CLI；预处理与翻译仍走 API。
- `codex_cli.workdir` 建议保持为 `lean`，这样 agent 会在 Lake 工程根目录里工作。
- `codex_cli.disable_plugins = true`：默认关闭 Codex 启动时的远程插件同步，避免 API-key-only 环境下因 OAuth 插件同步失败导致请求中断。
- `codex_cli.max_retries` 与 `retry_backoff_*`：控制 `codex exec` 的自动重试策略（用于断流/短暂网络波动）。
- `codex_cli.call_log_dir`：记录每次 `codex exec` 的完整调用日志（prompt/输出/stderr/stdout）。
- 注意：`codex_cli` 后端依赖 provider 的 `/responses` 流式完成事件（`response.completed`）。若你的网关只稳定支持 `chat.completions`，请继续使用 `llm_backend = "api"`。

## Codex CLI 初始化

若要启用 `codex_cli` 后端，先在仓库内完成一次登录：

```bash
cd /root/workspace/benchmark/JSON2LEAN
source /root/workspace/benchmark/.venv/bin/activate
bash scripts/codex_login.sh login --with-api-key
```

仓库内 wrapper 会：

- 使用 repo-isolated `.codex_home/`
- 自动从当前 `config.json` 同步 `config.toml` / `auth.json`
- 自动注册 `lean-lsp` MCP，并将 `LEAN_PROJECT_PATH` 指向 `lean/`

### 2) `settings.json`（运行参数）

`main.py` 会加载 `settings.json` 并叠加到默认配置上。常用字段：

- `preprocessing.enabled` / `preprocessing.max_attempts`
- `translation.mcp_enabled` / `translation.mcp_tool_mode` / `translation.mcp_tools`
- `semantic.enabled` / `semantic.max_rounds`
- `recovery.max_retries` / `recovery.mcp_enabled` / `recovery.mcp_tool_mode` / `recovery.mcp_tools`
- `lean.toolchain_dir` / `lean.timeout_seconds`
- `compile.use_lake_env` / `compile.auto_cache_recovery`

## 使用方式

```bash
# 默认管线
python3 main.py data/picks.json --config config.json

# 模块入口
python3 -m json2lean data/picks.json --config config.json

# 指定输出目录
python3 main.py data/picks.json -o lean/LeanProject --config config.json

# 跳过预处理
python3 main.py data/picks.json --no-preprocess --config config.json

# 跳过验证
python3 main.py data/picks.json --no-validate --config config.json

# 跳过自动修复
python3 main.py data/picks.json --no-recover --config config.json

# 仅语义循环（在已有合并 Lean 文件上）
python3 main.py data/ch9_9_12_21.json --semantic-only --config config.json

# 仅后处理
python3 main.py data/ch9_9_12_21.json --postprocess-only --config config.json

# 续跑
python3 main.py data/picks.json --resume --config config.json

# 从指定条目续跑
python3 main.py data/picks.json --resume-from 12 --config config.json

# 启用 codex_cli（仅 recovery）
python3 main.py data/picks.json --config config.codex.json
```

## Pipeline 简述

```text
JSON -> parse -> (optional preprocess) -> translate block-by-block ->
compile validate -> (optional recover loop) -> semantic review/rewrite loop -> postprocess
```

说明：

- 输出是“单个合并 Lean 文件”，不是每题一个文件。
- `--semantic-only` 会跳过预处理/翻译，仅对现有合并文件执行语义循环。
- `--postprocess-only` 只做后处理并退出。

## 修复历史策略

当前修复历史由 `src/json2lean/repair_history.py` 管理：

- 严格仅保留最近 `5` 条完整历史（编译修复和语义修复都使用该策略）。
- 更早条目直接丢弃，不再摘要注入。
- 同时保留失败模式汇总（如重复错误签名、拒绝原因）用于 anti-repeat 提示。

## 日志与产物

- 结果文件：`lean/LeanProject/<input_stem>.lean`
- token 日志：运行结束汇总到 `logs/token_usage_<timestamp>.json`；API 调用过程中实时追加到 `logs/token_usage.jsonl`
- 恢复/语义 checkpoint：`logs/` 下 `resume_*.json` 与 `semantic_resume_*.json`
- 语义报告：`review_log/<input_stem>_semantic_report_round*.json`

## 常见问题

- Q: `--semantic-only` 报找不到输出文件？
	- A: 需先跑一次正常翻译流程生成合并 Lean 文件，再执行 `--semantic-only`。

- Q: 为什么 `--no-translate` 没有效果？
	- A: 当前单文件输出模式下该参数仅兼容保留，实际会被忽略（代码中有提示）。

- Q: 如何降低修复次数？
	- A: 可在 CLI 用 `--max-recovery-retries` 覆盖，或在 `settings.json` 调整 `recovery.max_retries`。
