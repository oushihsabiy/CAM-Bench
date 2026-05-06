# Task 生成器

此工具用于自动生成 `task.json` 配置文件。

## 使用方法

### 1. 配置 config.json

编辑 `config.json`，指定以下参数：

- `model`: 使用的单个模型名称（兼容旧配置）
- `models`: 多模型列表（推荐），支持两种写法：
  - 字符串列表：`["gpt-5.4", "gpt-4.1"]`
  - 对象列表：`[{"model":"gpt-5.4","base_url":"...","api_key":"..."}, ...]`
- `base_url`: LLM API 基础 URL（例如 "http://localhost:8000/v1"）
- `api_key`: LLM API 密钥
- `lean_cwd`: 你的 Lean 项目根目录路径（例如 "/path/to/json2lean"）
- `pass_n`: 评测通过次数（默认 3）
- `max_turns`: 最大交互轮数（默认 5）
- `max_tokens`: 单次解题请求最大输出 token 上限（默认 1000000）
- `llm_error_budget_per_sorry`: 每个 sorry 连续 LLM API 错误重试预算（默认 10，0 = 不限）
- `workers`: 并行工作数（默认 1）
- `problem_timeout`: 单题总解题时间上限（秒，默认 300）
- `lean_subdir`: 扫描子目录（默认 `"Leanproject"`）

### 2. 运行生成脚本

```bash
python generate.py
```

脚本将：
1. 读取 `config.json` 中的配置
2. 扫描 `lean_subdir` 下的 `.lean` 文件
3. 为每个 `.lean` 文件与每个模型组合生成任务条目（笛卡尔积）
4. 输出 `task.json`

如需只生成指定文件夹，可在终端传 `--include-dir`（可重复）：

```bash
python generate.py \
  --include-dir 最优化建模理论与方法 \
  --include-dir convex_optimization
```

路径解析规则：
- 相对路径先按 `lean_cwd/<lean_subdir>/...` 解析
- 若不存在，再按 `lean_cwd/...` 解析
- 也支持绝对路径

### 3. 输出结构

生成的 `task.json` 是一个 JSON 数组，每个元素包含：

```json
{
  "problem": "lean/LeanProject/path/to/problem.lean",
  "model": "gpt-5.4",
  "base_url": "http://localhost:8000/v1",
  "api_key": "EMPTY",
  "lean_cwd": "/path/to/json2lean",
  "pass_n": 3,
  "max_turns": 5,
  "max_tokens": 1000000,
  "llm_error_budget_per_sorry": 10,
  "workers": 1,
  "problem_timeout": 300
}
```

其中 `problem` 字段是相对于 `lean_cwd` 的相对路径。

## 多模型示例配置

```json
{
  "base_url": "https://rayplus.site/v1",
  "api_key": "<YOUR_API_KEY>",
  "models": [
    "gpt-5.4",
    {
      "model": "gpt-4.1",
      "temperature": 0.2,
      "max_tokens_per_call": 262144
    }
  ],
  "lean_cwd": "/root/workspace/benchmark/evaluation/lean/Leanproject",
  "pass_n": 1,
  "max_turns": 32,
  "llm_error_budget_per_sorry": 0,
  "workers": 4
}
```

## 评测与 Excel

生成 `task.json` 后，运行：

```bash
python -m eval.run_eval \
  --config eval/task.json \
  --output eval/eval_report.json
```

`run_eval` 会自动输出 Excel：`eval/eval_report.xlsx`（或你用 `--excel-output` 指定的路径）。


## 示例

假设你的 Lean 项目结构如下：

```
json2lean/
  lean/
    LeanProject/
      src/
        Foo.lean
        Bar.lean
      theorem/
        Main.lean
```

运行 `python generate.py` 后，生成的 `task.json` 将包含：

```json
[
  {
    "problem": "lean/LeanProject/src/Bar.lean",
    ...
  },
  {
    "problem": "lean/LeanProject/src/Foo.lean",
    ...
  },
  {
    "problem": "lean/LeanProject/theorem/Main.lean",
    ...
  }
]
```
