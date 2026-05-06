# 预处理 Pipeline 详细说明

本文档描述 `src/json2lean/preprocess/` 包的完整预处理流程。该 pipeline 将原始数学习题 JSON 转换为扁平化记录（flat-record）格式，输出到 `preprocessed_data/<input_stem>.json`。

---

## 总览

```
原始题目文本
    │
    ▼
Stage 0a: 提示语提取（hint extraction）
    │   → 带索引标记的文本 + hints 记录
    ▼
Stage 0b: 专有名词提取（technical-term extraction）
    │   → defn 记录（仅优化领域专有名词，基于 hint-masked 文本）
    ▼
Stage 1: 特殊块提取（special-block extraction）
    │   → opt_prob / algo 记录（带命名）+ 占位符替换后的文本
    ▼
Stage 2: 定理构造（theorem construction）
    │   → thm 记录（占位符替换 + 自然语言修复）
    ▼
Stage 3（可选）: 归一化（normalization）
    │   → 全部记录统一为标准数学英语
    ▼
输出: List[FlatRecord] → JSON 文件
```

---

## 输出 Schema

每条记录遵循以下格式：

```json
{
  "index": 0,
  "source": "Numerical_Optimization",
  "source_idx": "Exercise 3.1",
  "kind": "thm",
  "content": "Let f be strongly convex. Then ...",
  "term": "strongly convex"    // 仅 defn / opt_prob / algo 类型有此字段
}
```

`kind` 取值范围：`thm`、`defn`、`opt_prob`、`algo`、`hints`

---

## 各阶段详细说明

### Stage 0a: 提示语提取

| 项目            | 内容                                                                |
| ------------- | ----------------------------------------------------------------- |
| **文件**        | `hint_extraction.py`                                              |
| **入口函数**      | `_run_hint_extraction(client, problem_text, exercise_label, ...)` |
| **Prompt 模板** | `prompts/preprocess/extract_hint.md`                              |
| **验证函数**      | `validators._validate_hint_output()`                              |
| **输入**        | 原始题目文本                                                            |
| **输出**        | `StageResult(items=[{id, text}], masked_text="...")`              |

**逻辑：**

1. 调用 LLM 识别题目中的提示信息（"Hint:"、"Note:"、"you may"等触发词）
2. 每个提示被提取为独立条目，原文中替换为索引标记 `[HINT1_EXTRACTED]`、`[HINT2_EXTRACTED]`……
3. 验证器确认每条提示对应一个索引标记出现在 `masked_text` 中
4. 返回的 `masked_text` 将作为下一阶段的输入

### Stage 0b: 专有名词提取

| 项目            | 内容                                                                      |
| ------------- | ----------------------------------------------------------------------- |
| **文件**        | `definition.py`                                                         |
| **入口函数**      | `_run_definition_extraction(client, problem_text, exercise_label, ...)` |
| **Prompt 模板** | `prompts/preprocess/extract_technical_term.md`                          |
| **验证函数**      | `validators._validate_definition_output()`                              |
| **输入**        | Stage 0a 输出的 `hint_masked_text`（已去除提示标记）                                |
| **输出**        | `List[Dict]`，每个元素含 `term`、`definition`、`source`                         |

**逻辑：**

1. 调用 LLM 从 hint-masked 文本中提取**优化领域专有名词**（如 "strongly convex"、"Armijo condition"）
2. 两步提取：先提取文中有严格定义的术语（`source: "in_text"`），再补充文中使用但未定义的术语（`source: "standard"`）
3. 排除通用数学词汇（domain、function、set 等）、题目局部对象名、变量声明、函数设置
4. **不修改原文**
5. 验证器确认 `term` 和 `definition` 均为非空字符串，`source` 为 `"in_text"` 或 `"standard"`

### Stage 1: 特殊块提取

| 项目            | 内容                                                                  |
| ------------- | ------------------------------------------------------------------- |
| **文件**        | `masking.py`                                                        |
| **入口函数**      | `_run_masking_stage(client, problem_text, exercise_label, ...)`     |
| **Prompt 模板** | `prompts/preprocess/identify_special_blocks.md`                     |
| **验证函数**      | `validators._validate_masking_output()`                             |
| **输入**        | Stage 0a 输出的 `masked_text`（带 hint 标记）                               |
| **输出**        | `MaskingResult(masked_text="...", placeholders=[Placeholder(...)])` |

**逻辑：**

1. 调用 LLM 识别完整的优化问题公式和算法流程
2. 每个块被分配一个**简洁数学名称**（`assigned_name`，2-6 词，例如 "fractional convex program"）
3. 原文中替换为占位符 `<<OPT_PROBLEM_1>>`、`<<ALGORITHM_1>>` 等
4. 保留已有的 hint 索引标记
5. 验证器确认每个块包含 `token`、`kind`、`original_text`、`assigned_name` 字段
6. 构建 `Placeholder` 对象列表（含 `source_position` 用于排序）

### Stage 2: 定理构造

| 项目            | 内容                                                                                |
| ------------- | --------------------------------------------------------------------------------- |
| **文件**        | `theorem.py`                                                                      |
| **入口函数**      | `_run_theorem_construction(client, masked_text, hint_items, placeholders, ...)`   |
| **辅助函数**      | `_build_theorem_prompt(base_prompt, problem_text, hint_items, placeholders, ...)` |
| **Prompt 模板** | `prompts/preprocess/construct_theorem.md`                                         |
| **验证函数**      | `validators._validate_theorem_output()`                                           |
| **输入**        | Stage 1 的 `masked_text`（同时包含 hint 标记和特殊块占位符）                                      |
| **输出**        | `List[Dict]`，每个元素含 `content`                                                      |

**逻辑：**

1. 构建包含占位符上下文的增强 prompt（包含 hint 标记列表和特殊块占位符 → 名称的映射）
2. 调用 LLM：
   - 删除所有 `[HINTi_EXTRACTED]` 标记
   - 将 `<<OPT_PROBLEM_1>>` 等占位符替换为 `assigned_name`
   - 进行自然语言修复，使文本可读且语法正确
3. 如遇多子题（(a)/(b)/(c) 形式），拆分为多条定理
4. 验证器确认至少产出一条定理，且每条的 `content` 非空

### Stage 3（可选）: 归一化

| 项目            | 内容                                                         |
| ------------- | ---------------------------------------------------------- |
| **文件**        | `normalization.py`                                         |
| **入口函数**      | `_run_normalization(client, records, exercise_label, ...)` |
| **Prompt 模板** | `prompts/preprocess/normalize_record.md`                   |
| **验证函数**      | `validators._validate_normalize_output()`                  |
| **输入**        | 全部 `FlatRecord` 的 JSON 序列化                                 |
| **输出**        | 更新后的 `List[FlatRecord]`（原地修改 `content` 和 `term`）           |

**逻辑：**

1. 将所有记录序列化为 JSON 传给 LLM
2. LLM 统一为标准数学英语（标准符号、无库特有解释、不过度解释）
3. 验证器确认返回的记录数量匹配，每条 `content` 非空
4. 如归一化失败，静默回退到未归一化的记录

---

## Pipeline 编排

### 单题处理：`pipeline.preprocess_exercise()`

| 步骤  | 调用                             | 说明                                                                                 |
| --- | ------------------------------ | ---------------------------------------------------------------------------------- |
| 1   | `_run_hint_extraction()`       | 提取提示，生成 `hint_masked_text`                                                         |
| 2   | `_run_definition_extraction()` | 从 hint-masked 文本中提取优化领域专有名词                                                        |
| 3   | `_run_masking_stage()`         | 从 hint masked 文本中提取特殊块                                                             |
| 4   | `_run_theorem_construction()`  | 从 masked 文本构造定理                                                                    |
| 5   | 组装 `FlatRecord` 列表             | 按顺序: hints → opt_prob/algo → defn → thm                                            |
| 6   | `_run_normalization()`（可选）     | 归一化全部记录                                                                            |
| 7   | 反向兼容更新                         | 更新 `exercise.structured`、`exercise.preprocessed_problem`、`exercise.raw["problem"]` |

### 批量处理：`pipeline.preprocess_all()`

1. 加载所有 prompt 模板（通过 `PROMPT_NAMES` 映射）
2. 遍历每个 exercise，调用 `preprocess_exercise()`
3. 支持重试（`JSON2LEAN_PREPROCESS_EXERCISE_RETRIES` 环境变量控制）
4. 收集所有记录的字典，写入 `preprocessed_data/<input_stem>.json`
5. 返回处理失败的 exercise label 列表

---

## 文件结构

```
src/json2lean/preprocess/
├── __init__.py            # 包入口，re-export 全部公共 API
├── _common.py             # 共享常量（PROMPT_NAMES）和工具函数（build_stage_prompt）
├── models.py              # 数据类：StageResult, Placeholder, MaskingResult, FlatRecord
├── validators.py          # 各阶段输出的验证函数
├── hint_extraction.py     # Stage 0a: 提示语提取
├── definition.py          # Stage 0b: 专有名词提取
├── masking.py             # Stage 1: 特殊块提取
├── theorem.py             # Stage 2: 定理构造
├── normalization.py       # Stage 3: 归一化
├── pipeline.py            # 编排器：preprocess_exercise / preprocess_all / reindex_records
└── PIPELINE.md            # 本文档
```

---

## Prompt 模板

| 模板文件                                            | 对应阶段     | 内部 key              |
| ----------------------------------------------- | -------- | ------------------- |
| `prompts/preprocess/extract_hint.md`            | Stage 0a | `hint`              |
| `prompts/preprocess/extract_technical_term.md`  | Stage 0b | `definition`        |
| `prompts/preprocess/identify_special_blocks.md` | Stage 1  | `special_blocks`    |
| `prompts/preprocess/construct_theorem.md`       | Stage 2  | `construct_theorem` |
| `prompts/preprocess/normalize_record.md`        | Stage 3  | `normalize`         |

---

## 下游集成

- `main.py` 调用 `preprocess_all()` 进行批量预处理
- `translater._kind_hint()` 根据 `kind` 字段返回 Lean 声明约束
- `semantic/declaration_policy.validate_top_level_contract()` 根据 `kind` 验证 Lean 代码结构
- `kind="hints"` 的记录在翻译阶段被跳过（不生成 Lean 代码）
