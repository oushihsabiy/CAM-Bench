# Lean File Splitter

将 Lean 项目文件按 sections 进行拆分。

## 功能

此工具可以将原始的 Lean 文件（包含多个 `section`）拆分为多个独立的 Lean 文件，其中：

1. **目录结构**：每个原始文件名对应一个文件夹
2. **文件拆分**：每个 `section` 生成一个单独的 `.lean` 文件
3. **文件头**：每个生成的文件自动添加：
   ```lean
   import Mathlib
   noncomputable section
   ```

## 使用方法

### 基础用法

使用默认输入/输出目录运行：

```bash
python3 lean_splitter.py
```

默认目录：
- 输入：`projects/json2lean/lean/LeanProject`
- 输出：`projects/LEAN/LeanProject`

### 自定义目录

指定输入和输出目录：

```bash
python3 lean_splitter.py \
  --input-dir /path/to/input \
  --output-dir /path/to/output
```

## 示例

假设输入目录结构如下：

```
json2lean/lean/LeanProject/
  ch5.lean          # 包含 Exercise_5_2, Exercise_5_4, 等 sections
```

运行脚本后，输出目录结构为：

```
LEAN/LeanProject/
  ch5/
    Exercise_5_2.lean
    Exercise_5_4.lean
    Exercise_5_6.lean
    ...
```

其中每个 `.lean` 文件都包含相应 section 的完整内容，并自动添加了头部：

```lean
import Mathlib

noncomputable section

-- Exercise_5_2

[section content here]
```

## 工作流程

1. **读取**：从源目录读取所有 `.lean` 文件
2. **解析**：识别并提取每个文件中的 `section SectionName ... end SectionName` 块
3. **生成**：为每个 section 创建独立的 `.lean` 文件
4. **输出**：按原文件名创建文件夹，放入对应的拆分文件

## 注意事项

- 脚本只处理 `section ... end` 块，嵌套的 section 会正确处理
- 文件编码为 UTF-8
- 输出目录如不存在会自动创建
