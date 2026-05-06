#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""problem_loader.py: 加载 Lean 文件，定位所有 sorry 块并逐一切分。"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class SorryBlock:
    """一个含 sorry 的 theorem/lemma 块。"""
    index: int                  # 在文件中的块序号（0-based）
    name: str                   # theorem/lemma 名称
    start_line: int             # 块起始行号（1-based）
    end_line: int               # 块结束行号（1-based，含）
    raw_text: str               # 块原文
    sorry_count: int            # 该块内 sorry 数量

    def text_with_placeholder(self) -> str:
        """将块中 sorry 替换为占位标记，帮助 LLM 定位。"""
        return re.sub(r"\bsorry\b", "/- FILL_PROOF_HERE -/", self.raw_text)


@dataclass
class Problem:
    """一道 Lean 题目。"""
    path: Path
    full_text: str
    blocks: list[SorryBlock] = field(default_factory=list)
    total_sorry_count: int = 0


# ---------------------------------------------------------------------------
# 块切分：按 theorem / lemma 声明分割文件
# ---------------------------------------------------------------------------

_DECL_RE = re.compile(
    r"\b(noncomputable\s+def|theorem|lemma|def)\s+(\S+)",
)


def _extract_decl_name(raw_name: str) -> str:
    """从声明头提取声明名，去掉结尾常见分隔符。"""
    return raw_name.rstrip(":").rstrip("(").rstrip("{")


def _is_decl_line_context(text: str, pos: int) -> bool:
    """检查声明关键字是否位于合法行上下文中。"""
    line_start = text.rfind("\n", 0, pos) + 1
    prefix = text[line_start:pos].strip()
    # 允许行首声明、缩进声明，以及注释刚闭合后紧贴声明：`-/theorem ...`
    return prefix == "" or prefix.endswith("-/")


def _find_decl_starts(text: str) -> list[tuple[int, str]]:
    """返回非注释区域内所有声明起点与名称。"""
    comment_mask = _build_comment_mask(text)
    decls: list[tuple[int, str]] = []
    for m in _DECL_RE.finditer(text):
        start = m.start()
        if comment_mask[start]:
            continue
        if not _is_decl_line_context(text, start):
            continue
        decls.append((start, _extract_decl_name(m.group(2))))
    return decls


def _find_block_ranges(text: str) -> list[tuple[int, int, str]]:
    """返回 [(start_offset, end_offset, decl_name), ...]"""
    decls = _find_decl_starts(text)
    if not decls:
        return []

    ranges: list[tuple[int, int, str]] = []
    for i, (start, name) in enumerate(decls):
        end = decls[i + 1][0] if i + 1 < len(decls) else len(text)
        # 防御性裁剪：若块内再次出现声明头，截断到最早位置，避免跨块吞并。
        nested = _find_decl_starts(text[start + 1:end])
        if nested:
            end = start + 1 + nested[0][0]
        ranges.append((start, end, name))
    return ranges


def _offset_to_line(text: str, offset: int) -> int:
    """将字符偏移量转换为 1-based 行号。"""
    return text[:offset].count("\n") + 1


def _count_sorry(text: str) -> int:
    """统计非注释行中 sorry 出现次数。"""
    count = 0
    for line in text.splitlines():
        stripped = line.lstrip()
        if stripped.startswith("--"):
            continue
        # 去掉行内注释 -- 之后的部分
        code_part = line.split("--")[0]
        count += len(re.findall(r"\bsorry\b", code_part))
    return count


def load_problem(path: str | Path) -> Problem:
    """
    加载一道 Lean 文件，返回 Problem 含所有 sorry 块。

    如果文件中没有明确的 theorem/lemma 声明，则将整个文件视为一个块。
    """
    path = Path(path)
    text = path.read_text(encoding="utf-8")
    total_sorry = _count_sorry(text)

    ranges = _find_block_ranges(text)
    blocks: list[SorryBlock] = []

    if not ranges:
        # 整个文件当作一个块
        if total_sorry > 0:
            blocks.append(SorryBlock(
                index=0,
                name=path.stem,
                start_line=1,
                end_line=text.count("\n") + 1,
                raw_text=text,
                sorry_count=total_sorry,
            ))
    else:
        for idx, (start, end, name) in enumerate(ranges):
            chunk = text[start:end]
            n_sorry = _count_sorry(chunk)
            if n_sorry == 0:
                continue
            blocks.append(SorryBlock(
                index=idx,
                name=name,
                start_line=_offset_to_line(text, start),
                end_line=_offset_to_line(text, max(end - 1, start)),
                raw_text=chunk,
                sorry_count=n_sorry,
            ))

    return Problem(
        path=path,
        full_text=text,
        blocks=blocks,
        total_sorry_count=total_sorry,
    )


def replace_block(full_text: str, block: SorryBlock, new_text: str) -> str:
    """在完整文件文本中，将指定块原文替换为 new_text。"""
    return full_text.replace(block.raw_text, new_text, 1)


# ---------------------------------------------------------------------------
# 精细 sorry 定位：逐 token 定位，支持前缀编译模式
# ---------------------------------------------------------------------------

@dataclass
class SorryItem:
    """文件中一个具体的 sorry token 出现位置。"""
    index: int              # 文件内全局顺序编号（0-based）
    char_offset: int        # 在文件文本中的字符偏移量（对应 working_text）
    line_no: int            # 1-based 行号
    col_no: int             # 1-based 列号
    block_name: str         # 所在声明块的名称
    block_char_start: int   # 所在块在文件中的起始偏移（含）
    block_char_end: int     # 所在块在文件中的结束偏移（不含）


def _build_comment_mask(text: str) -> list[bool]:
    """
    构建字符级注释掩码：True 表示该字符在注释内。

    支持：
    - `-- ...` 行注释
    - `/- ... -/` 块注释（允许嵌套）
    """
    n = len(text)
    mask = [False] * n
    i = 0
    while i < n:
        # 行注释 -- ...
        if text[i] == '-' and i + 1 < n and text[i + 1] == '-':
            while i < n and text[i] != '\n':
                mask[i] = True
                i += 1
            continue
        # 块注释 /- ... -/ （嵌套）
        if text[i] == '/' and i + 1 < n and text[i + 1] == '-':
            depth = 1
            mask[i] = True
            mask[i + 1] = True
            i += 2
            while i < n and depth > 0:
                if i + 1 < n and text[i] == '/' and text[i + 1] == '-':
                    depth += 1
                    mask[i] = mask[i + 1] = True
                    i += 2
                elif i + 1 < n and text[i] == '-' and text[i + 1] == '/':
                    depth -= 1
                    mask[i] = mask[i + 1] = True
                    i += 2
                else:
                    mask[i] = True
                    i += 1
            continue
        i += 1
    return mask


def detect_sorry_items(text: str) -> list[SorryItem]:
    """
    检测文件文本中所有非注释的 sorry 出现位置，按源码顺序返回。

    每个 sorry 单独对应一个 SorryItem，并记录其所在的声明块范围。
    用于"顺序前缀编译"模式：solver 每次只处理第一个 sorry，
    编译的临时文件只包含到当前块结尾的前缀。
    """
    comment_mask = _build_comment_mask(text)
    block_ranges = _find_block_ranges(text)  # [(start, end, name), ...]

    def _find_enclosing_block(offset: int) -> tuple[int, int, str]:
        """找到包含 offset 的最近声明块；未找到则以整个文件为块。"""
        for bs, be, bn in reversed(block_ranges):
            if bs <= offset < be:
                return bs, be, bn
        return 0, len(text), ""

    items: list[SorryItem] = []
    for m in re.finditer(r'\bsorry\b', text):
        if comment_mask[m.start()]:
            continue
        offset = m.start()
        line_no = text[:offset].count('\n') + 1
        last_nl = text[:offset].rfind('\n')
        col_no = offset - last_nl  # 1-based
        bs, be, bn = _find_enclosing_block(offset)
        items.append(SorryItem(
            index=len(items),
            char_offset=offset,
            line_no=line_no,
            col_no=col_no,
            block_name=bn,
            block_char_start=bs,
            block_char_end=be,
        ))
    return items
