#!/usr/bin/env python3
"""
Split one Lean file into per-namespace files.

This script is intentionally single-file only, so it never scans all Lean files
under a directory by accident.
"""

from __future__ import annotations

import argparse
import re
import shlex
import sys
from pathlib import Path
from typing import List, Tuple


def parse_sections(content: str) -> List[Tuple[str, str]]:
    """Parse sections as (namespace_name, content)."""
    sections: List[Tuple[str, str]] = []

    lines = content.split("\n")
    start_idx = 0
    for i, line in enumerate(lines):
        if line.strip() == "noncomputable section":
            start_idx = i + 1
            break

    body = "\n".join(lines[start_idx:]).strip()
    section_pattern = r"^namespace\s+(\w+)\s*$"
    end_pattern = r"^end\s+\w+\s*$"

    current_section = None
    current_content: List[str] = []
    for line in body.split("\n"):
        m_start = re.match(section_pattern, line)
        m_end = re.match(end_pattern, line)
        if m_start:
            if current_section is not None:
                sections.append((current_section, "\n".join(current_content).strip()))
            current_section = m_start.group(1)
            current_content = []
        elif m_end:
            if current_section is not None:
                sections.append((current_section, "\n".join(current_content).strip()))
                current_section = None
                current_content = []
        else:
            if current_section is not None:
                current_content.append(line)

    if current_section is not None:
        sections.append((current_section, "\n".join(current_content).strip()))
    return sections


def create_section_file(section_name: str, section_content: str, output_path: Path) -> None:
    file_content = f"""import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

-- {section_name}

{section_content}
"""
    output_path.write_text(file_content, encoding="utf-8")


def split_one_file(input_lean: Path, output_dir: Path) -> int:
    content = input_lean.read_text(encoding="utf-8")
    sections = parse_sections(content)
    if not sections:
        print(f"[split_single_lean] Warning: No sections found in {input_lean}")
        return 0

    stem = input_lean.stem
    target_dir = output_dir / stem
    target_dir.mkdir(parents=True, exist_ok=True)

    created = 0
    for section_name, section_content in sections:
        out_file = target_dir / f"{section_name}.lean"
        create_section_file(section_name, section_content, out_file)
        print(f"[split_single_lean] Created: {out_file}")
        created += 1
    return created


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Split one Lean file by namespace into multiple Lean files."
    )
    parser.add_argument("--input-lean", required=True, help="Input .lean file path")
    parser.add_argument("--output-dir", required=True, help="Output directory")
    args = parser.parse_args()

    input_lean = Path(args.input_lean).expanduser().resolve()
    output_dir = Path(args.output_dir).expanduser().resolve()

    if not input_lean.exists():
        print(f"[split_single_lean] Error: input file not found: {input_lean}", file=sys.stderr)
        sys.exit(1)
    if not input_lean.is_file():
        print(f"[split_single_lean] Error: input path is not a file: {input_lean}", file=sys.stderr)
        sys.exit(1)
    if input_lean.suffix != ".lean":
        print(f"[split_single_lean] Error: input file must end with .lean: {input_lean}", file=sys.stderr)
        sys.exit(1)

    output_dir.mkdir(parents=True, exist_ok=True)

    cmd_preview = (
        "python3 scripts/split_single_lean.py "
        f"--input-lean {shlex.quote(str(input_lean))} "
        f"--output-dir {shlex.quote(str(output_dir))}"
    )
    print(f"[split_single_lean] Command: {cmd_preview}")
    print(f"[split_single_lean] Input : {input_lean}")
    print(f"[split_single_lean] Output: {output_dir}")

    count = split_one_file(input_lean, output_dir)
    print(f"[split_single_lean] Done. sections={count}")


if __name__ == "__main__":
    main()
