#!/usr/bin/env python3
"""
Split Lean files by sections.

This script reads Lean files from the source directory, splits them by sections,
and writes each section to a separate file in the output directory.

Usage:
    python lean_splitter.py [--input-dir INPUT_PATH] [--output-dir OUTPUT_DIR]
    
Default:
    Input: JSON2LEAN/lean/LeanProject
    Output: 4.27.0/4-27mathlib/4.27mathlib
"""

"python3 JSON2LEAN/src/utils/lean_splitter.py --include-file"
import json
import os
import re
import sys
from pathlib import Path
from typing import Iterable, List, Tuple


def parse_sections(content: str) -> List[Tuple[str, str]]:
    """
    Parse sections from Lean file content.
    
    Returns a list of (section_name, section_content) tuples.
    """
    sections = []
    
    # Remove the header (import Mathlib and noncomputable section)
    lines = content.split('\n')
    start_idx = 0
    
    # Skip import and noncomputable section
    for i, line in enumerate(lines):
        if line.strip() == 'noncomputable section':
            start_idx = i + 1
            break
    
    content_body = '\n'.join(lines[start_idx:]).strip()
    
    # Find all namespaces
    # Pattern: "namespace SectionName" ... "end SectionName"
    section_pattern = r'^namespace\s+(\w+)\s*$'
    end_pattern = r'^end\s+\w+\s*$'
    
    current_section = None
    current_content = []
    section_lines = content_body.split('\n')
    
    for line in section_lines:
        section_match = re.match(section_pattern, line)
        end_match = re.match(end_pattern, line)
        
        if section_match:
            # Start of a new section
            if current_section is not None:
                # Save previous section
                sections.append((current_section, '\n'.join(current_content).strip()))
            
            current_section = section_match.group(1)
            current_content = []
        elif end_match:
            # End of current section
            if current_section is not None:
                sections.append((current_section, '\n'.join(current_content).strip()))
                current_section = None
                current_content = []
        else:
            # Content line
            if current_section is not None:
                current_content.append(line)
    
    # Handle any remaining section
    if current_section is not None:
        sections.append((current_section, '\n'.join(current_content).strip()))
    
    return sections


def create_section_file(section_name: str, section_content: str, output_path: str) -> None:
    """
    Create a Lean file for a single section.
    """
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
    
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write(file_content)


def split_lean_file(input_file: str, output_dir: str) -> None:
    """
    Split a single Lean file into sections.
    """
    # Read the input file
    with open(input_file, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Parse sections
    sections = parse_sections(content)
    
    if not sections:
        print(f"Warning: No sections found in {input_file}")
        return
    
    # Create output directory for this file
    base_name = Path(input_file).stem  # Get filename without extension
    file_output_dir = os.path.join(output_dir, base_name)
    
    os.makedirs(file_output_dir, exist_ok=True)
    
    # Create a file for each section
    for section_name, section_content in sections:
        # Convert section name to snake_case for filename
        file_name = section_name + '.lean'
        output_path = os.path.join(file_output_dir, file_name)
        
        create_section_file(section_name, section_content, output_path)
        print(f"  Created: {os.path.join(base_name, file_name)}")


def split_lean_project(input_dir: str, output_dir: str) -> None:
    """
    Split all Lean files in a project directory.
    """
    # Ensure output directory exists
    os.makedirs(output_dir, exist_ok=True)
    
    # Find all .lean files in input directory
    lean_files = []
    for root, dirs, files in os.walk(input_dir):
        for file in files:
            if file.endswith('.lean'):
                lean_files.append(os.path.join(root, file))
    
    if not lean_files:
        print(f"No .lean files found in {input_dir}")
        return
    
    print(f"Found {len(lean_files)} .lean files")
    print(f"Splitting to: {output_dir}\n")
    
    for lean_file in sorted(lean_files):
        rel_path = os.path.relpath(lean_file, input_dir)
        print(f"Processing: {rel_path}")
        split_lean_file(lean_file, output_dir)
    
    print(f"\nDone! Output written to: {output_dir}")


def _load_include_file_list(file_path: str) -> List[str]:
    """
    Load include file list from a config file.

    Supported formats:
    - JSON list: ["a.lean", "b.lean"]
    - JSON object: {"files": ["a.lean", "b.lean"]}
    - Plain text: one file path per line, '#' comments allowed
    """
    path = Path(file_path)
    if not path.exists():
        raise FileNotFoundError(f"Include file list not found: {file_path}")

    text = path.read_text(encoding="utf-8")
    stripped = text.strip()
    if not stripped:
        return []

    # Try JSON first.
    try:
        parsed = json.loads(stripped)
        if isinstance(parsed, list):
            return [str(x).strip() for x in parsed if str(x).strip()]
        if isinstance(parsed, dict):
            files = parsed.get("files", [])
            if isinstance(files, list):
                return [str(x).strip() for x in files if str(x).strip()]
    except json.JSONDecodeError:
        pass

    # Fallback to plain text lines.
    lines: List[str] = []
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        lines.append(line)
    return lines


def _resolve_requested_files(
    input_dir: str,
    requested_files: Iterable[str] | None = None,
) -> List[str]:
    """
    Resolve requested Lean files against input directory.

    Requested entries can be:
    - absolute file paths
    - paths relative to input_dir
    - basenames like "foo.lean"
    """
    # Find all .lean files in input directory
    all_lean_files: List[str] = []
    for root, _, files in os.walk(input_dir):
        for file in files:
            if file.endswith('.lean'):
                all_lean_files.append(os.path.join(root, file))

    if not requested_files:
        return sorted(all_lean_files)

    all_abs = [str(Path(p).resolve()) for p in all_lean_files]
    all_abs_set = set(all_abs)
    basename_to_abs = {}
    for p in all_abs:
        basename_to_abs.setdefault(Path(p).name, []).append(p)

    resolved: List[str] = []
    missing: List[str] = []
    base_dir = Path(input_dir).resolve()

    for entry in requested_files:
        e = str(entry).strip()
        if not e:
            continue
        p = Path(e)
        candidates: List[Path] = []
        if p.is_absolute():
            candidates.append(p.resolve())
        else:
            candidates.append((base_dir / p).resolve())
            # also try basename match
            if p.name in basename_to_abs:
                for m in basename_to_abs[p.name]:
                    candidates.append(Path(m))

        matched = None
        for c in candidates:
            if str(c) in all_abs_set:
                matched = str(c)
                break
        if matched is None:
            missing.append(e)
            continue
        resolved.append(matched)

    if missing:
        raise FileNotFoundError(
            "Requested .lean files not found under input-dir: " + ", ".join(missing)
        )

    # Keep stable order and deduplicate.
    seen = set()
    out: List[str] = []
    for p in resolved:
        if p in seen:
            continue
        seen.add(p)
        out.append(p)
    return out


def split_selected_lean_files(input_dir: str, output_dir: str, selected_files: Iterable[str]) -> None:
    """
    Split selected Lean files in a project directory.
    """
    os.makedirs(output_dir, exist_ok=True)

    files = list(selected_files)
    if not files:
        print("No matching .lean files selected.")
        return

    print(f"Selected {len(files)} .lean files")
    print(f"Splitting to: {output_dir}\n")

    for lean_file in sorted(files):
        rel_path = os.path.relpath(lean_file, input_dir)
        print(f"Processing: {rel_path}")
        split_lean_file(lean_file, output_dir)

    print(f"\nDone! Output written to: {output_dir}")


def main():
    """Main entry point."""
    import argparse
    
    # Get the directory of this script to compute default paths
    script_dir = Path(__file__).resolve().parent
    # src/utils -> src -> JSON2LEAN -> workspace root
    workspace_root = script_dir.parent.parent.parent
    
    default_input = str(workspace_root / "JSON2LEAN" / "lean" / "LeanProject")
    default_output = str(workspace_root / "evaluation" / "lean"/ "Leanproject" / "Leanproject")
    
    parser = argparse.ArgumentParser(
        description="Split Lean files by sections",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    # Use default directories
    python lean_splitter.py
    
    # Specify custom directories
    python lean_splitter.py --input-dir /path/to/input --output-dir /path/to/output

    # Split only selected files (repeat --include-file)
    python lean_splitter.py --include-file foo.lean --include-file subdir/bar.lean

    # Split files from a config list (json list/object or txt lines)
    python lean_splitter.py --include-file-list split_files.json
        """
    )
    
    parser.add_argument(
        '--input-dir',
        default=default_input,
        help=f"Input path (directory or single .lean file), default: {default_input}"
    )
    parser.add_argument(
        '--output-dir',
        default=default_output,
        help=f"Output directory for split files (default: {default_output})"
    )
    parser.add_argument(
        '--include-file',
        action='append',
        default=[],
        help=(
            "Only split specified .lean file(s). Can be repeated. "
            "Supports absolute path, path relative to --input-dir, or basename."
        ),
    )
    parser.add_argument(
        '--include-file-list',
        default="",
        help=(
            "Path to include-file list config. Supports JSON list/object "
            "or plain text (one file per line)."
        ),
    )
    
    args = parser.parse_args()
    
    # Check if input path exists
    if not os.path.exists(args.input_dir):
        print(f"Error: Input path not found: {args.input_dir}", file=sys.stderr)
        sys.exit(1)
    
    try:
        if os.path.isfile(args.input_dir):
            if not args.input_dir.endswith(".lean"):
                print(f"Error: Input file is not a .lean file: {args.input_dir}", file=sys.stderr)
                sys.exit(1)
            os.makedirs(args.output_dir, exist_ok=True)
            print(f"Processing single file: {Path(args.input_dir).name}")
            split_lean_file(args.input_dir, args.output_dir)
            print(f"\nDone! Output written to: {args.output_dir}")
        else:
            requested_files = list(args.include_file or [])
            if args.include_file_list:
                requested_files.extend(_load_include_file_list(args.include_file_list))
            selected = _resolve_requested_files(args.input_dir, requested_files)
            split_selected_lean_files(args.input_dir, args.output_dir, selected)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
