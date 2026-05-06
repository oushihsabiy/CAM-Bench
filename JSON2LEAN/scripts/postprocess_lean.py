#!/usr/bin/env python3
"""CLI wrapper for Lean post-processing."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys


PROJECT_ROOT = Path(__file__).resolve().parents[1]
SRC_DIR = PROJECT_ROOT / "src"
if str(SRC_DIR) not in sys.path:
    sys.path.insert(0, str(SRC_DIR))

from json2lean.postprocess_lean import postprocess_lean_file


def main() -> None:
    p = argparse.ArgumentParser(description="Post-process a generated Lean file.")
    p.add_argument("lean_file", help="Path to Lean file")
    args = p.parse_args()

    path = Path(args.lean_file).expanduser().resolve()
    changed = postprocess_lean_file(path)
    print(f"[postprocess] {'changed' if changed else 'unchanged'}: {path}")


if __name__ == "__main__":
    main()
