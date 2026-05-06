"""Console-script entrypoint for the top-level JSON2LEAN pipeline."""

from __future__ import annotations

import sys
from pathlib import Path


def main() -> None:
    """Run the repository-level ``main.py`` entrypoint.

    The project keeps the full pipeline in the repository root while the
    installable package lives under ``src/``.  Console scripts import package
    modules directly, so add the repository root before importing ``main``.
    """

    root = Path(__file__).resolve().parents[2]
    if str(root) not in sys.path:
        sys.path.insert(0, str(root))

    from main import main as pipeline_main

    pipeline_main()
