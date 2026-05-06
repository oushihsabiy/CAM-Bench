"""Allow running as ``python -m json2lean``."""

import sys
from pathlib import Path

# Ensure project root (two levels above src/json2lean/) is on sys.path
# so that the top-level main.py is importable.
_root = Path(__file__).resolve().parents[2]
if str(_root) not in sys.path:
    sys.path.insert(0, str(_root))

from main import main  # noqa: E402

main()
