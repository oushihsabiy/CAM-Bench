"""Development shim package so `python -m json2lean` works from repo root.

This package extends its search path to include `src/json2lean`.
In installed mode, the real package is provided from `src/`.
"""

from __future__ import annotations

from pathlib import Path
from pkgutil import extend_path

__path__ = extend_path(__path__, __name__)  # type: ignore[name-defined]
_src_pkg = Path(__file__).resolve().parents[1] / "src" / "json2lean"
if _src_pkg.exists():
    __path__.append(str(_src_pkg))
