#!/usr/bin/env bash
set -euo pipefail
# Run eval.run_eval using the repository-local .venv
REPO_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$REPO_DIR"

# Search upward for a .venv directory (repo or workspace root)
VENV_DIR=""
CUR_DIR="$REPO_DIR"
while [ "$CUR_DIR" != "/" ]; do
  if [ -d "$CUR_DIR/.venv" ]; then
    VENV_DIR="$CUR_DIR/.venv"
    break
  fi
  CUR_DIR=$(dirname "$CUR_DIR")
done

if [ -n "$VENV_DIR" ]; then
  # shellcheck disable=SC1091
  . "$VENV_DIR/bin/activate"
  python3 -m eval.run_eval "$@"
else
  echo "No .venv found in repository or parent directories. Create one with:" >&2
  echo "  python3 -m venv .venv" >&2
  echo "  . .venv/bin/activate" >&2
  echo "  pip install -r requirements.txt" >&2
  exit 1
fi
