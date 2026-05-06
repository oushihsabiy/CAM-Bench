#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

require_cmd() {
  local cmd="$1"
  if ! command -v "$cmd" >/dev/null 2>&1; then
    echo "[wrapper] FAIL required command not found: $cmd" >&2
    exit 127
  fi
}

require_cmd bash

if [[ ! -f "$ROOT_DIR/scripts/ensure_all_outputs.sh" ]]; then
  echo "[wrapper] FAIL missing script: $ROOT_DIR/scripts/ensure_all_outputs.sh" >&2
  exit 1
fi

if [[ $# -lt 1 ]]; then
  echo "Usage: bash scripts/run_with_autoscan.sh '<original command>'"
  echo "Example: bash scripts/run_with_autoscan.sh 'bash scripts/run_pipeline.sh data/convex_optimization_Chp2.json --resume'"
  exit 1
fi

CMD="$*"
echo "[wrapper] run: $CMD"
cmd_rc=0
bash -lc "$CMD" || cmd_rc=$?

if [[ "$cmd_rc" -ne 0 && "${AUTOSCAN_AFTER_FAIL:-0}" != "1" ]]; then
  echo "[wrapper] command failed (rc=$cmd_rc), skip autoscan (set AUTOSCAN_AFTER_FAIL=1 to force)"
  exit "$cmd_rc"
fi

echo "[wrapper] command finished (rc=$cmd_rc), start autoscan..."
auto_rc=0
bash scripts/ensure_all_outputs.sh || auto_rc=$?

if [[ "$auto_rc" -ne 0 ]]; then
  echo "[wrapper] autoscan failed (rc=$auto_rc)"
  exit "$auto_rc"
fi

exit "$cmd_rc"
