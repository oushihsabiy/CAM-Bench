#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

DATA_DIR="$ROOT_DIR/data"
PRE_DIR="$ROOT_DIR/preprocessed_data"
LEAN_DIR="$ROOT_DIR/lean/LeanProject"
MAX_RETRIES="${MAX_RETRIES:-3}"
CMD_TIMEOUT_SEC="${CMD_TIMEOUT_SEC:-1800}"

require_cmd() {
  local cmd="$1"
  if ! command -v "$cmd" >/dev/null 2>&1; then
    echo "[autoscan] FAIL required command not found: $cmd" >&2
    exit 127
  fi
}

require_cmd bash
require_cmd python3
require_cmd find
require_cmd sort

if [[ ! -f "$ROOT_DIR/scripts/run_pipeline.sh" ]]; then
  echo "[autoscan] FAIL missing script: $ROOT_DIR/scripts/run_pipeline.sh" >&2
  exit 1
fi

if command -v timeout >/dev/null 2>&1; then
  HAS_TIMEOUT=1
else
  HAS_TIMEOUT=0
  echo "[autoscan] WARN command 'timeout' not found, run without timeout protection"
fi

on_interrupt() {
  echo "[autoscan] INTERRUPTED, stopping child processes..." >&2
  pkill -P $$ 2>/dev/null || true
  exit 130
}
trap on_interrupt INT TERM

run_cmd_with_timeout() {
  if [[ "$HAS_TIMEOUT" -eq 1 ]]; then
    timeout --foreground "${CMD_TIMEOUT_SEC}s" "$@"
  else
    "$@"
  fi
}

if [[ ! -d "$DATA_DIR" ]]; then
  echo "[autoscan] FAIL data dir missing: $DATA_DIR"
  exit 1
fi

mkdir -p "$PRE_DIR"
mkdir -p "$LEAN_DIR"

# shellcheck disable=SC2034
declare -A RETRIES=()

autoscan_check_preprocessed() {
  local p="$1"
  if [[ ! -f "$p" ]]; then
    return 1
  fi
  if [[ ! -s "$p" ]]; then
    return 1
  fi
  if ! python3 - <<'PY' "$p"
import json,sys
p=sys.argv[1]
try:
    with open(p,'r',encoding='utf-8') as f:
        obj=json.load(f)
except Exception:
    raise SystemExit(1)
# Treat empty as missing.
if obj in (None, "", [], {}):
    raise SystemExit(1)
# Expected preprocessed payload is a non-empty list.
if not isinstance(obj, list) or len(obj)==0:
    raise SystemExit(1)
PY
  then
    return 1
  fi
  return 0
}

autoscan_check_lean_file() {
  local p="$1"
  [[ -f "$p" && -s "$p" ]]
}

autoscan_safe_stem() {
  local raw="$1"
  python3 - <<'PY' "$raw"
import re, sys
s = str(sys.argv[1] if len(sys.argv) > 1 else "")
print(re.sub(r"[^\w\-.]", "_", s) or "input")
PY
}

run_pipeline_from_preprocessed() {
  local pre_file="$1"
  local stem raw_stem
  local lean_file
  raw_stem="$(basename "$pre_file" .json)"
  stem="$(autoscan_safe_stem "$raw_stem")"
  lean_file="$LEAN_DIR/$stem.lean"

  echo "[autoscan] RUN  bash scripts/run_pipeline.sh $pre_file --no-preprocess --resume"
  run_cmd_with_timeout bash scripts/run_pipeline.sh "$pre_file" --no-preprocess --resume

  # Resume can be a no-op when checkpoint says all items are done, while the
  # final .lean file is actually missing. In that case, force a full rebuild.
  if ! autoscan_check_lean_file "$lean_file"; then
    echo "[autoscan] WARN $stem resume produced no .lean, fallback to full run"
    echo "[autoscan] RUN  bash scripts/run_pipeline.sh $pre_file --no-preprocess"
    run_cmd_with_timeout bash scripts/run_pipeline.sh "$pre_file" --no-preprocess
  fi
}

run_pipeline_from_data() {
  local data_file="$1"
  local stem raw_stem
  local pre_file
  raw_stem="$(basename "$data_file" .json)"
  stem="$(autoscan_safe_stem "$raw_stem")"
  pre_file="$PRE_DIR/$stem.json"
  echo "[autoscan] RUN  bash scripts/run_pipeline.sh $data_file --resume"
  run_cmd_with_timeout bash scripts/run_pipeline.sh "$data_file" --resume

  # Same stale-checkpoint guard as lean rebuild:
  # if resume no-ops and preprocessing output is still missing, force full run.
  if ! autoscan_check_preprocessed "$pre_file"; then
    echo "[autoscan] WARN $stem resume produced no preprocessed output, fallback to full run"
    echo "[autoscan] RUN  bash scripts/run_pipeline.sh $data_file"
    run_cmd_with_timeout bash scripts/run_pipeline.sh "$data_file"
  fi
}

while true; do
  unresolved_this_round=0
  progress_this_round=0

  while IFS= read -r -d '' data_file; do
    base="$(basename "$data_file")"
    stem="${base%.json}"
    safe_stem="$(autoscan_safe_stem "$stem")"
    pre_file="$PRE_DIR/$safe_stem.json"
    lean_file="$LEAN_DIR/$safe_stem.lean"

    missing_pre=0
    missing_lean=0

    if ! autoscan_check_preprocessed "$pre_file"; then
      missing_pre=1
    fi
    if ! autoscan_check_lean_file "$lean_file"; then
      missing_lean=1
    fi

    if [[ "$missing_pre" -eq 0 && "$missing_lean" -eq 0 ]]; then
      echo "[autoscan] OK   $stem"
      continue
    fi

    unresolved_this_round=1
    current_retry="${RETRIES[$safe_stem]:-0}"
    if (( current_retry >= MAX_RETRIES )); then
      echo "[autoscan] FAIL $stem (exceeded retries=$MAX_RETRIES)"
      continue
    fi

    RETRIES[$safe_stem]=$((current_retry + 1))
    echo "[autoscan] FIX  $stem (attempt ${RETRIES[$safe_stem]}/$MAX_RETRIES)"

    if [[ "$missing_pre" -eq 1 ]]; then
      if run_pipeline_from_data "$data_file"; then
        progress_this_round=1
      else
        rc=$?
        echo "[autoscan] ERR  $stem preprocess/translate rc=$rc"
      fi
    fi

    if autoscan_check_preprocessed "$pre_file" && ! autoscan_check_lean_file "$lean_file"; then
      if run_pipeline_from_preprocessed "$pre_file"; then
        progress_this_round=1
      else
        rc=$?
        echo "[autoscan] ERR  $stem lean-build rc=$rc"
      fi
    fi

    # Re-check after attempted fix.
    post_missing=0
    if ! autoscan_check_preprocessed "$pre_file"; then
      post_missing=1
    fi
    if ! autoscan_check_lean_file "$lean_file"; then
      post_missing=1
    fi
    if [[ "$post_missing" -eq 0 ]]; then
      echo "[autoscan] OK   $stem"
    fi
  done < <(find "$DATA_DIR" -maxdepth 1 -type f -name '*.json' -print0 | sort -z)

  if [[ "$unresolved_this_round" -eq 0 ]]; then
    echo "[autoscan] DONE all files have preprocessed + lean outputs"
    exit 0
  fi

  # Recompute unresolved files and decide whether any of them is still retryable.
  unresolved_count=0
  retryable_count=0
  while IFS= read -r -d '' data_file; do
    base="$(basename "$data_file")"
    stem="${base%.json}"
    safe_stem="$(autoscan_safe_stem "$stem")"
    pre_file="$PRE_DIR/$safe_stem.json"
    lean_file="$LEAN_DIR/$safe_stem.lean"
    missing_pre=0
    missing_lean=0
    if ! autoscan_check_preprocessed "$pre_file"; then
      missing_pre=1
    fi
    if ! autoscan_check_lean_file "$lean_file"; then
      missing_lean=1
    fi
    if [[ "$missing_pre" -eq 1 || "$missing_lean" -eq 1 ]]; then
      unresolved_count=$((unresolved_count + 1))
      if (( ${RETRIES[$safe_stem]:-0} < MAX_RETRIES )); then
        retryable_count=$((retryable_count + 1))
      fi
    fi
  done < <(find "$DATA_DIR" -maxdepth 1 -type f -name '*.json' -print0 | sort -z)

  if [[ "$retryable_count" -eq 0 ]]; then
    echo "[autoscan] STOP unresolved files remain after max retries"
    exit 2
  fi

  # Safety stop: unresolved remains but this round had no successful fix.
  if [[ "$progress_this_round" -eq 0 ]]; then
    echo "[autoscan] STOP unresolved files remain and no progress in this round"
    exit 2
  fi

  # Continue next round.
  sleep 1

done
