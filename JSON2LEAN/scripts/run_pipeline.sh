#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

require_cmd() {
  local cmd="$1"
  if ! command -v "$cmd" >/dev/null 2>&1; then
    echo "[run_pipeline] FAIL required command not found: $cmd" >&2
    exit 127
  fi
}

require_cmd python3

if [[ ! -f "$ROOT_DIR/main.py" ]]; then
  echo "[run_pipeline] FAIL missing file: $ROOT_DIR/main.py" >&2
  exit 1
fi

if [[ -f "$ROOT_DIR/scripts/load_env.sh" ]]; then
  # shellcheck disable=SC1090
  source "$ROOT_DIR/scripts/load_env.sh"
fi

unset http_proxy https_proxy HTTP_PROXY HTTPS_PROXY all_proxy ALL_PROXY

if [[ $# -lt 1 ]]; then
  echo "Usage: bash scripts/run_pipeline.sh <input_json> [json2lean args...]"
  exit 1
fi

INPUT_JSON="$1"
shift

if [[ ! -f "$INPUT_JSON" ]]; then
  echo "[run_pipeline] FAIL input json not found: $INPUT_JSON" >&2
  exit 1
fi

ARGS=("$@")

if [[ -n "${MCP_HTTP_PROXY:-}" ]]; then
  export MCP_HTTP_PROXY
fi
if [[ -n "${MCP_HTTPS_PROXY:-}" ]]; then
  export MCP_HTTPS_PROXY
fi
if [[ -n "${MCP_ALL_PROXY:-}" ]]; then
  export MCP_ALL_PROXY
fi
if [[ -n "${MCP_NO_PROXY:-}" ]]; then
  export MCP_NO_PROXY
fi
if [[ -n "${MCP_USE_ALL_PROXY:-}" ]]; then
  export MCP_USE_ALL_PROXY
fi

exec python3 main.py "$INPUT_JSON" "${ARGS[@]}"
