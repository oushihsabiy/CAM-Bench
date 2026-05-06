#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
source "$ROOT/scripts/load_env.sh"

CODEX_HOME="${CODEX_HOME:-$ROOT/.codex_home}"
export CODEX_HOME

if [[ -z "${HOME:-}" || ! -d "${HOME:-/nonexistent}" || ! -w "${HOME:-/nonexistent}" ]]; then
  export HOME="$CODEX_HOME/home"
fi

export XDG_CONFIG_HOME="${XDG_CONFIG_HOME:-$CODEX_HOME/xdg/config}"
export XDG_DATA_HOME="${XDG_DATA_HOME:-$CODEX_HOME/xdg/data}"
export XDG_CACHE_HOME="${XDG_CACHE_HOME:-$CODEX_HOME/xdg/cache}"

mkdir -p "$CODEX_HOME" "$HOME" "$XDG_CONFIG_HOME" "$XDG_DATA_HOME" "$XDG_CACHE_HOME"

echo "Using repo-isolated CODEX_HOME: $CODEX_HOME"
echo "Running codex-cli login in this isolated home."
echo ""

_json_api_key_from_configs() {
  local source_json="${JSON2LEAN_CODEX_SOURCE_CONFIG:-}"
  local cands=()
  if [[ -n "$source_json" ]]; then
    cands+=("$source_json")
  fi
  cands+=(
    "$ROOT/config.codex.json"
    "$ROOT/config.json"
    "$ROOT/config-me.json"
    "$ROOT/config2.json"
    "$ROOT/config3.json"
    "$ROOT/config4.json"
    "$ROOT/config5.json"
    "$ROOT/config6.json"
  )
  python3 - "${cands[@]}" <<'PY'
import json
import pathlib
import sys

for p in sys.argv[1:]:
    path = pathlib.Path(p)
    if not path.exists():
        continue
    try:
        obj = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        continue
    if not isinstance(obj, dict):
        continue
    key = str(obj.get("api_key", "") or "").strip()
    if key:
        print(key)
        raise SystemExit(0)
raise SystemExit(1)
PY
}

_maybe_auto_pipe_api_key() {
  [[ $# -ge 2 ]] || return 1
  [[ "$1" == "login" ]] || return 1

  local has_with_api_key=0
  local arg
  for arg in "$@"; do
    if [[ "$arg" == "--with-api-key" ]]; then
      has_with_api_key=1
      break
    fi
  done
  [[ "$has_with_api_key" == "1" ]] || return 1

  # If caller already piped stdin, keep default behavior.
  if [[ ! -t 0 ]]; then
    return 1
  fi

  local key="${OPENAI_API_KEY:-}"
  if [[ -z "$key" ]]; then
    key="$(_json_api_key_from_configs 2>/dev/null || true)"
  fi
  if [[ -z "$key" ]]; then
    echo "No API key found in OPENAI_API_KEY or config*.json." >&2
    echo "You can run: printenv OPENAI_API_KEY | bash scripts/codex_login.sh login --with-api-key" >&2
    exit 2
  fi

  printf '%s\n' "$key" | "$ROOT/bin/codex" "$@"
  exit $?
}

_maybe_auto_pipe_api_key "$@"

if [[ $# -gt 0 ]]; then
  exec "$ROOT/bin/codex" "$@"
fi

echo "Pass your codex-cli login command, for example:"
echo "  bash scripts/codex_login.sh login"
echo "  bash scripts/codex_login.sh login --with-api-key"
echo ""
echo "Or run any codex command through the wrapper:"
echo "  bin/codex mcp list"
exit 2
