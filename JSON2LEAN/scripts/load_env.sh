#!/usr/bin/env bash
set -euo pipefail

# Load repo-local env without touching user/global shell config.
# If `CODEX_ENV_FILE` is set, load only that file.
# Otherwise load `.env`, then `.env.local`, then legacy `.env.codex_api`.

_json2lean_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

_trim() {
  local s="$1"
  s="${s#"${s%%[![:space:]]*}"}"
  s="${s%"${s##*[![:space:]]}"}"
  printf '%s' "$s"
}

_load_kv_file() {
  local file="$1"
  [[ -f "$file" ]] || return 0

  local raw line key value
  while IFS= read -r raw || [[ -n "$raw" ]]; do
    raw="${raw%$'\r'}"
    line="$(_trim "$raw")"
    [[ -z "$line" || "$line" == \#* ]] && continue
    [[ "$line" == export\ * ]] && line="${line#export }"
    [[ "$line" == *=* ]] || continue
    key="$(_trim "${line%%=*}")"
    value="$(_trim "${line#*=}")"
    [[ "$key" =~ ^[A-Za-z_][A-Za-z0-9_]*$ ]] || continue
    if [[ "$value" == \"*\" && "$value" == *\" ]]; then
      value="${value:1:-1}"
    elif [[ "$value" == \'*\' && "$value" == *\' ]]; then
      value="${value:1:-1}"
    fi
    export "$key=$value"
  done <"$file"
}

if [[ -n "${CODEX_ENV_FILE:-}" ]]; then
  _load_kv_file "$CODEX_ENV_FILE"
  return 0
fi

_load_kv_file "$_json2lean_root/.env"
_load_kv_file "$_json2lean_root/.env.local"
_load_kv_file "$_json2lean_root/.env.codex_api"
