#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
SUBMIT_SCRIPT="${SCRIPT_DIR}/submit_formal_to_aristotle.sh"

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" || $# -eq 0 ]]; then
  cat <<EOF
Usage:
  $0 LEAN_FILE... [-- aristotle_request.py submit options]

Examples:
  $0 /root/workspace/benchmark/JSON2LEAN/lean/problems/problem-{1..10}.lean

  $0 /root/workspace/benchmark/JSON2LEAN/lean/problems/problem-1.lean \\
     /root/workspace/benchmark/JSON2LEAN/lean/problems/problem-2.lean \\
     -- --wait

Notes:
  Options after -- are passed to aristotle_request.py submit for every file.
  Without --wait, this submits jobs and returns quickly with project IDs.
  With --wait, files are processed sequentially.
EOF
  exit 0
fi

if [[ ! -x "${SUBMIT_SCRIPT}" ]]; then
  echo "Missing or non-executable submit script: ${SUBMIT_SCRIPT}" >&2
  exit 1
fi

declare -a lean_files=()
declare -a submit_args=()
seen_separator=0

for arg in "$@"; do
  if [[ "${seen_separator}" -eq 0 && "${arg}" == "--" ]]; then
    seen_separator=1
    continue
  fi

  if [[ "${seen_separator}" -eq 0 ]]; then
    lean_files+=("${arg}")
  else
    submit_args+=("${arg}")
  fi
done

if [[ "${#lean_files[@]}" -eq 0 ]]; then
  echo "No Lean files provided." >&2
  exit 1
fi

for lean_file in "${lean_files[@]}"; do
  if [[ ! -f "${lean_file}" ]]; then
    echo "Lean file does not exist: ${lean_file}" >&2
    exit 1
  fi
done

for lean_file in "${lean_files[@]}"; do
  echo "==> Submitting ${lean_file}" >&2
  "${SUBMIT_SCRIPT}" "${lean_file}" "${submit_args[@]}"
done
