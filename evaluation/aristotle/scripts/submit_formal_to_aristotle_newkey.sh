#!/usr/bin/env bash
set -euo pipefail

PROJECT_DIR="/root/workspace/benchmark/evaluation/aristotle"
PYTHON_BIN="${PROJECT_DIR}/.venv/bin/python"
REQUEST_SCRIPT="${PROJECT_DIR}/scripts/aristotle_request.py"

# API key provided for this benchmark run.
export ARISTOTLE_API_KEY="arstl_2cbFqXoaNCKLxYzR7DyZogbboJAriSY4haQAhL_d1HY"

if [[ ! -x "${PYTHON_BIN}" ]]; then
  echo "Missing Python virtualenv at ${PYTHON_BIN}" >&2
  echo "Create it and install aristotlelib first:" >&2
  echo "  python3 -m venv ${PROJECT_DIR}/.venv" >&2
  echo "  ${PROJECT_DIR}/.venv/bin/pip install aristotlelib" >&2
  exit 1
fi

if [[ ! -f "${REQUEST_SCRIPT}" ]]; then
  echo "Missing request script: ${REQUEST_SCRIPT}" >&2
  exit 1
fi

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  cat <<EOF
Usage:
  $0 [LEAN_FILE] [aristotle_request.py submit options]

Examples:
  $0
  $0 /root/workspace/benchmark/JSON2LEAN/lean/problems/problem-1.lean --wait --destination /tmp/problem-1.tar.gz

LEAN_FILE defaults to ${PROJECT_DIR}/formal.lean.
The script infers the Lean project root by walking upward from LEAN_FILE until it finds lakefile.lean.
EOF
  exit 0
fi

LEAN_FILE="${1:-${PROJECT_DIR}/formal.lean}"
if [[ $# -gt 0 ]]; then
  shift
fi

if [[ ! -f "${LEAN_FILE}" ]]; then
  echo "Lean file does not exist: ${LEAN_FILE}" >&2
  exit 1
fi

LEAN_FILE="$(realpath "${LEAN_FILE}")"
LEAN_DIR="$(dirname "${LEAN_FILE}")"
TARGET_PROJECT_DIR="${LEAN_DIR}"

while [[ "${TARGET_PROJECT_DIR}" != "/" && ! -f "${TARGET_PROJECT_DIR}/lakefile.lean" ]]; do
  TARGET_PROJECT_DIR="$(dirname "${TARGET_PROJECT_DIR}")"
done

if [[ ! -f "${TARGET_PROJECT_DIR}/lakefile.lean" ]]; then
  echo "Could not find lakefile.lean above ${LEAN_FILE}" >&2
  exit 1
fi

REL_LEAN_FILE="$(realpath --relative-to="${TARGET_PROJECT_DIR}" "${LEAN_FILE}")"
PROMPT="${ARISTOTLE_PROMPT:-Prove all theorems with sorry in ${REL_LEAN_FILE}. Keep all theorem statements and existing definitions unchanged. Use Lean 4.28/mathlib 4.28. Return a compiling Lean project.}"

cd "${TARGET_PROJECT_DIR}"

"${PYTHON_BIN}" "${REQUEST_SCRIPT}" submit \
  --project-dir "${TARGET_PROJECT_DIR}" \
  --prompt "${PROMPT}" \
  "$@"
