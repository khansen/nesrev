#!/usr/bin/env bash
set -euo pipefail

mode="$1"
source_file="$2"
if [[ ! -f "${source_file}" ]]; then
  echo "error: asm file not found: ${source_file}" >&2
  exit 65
fi
if [[ ( "${mode}" == kpi && -n "${3:-}" ) || "${mode}" == check ]]; then
  if [[ ! -f "${3}" ]]; then
    echo "error: branch-literal ${mode} input not found: ${3}" >&2
    exit 66
  fi
fi
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
if [[ -z "${NESREV_ANALYSIS_BUNDLE+x}" ]]; then
  analysis_dir="$(mktemp -d)"
  trap 'rm -rf "${analysis_dir}"' EXIT
  prepare_command=(python3 "${SCRIPT_DIR}/analysis_bundle.py" prepare-source "${analysis_dir}" "${source_file}")
  if [[ "${mode}" == kpi && -n "${3:-}" ]]; then
    prepare_command+=("$3")
  fi
  "${prepare_command[@]}"
  python3 "${SCRIPT_DIR}/analysis_bundle.py" produce "${analysis_dir}" "${source_file}" "${analysis_dir}/output.bin" >&2
  export NESREV_ANALYSIS_BUNDLE="${analysis_dir}/bundle.json"
fi
python3 "${SCRIPT_DIR}/branch_literals.py" "$@"
