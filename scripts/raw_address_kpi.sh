#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 || $# -gt 2 ]]; then
  echo "usage: $0 <asm_file> [kpi_conf]" >&2
  exit 64
fi
if [[ ! -f "$1" ]]; then
  echo "error: asm file not found: $1" >&2
  exit 65
fi
if [[ -n "${2:-}" && ! -f "$2" ]]; then
  echo "error: raw KPI config not found: $2" >&2
  exit 66
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
if [[ -z "${NESREV_ANALYSIS_BUNDLE+x}" ]]; then
  analysis_dir="$(mktemp -d)"
  trap 'rm -rf "${analysis_dir}"' EXIT
  prepare_command=(python3 "${SCRIPT_DIR}/analysis_bundle.py" prepare-source "${analysis_dir}" "$1")
  if [[ -n "${2:-}" ]]; then
    prepare_command+=("$2")
  fi
  "${prepare_command[@]}"
  python3 "${SCRIPT_DIR}/analysis_bundle.py" produce "${analysis_dir}" "$1" "${analysis_dir}/output.bin" >&2
  export NESREV_ANALYSIS_BUNDLE="${analysis_dir}/bundle.json"
fi
python3 "${SCRIPT_DIR}/raw_addresses.py" "$@"
