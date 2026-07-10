#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 || $# -gt 2 ]]; then
  echo "usage: $0 <project_slug> [text|json]" >&2
  exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=scripts/project_common.sh
source "${SCRIPT_DIR}/project_common.sh"

load_project_conf "$1"
COMPARE_FORMAT="${2:-text}"

TMPDIR_COMPARE="$(mktemp -d)"
trap 'rm -rf "${TMPDIR_COMPARE}"' EXIT

REF_PRG="${TMPDIR_COMPARE}/reference_prg.bin"
extract_reference_prg_from_ines "${REF_NES}" "${REF_PRG}"

cmd=(
  xasm
  --pure-binary
  -o "${TMPDIR_COMPARE}/scratch.o"
  "--compare=${REF_PRG}"
  "--compare-format=${COMPARE_FORMAT}"
)

if [[ -n "${XASM_COMPARE_CPU_BASE:-}" ]]; then
  cmd+=("--compare-cpu-base=${XASM_COMPARE_CPU_BASE}")
fi

cmd+=("${ASM_FILE}")
"${cmd[@]}"
