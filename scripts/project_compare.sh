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

if [[ ! -f "${REF_NES}" ]]; then
  echo "error: reference iNES file not found: ${REF_NES}" >&2
  exit 1
fi

TMPDIR_COMPARE="$(mktemp -d)"
trap 'rm -rf "${TMPDIR_COMPARE}"' EXIT

INES_MAGIC="$(od -An -tx1 -N4 "${REF_NES}" | tr -d ' \n')"
if [[ "${INES_MAGIC}" != "4e45531a" ]]; then
  echo "error: ${REF_NES} is not a valid iNES file (bad magic)" >&2
  exit 2
fi

PRG_UNITS="$(od -An -tu1 -j4 -N1 "${REF_NES}" | tr -d ' ')"
FLAGS6="$(od -An -tu1 -j6 -N1 "${REF_NES}" | tr -d ' ')"

if [[ -z "${PRG_UNITS}" || -z "${FLAGS6}" ]]; then
  echo "error: failed to parse iNES header fields from ${REF_NES}" >&2
  exit 2
fi

TRAINER_SIZE=0
if (( (FLAGS6 & 0x04) != 0 )); then
  TRAINER_SIZE=512
fi

PRG_OFFSET=$((16 + TRAINER_SIZE))
PRG_SIZE=$((PRG_UNITS * 16384))
REF_PRG="${TMPDIR_COMPARE}/reference_prg.bin"
dd if="${REF_NES}" of="${REF_PRG}" bs=1 skip="${PRG_OFFSET}" count="${PRG_SIZE}" status=none

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
