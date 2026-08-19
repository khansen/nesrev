#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <project_slug>" >&2
  exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=scripts/project_common.sh
source "${SCRIPT_DIR}/project_common.sh"

slug="$1"
load_project_conf "${slug}"

pass_dir="${DOC_ROOT}/inventory/pass"
out_file="${pass_dir}/orphan_opcode_candidates.csv"
min_size="${MIN_SIZE:-12}"
threshold="${THRESHOLD:-22}"
max_start_offset="${MAX_START_OFFSET:-64}"
mkdir -p "${pass_dir}"

args=(
  --asm "${ASM_FILE}"
  --warnings "${WARN_BASELINE_FILE}"
  --data-blob-dispositions "${DATA_BLOB_DISPOSITIONS_FILE}"
  --out "${out_file}"
  --min-size "${min_size}"
  --threshold "${threshold}"
  --max-start-offset "${max_start_offset}"
)

if [[ -n "${REF_NES:-}" && -f "${REF_NES}" ]]; then
  args+=(--ref-nes "${REF_NES}")
fi
if [[ -n "${NESREV_CODEENTRIES_FILE:-}" && -f "${NESREV_CODEENTRIES_FILE}" ]]; then
  args+=(--codeentries "${NESREV_CODEENTRIES_FILE}")
fi
if [[ -n "${NESREV_DATARANGES_FILE:-}" && -f "${NESREV_DATARANGES_FILE}" ]]; then
  args+=(--dataranges "${NESREV_DATARANGES_FILE}")
fi
if [[ -n "${NESREV_INLINECALLS_FILE:-}" && -f "${NESREV_INLINECALLS_FILE}" ]]; then
  args+=(--inlinecalls "${NESREV_INLINECALLS_FILE}")
fi

scanner_summary="$(python3 "${SCRIPT_DIR}/orphan_opcode_scan.py" "${args[@]}")"

echo "wrote ${out_file}"
echo "${scanner_summary}"
echo "advisory only: review candidates before adding NESrev recovery controls"
