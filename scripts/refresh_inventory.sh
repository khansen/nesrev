#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <project_slug>" >&2
  exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=scripts/project_common.sh
source "${SCRIPT_DIR}/project_common.sh"

load_project_conf "$1"

inv_dir="${NESREV_INVENTORY_OUT_DIR:-${DOC_ROOT}/inventory}"
mkdir -p "${inv_dir}"

project_slug="$1"

const_tmp="$(mktemp)"
trap 'rm -f "$const_tmp"' EXIT

awk '
/^[A-Za-z_][A-Za-z0-9_]*[ \t]+\.EQU[ \t]+/ {
  name=$1
  val=$3
  gsub(/[,;]/, "", val)
  print name "\t" val
}
' "${ASM_FILE}" | sort -u > "$const_tmp"

{
  echo "constant_name,value,domain,usage_sites"
  while IFS=$'\t' read -r name val; do
    [[ -z "$name" ]] && continue
    domain="misc"
    case "$name" in
      ZP_*) domain="zp" ;;
      RAM_*) domain="ram" ;;
      PPU*|PPU_*) domain="ppu" ;;
      APU*|IO_RAW_40*) domain="apu" ;;
      OAM*|RAM_OAM*) domain="oam" ;;
      JOYPAD*|PAD_*|BTN_*) domain="input" ;;
      AUDIO_*|SFX_*|MUSIC_*) domain="audio" ;;
    esac
    matches="$(rg -n "\\b${name}\\b" "${ASM_FILE}" || true)"
    if [[ -n "${matches}" ]]; then
      uses="$(printf '%s\n' "${matches}" | wc -l | tr -d ' ')"
    else
      uses=0
    fi
    if [[ "$uses" -gt 0 ]]; then
      uses=$((uses - 1))
    fi
    printf "%s,%s,%s,%s\n" "$name" "$val" "$domain" "$uses"
  done < "$const_tmp"
} > "${inv_dir}/constants_catalog.csv"

bash "${SCRIPT_DIR}/pointer_targets.sh" \
  "${ASM_FILE}" \
  "${inv_dir}/pointer_targets.csv"

python3 "${SCRIPT_DIR}/embedded_pointer_targets.py" \
  "${ASM_FILE}" \
  "${inv_dir}/embedded_pointer_targets.csv"

raw_report="$(bash "${SCRIPT_DIR}/raw_address_kpi.sh" "${ASM_FILE}" 2>/dev/null || true)"
raw_lowaddr="$(printf '%s\n' "$raw_report" | awk -F= '/strict_active_raw_lowaddr=/{print $2}')"
raw_absrom="$(printf '%s\n' "$raw_report" | awk -F= '/strict_active_raw_absrom=/{print $2}')"
raw_lowaddr="${raw_lowaddr:-unknown}"
raw_absrom="${raw_absrom:-unknown}"
proc_doc_report="$(bash "${SCRIPT_DIR}/procedure_doc_kpi.sh" "${ASM_FILE}" 2>/dev/null || true)"
proc_undoc="$(printf '%s\n' "$proc_doc_report" | awk -F= '/strict_callable_procedures_undocumented=/{print $2}')"
proc_total="$(printf '%s\n' "$proc_doc_report" | awk -F= '/strict_callable_procedures_total=/{print $2}')"
proc_undoc="${proc_undoc:-unknown}"
proc_total="${proc_total:-unknown}"
global_code_doc_report="$(bash "${SCRIPT_DIR}/global_code_label_doc_kpi.sh" "${ASM_FILE}" 2>/dev/null || true)"
global_code_undoc="$(printf '%s\n' "$global_code_doc_report" | awk -F= '/strict_global_code_labels_undocumented=/{print $2}')"
global_code_total="$(printf '%s\n' "$global_code_doc_report" | awk -F= '/strict_global_code_labels_total=/{print $2}')"
global_code_undoc="${global_code_undoc:-unknown}"
global_code_total="${global_code_total:-unknown}"
branch_report="$(bash "${SCRIPT_DIR}/branch_literal_kpi.sh" "${ASM_FILE}" 2>/dev/null || true)"
branch_literals="$(printf '%s\n' "$branch_report" | awk -F= '/strict_active_branch_literals=/{print $2}')"
branch_literals="${branch_literals:-unknown}"
inferred_report="$(bash "${SCRIPT_DIR}/inferred_kpi.sh" "${ASM_FILE}" 2>/dev/null || true)"
inferred_annotations="$(printf '%s\n' "$inferred_report" | awk -F= '/strict_inferred_annotations=/{print $2}')"
inferred_annotations="${inferred_annotations:-unknown}"
comment_report="$(bash "${SCRIPT_DIR}/comment_quality_kpi.sh" "${ASM_FILE}" 2>/dev/null || true)"
placeholder_comments="$(printf '%s\n' "$comment_report" | awk -F= '/strict_placeholder_comments=/{print $2}')"
placeholder_comments="${placeholder_comments:-unknown}"
data_doc_report="$(bash "${SCRIPT_DIR}/data_label_doc_kpi.sh" "${ASM_FILE}" 2>/dev/null || true)"
data_labels_noncompliant="$(printf '%s\n' "$data_doc_report" | awk -F= '/strict_data_labels_noncompliant=/{print $2}')"
data_labels_total="$(printf '%s\n' "$data_doc_report" | awk -F= '/strict_data_labels_total=/{print $2}')"
data_labels_noncompliant="${data_labels_noncompliant:-unknown}"
data_labels_total="${data_labels_total:-unknown}"
read -r lxxxx_defs lxxxx_refs < <(
  python3 - "${ASM_FILE}" <<'PY'
import re
import sys
from pathlib import Path

text = Path(sys.argv[1]).read_text(encoding="utf-8")
defs = len(re.findall(r"(?m)^L[0-9A-F]{4,5}:", text))
refs = len(re.findall(r"\bL[0-9A-F]{4,5}\b", text))
print(defs, refs)
PY
)

bash "${SCRIPT_DIR}/branch_literal_sites.sh" \
  "${ASM_FILE}" \
  "${inv_dir}/branch_literal_sites.csv"

cat > "${inv_dir}/unknowns.md" <<DOC
# Unknowns

Auto-generated inventory. Prioritize these unresolved buckets:

- Remaining generic hex labels (LXXXX): ${lxxxx_defs} / ${lxxxx_refs}
- Strict active raw low-address operands: ${raw_lowaddr}
- Strict active raw absolute-ROM operands: ${raw_absrom}
- Strict active parity-sensitive branch literals: ${branch_literals}
- Strict active inferred annotations: ${inferred_annotations}
- Strict placeholder comments: ${placeholder_comments}
- Noncompliant data labels (missing docs/format/usage): ${data_labels_noncompliant} / ${data_labels_total}
- Undocumented callable procedures: ${proc_undoc} / ${proc_total}
- Undocumented global code labels: ${global_code_undoc} / ${global_code_total}
DOC

if [ "${branch_literals}" != "0" ]; then
  cat >> "${inv_dir}/unknowns.md" <<DOC
- Review branch_literal_sites.csv before converting plus/minus relative-branch literal sites to labels.
DOC
fi

unknown_pointer_count="$(awk -F, 'NR > 1 && $4 == "unknown_pointer" { count++ } END { print count + 0 }' "${inv_dir}/pointer_targets.csv")"
if [ "${unknown_pointer_count}" != "0" ]; then
  cat >> "${inv_dir}/unknowns.md" <<DOC
- Review pointer_targets.csv entries with target_type=unknown_pointer and classify each as code/data/mixed.
DOC
fi

embedded_unknown_pointer_count="$(awk -F, 'NR > 1 && $4 == "unknown_pointer" { count++ } END { print count + 0 }' "${inv_dir}/embedded_pointer_targets.csv")"
if [ "${embedded_unknown_pointer_count}" != "0" ]; then
  cat >> "${inv_dir}/unknowns.md" <<DOC
- Review embedded_pointer_targets.csv entries with target_type=unknown_pointer and classify each as code/data/mixed.
DOC
fi

echo "inventory refreshed: ${project_slug} -> ${inv_dir}"
