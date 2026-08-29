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
python3 "${SCRIPT_DIR}/project_policy_config_check.py" kpis "${KPI_FILE}"

TMPDIR_PROJECT_VERIFY="$(mktemp -d)"
trap 'rm -rf "${TMPDIR_PROJECT_VERIFY}"' EXIT
verification_xref="${NESREV_XREF_FILE:-${TMPDIR_PROJECT_VERIFY}/xref_with_data.json}"

bash "${SCRIPT_DIR}/verify.sh" \
  "${ASM_FILE}" \
  "${REF_NES}" \
  "${OUT_BIN}" \
  "${WARN_BASELINE_FILE}" \
  "${XASM_COMPARE_CPU_BASE:-}" \
  "${verification_xref}"

if [[ "${PROJECT_VERIFY_REFRESH_INVENTORY:-0}" == "1" ]]; then
  refresh_script="${PROJECT_VERIFY_REFRESH_SCRIPT:-${SCRIPT_DIR}/refresh_inventory.sh}"
  NESREV_XREF_FILE="${verification_xref}" bash "${refresh_script}" "$1"
fi

bash "${SCRIPT_DIR}/raw_address_kpi.sh" \
  "${ASM_FILE}" \
  "${RAW_KPI_FILE}"

bash "${SCRIPT_DIR}/constant_kpi.sh" \
  "${ASM_FILE}" \
  "${CONST_KPI_FILE}"

bash "${SCRIPT_DIR}/procedure_doc_kpi.sh" \
  "${ASM_FILE}" \
  "${PROC_DOC_KPI_FILE}"

bash "${SCRIPT_DIR}/global_code_label_doc_kpi.sh" \
  "${ASM_FILE}" \
  "${GLOBAL_CODE_LABEL_DOC_KPI_FILE}"

bash "${SCRIPT_DIR}/branch_literal_kpi.sh" \
  "${ASM_FILE}" \
  "${BRANCH_KPI_FILE}"

bash "${SCRIPT_DIR}/branch_literal_sites_check.sh" \
  "${ASM_FILE}" \
  "${BRANCH_SITES_FILE}"

bash "${SCRIPT_DIR}/pointer_targets_check.sh" \
  "${verification_xref}" \
  "${POINTER_TARGETS_FILE}"

bash "${SCRIPT_DIR}/embedded_pointer_targets_check.sh" \
  "${verification_xref}" \
  "${EMBEDDED_POINTER_TARGETS_FILE}"

bash "${SCRIPT_DIR}/split_pointer_targets_check.sh" \
  "${verification_xref}" \
  "${SPLIT_POINTER_TARGETS_FILE}"

python3 "${SCRIPT_DIR}/embedded_pointer_audit.py" \
  "${ASM_FILE}"

bash "${SCRIPT_DIR}/base_readability_kpi.sh" \
  "${ASM_FILE}" --strict --strict-equates

# Hard gate for established whole-body findings; newly detected prefix-only
# findings stay advisory here until the corpus migration is complete. Maturity
# retains the full strict check.
python3 "${SCRIPT_DIR}/pointer_table_body_check.py" \
  "${ASM_FILE}" --strict-whole-body

bash "${SCRIPT_DIR}/inferred_kpi.sh" \
  "${ASM_FILE}" \
  "${INFERRED_KPI_FILE}"

bash "${SCRIPT_DIR}/comment_quality_kpi.sh" \
  "${ASM_FILE}" \
  "${COMMENT_KPI_FILE}"

bash "${SCRIPT_DIR}/project_comment_audit.sh" \
  "$1" \
  text

bash "${SCRIPT_DIR}/data_label_doc_kpi.sh" \
  "${ASM_FILE}" \
  "${DATA_LABEL_DOC_KPI_FILE}"

bash "${SCRIPT_DIR}/data_extent_assertions_check.sh" \
  "${ASM_FILE}" \
  "${DATA_EXTENT_ASSERTIONS_FILE}"
