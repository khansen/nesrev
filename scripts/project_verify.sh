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

bash "${SCRIPT_DIR}/verify.sh" \
  "${ASM_FILE}" \
  "${REF_NES}" \
  "${OUT_BIN}" \
  "${WARN_BASELINE_FILE}" \
  "${XASM_COMPARE_CPU_BASE:-}"

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
  "${ASM_FILE}" \
  "${POINTER_TARGETS_FILE}"

if [[ -f "${EMBEDDED_POINTER_TARGETS_FILE}" ]]; then
  bash "${SCRIPT_DIR}/embedded_pointer_targets_check.sh" \
    "${ASM_FILE}" \
    "${EMBEDDED_POINTER_TARGETS_FILE}"
fi

if [[ "${EMBEDDED_POINTER_AUDIT_REQUIRED}" == "1" ]]; then
  python3 "${SCRIPT_DIR}/embedded_pointer_audit.py" \
    "${ASM_FILE}"
fi

if [[ "${BASE_READABILITY_REQUIRED}" == "1" ]]; then
  # Hard gate for opted-in projects: fails if hex #$00/#$01 reappear in
  # index-register / unit-step quantity contexts.
  bash "${SCRIPT_DIR}/base_readability_kpi.sh" \
    "${ASM_FILE}" --strict
fi

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
