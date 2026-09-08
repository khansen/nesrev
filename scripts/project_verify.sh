#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <project_slug>" >&2
  exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=scripts/project_common.sh
source "${SCRIPT_DIR}/project_common.sh"

load_project_analysis_conf "$1"
validate_project_analysis_bundle "$1"
if [[ -n "${NESREV_ANALYSIS_BUNDLE+x}" ]]; then
  echo "error: project-verify requires fresh verification production, not a supplied bundle" >&2
  exit 65
fi
python3 "${SCRIPT_DIR}/project_policy_config_check.py" kpis "${KPI_FILE}"

TMPDIR_PROJECT_VERIFY="$(mktemp -d)"
trap 'rm -rf "${TMPDIR_PROJECT_VERIFY}"' EXIT
if [[ -z "${NESREV_ANALYSIS_BUILD_DIR+x}" ]]; then
  export NESREV_ANALYSIS_BUILD_DIR="${TMPDIR_PROJECT_VERIFY}"
  prepare_project_analysis_bundle "$1" "${NESREV_ANALYSIS_BUILD_DIR}" ci-instructions-v1
elif [[ -z "${NESREV_ANALYSIS_BUILD_DIR}" ]]; then
  echo "error: empty supplied analysis build directory" >&2
  exit 65
fi
verification_xref="${NESREV_ANALYSIS_BUILD_DIR}/xref_with_data.json"
if [[ -n "${NESREV_XREF_FILE+x}" && "${NESREV_XREF_FILE}" != "${verification_xref}" ]]; then
  echo "error: verification xref must use its owning analysis directory" >&2
  exit 65
fi
export NESREV_XREF_FILE="${verification_xref}"

bash "${SCRIPT_DIR}/verify.sh" \
  "${ASM_FILE}" \
  "${REF_NES}" \
  "${OUT_BIN}" \
  "${WARN_BASELINE_FILE}" \
  "${XASM_COMPARE_CPU_BASE:-}" \
  "${verification_xref}"

if [[ -n "${NESREV_ANALYSIS_BUILD_DIR:-}" ]]; then
  export NESREV_ANALYSIS_BUNDLE="${NESREV_ANALYSIS_BUILD_DIR}/bundle.json"
fi
python3 "${SCRIPT_DIR}/analysis_bundle.py" validate "${NESREV_ANALYSIS_BUNDLE}" --profile ci-instructions-v1
validate_project_analysis_bundle "$1"

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

python3 "${SCRIPT_DIR}/branch_literals.py" verify \
  "${ASM_FILE}" \
  "${BRANCH_KPI_FILE}" --registry "${BRANCH_SITES_FILE}"

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

if [[ -n "${NESREV_ANALYSIS_BUNDLE:-}" ]]; then
  python3 "${SCRIPT_DIR}/analysis_bundle.py" validate "${NESREV_ANALYSIS_BUNDLE}" --source "${ASM_FILE}"
fi
