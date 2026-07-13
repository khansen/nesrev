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

raw_report="$(bash "${SCRIPT_DIR}/raw_address_kpi.sh" "${ASM_FILE}" 2>/dev/null || true)"
raw_lowaddr="$(printf '%s\n' "${raw_report}" | awk -F= '/strict_active_raw_lowaddr=/{print $2}')"
raw_absrom="$(printf '%s\n' "${raw_report}" | awk -F= '/strict_active_raw_absrom=/{print $2}')"
raw_lowaddr="${raw_lowaddr:-unknown}"
raw_absrom="${raw_absrom:-unknown}"

data_doc_report="$(bash "${SCRIPT_DIR}/data_label_doc_kpi.sh" "${ASM_FILE}" 2>/dev/null || true)"
data_noncompliant="$(printf '%s\n' "${data_doc_report}" | awk -F= '/strict_data_labels_noncompliant=/{print $2}')"
data_noncompliant="${data_noncompliant:-unknown}"

proc_doc_report="$(bash "${SCRIPT_DIR}/procedure_doc_kpi.sh" "${ASM_FILE}" 2>/dev/null || true)"
proc_total="$(printf '%s\n' "${proc_doc_report}" | awk -F= '/strict_callable_procedures_total=/{print $2}')"
proc_documented="$(printf '%s\n' "${proc_doc_report}" | awk -F= '/strict_callable_procedures_documented=/{print $2}')"
proc_total="${proc_total:-unknown}"
proc_documented="${proc_documented:-unknown}"

global_doc_report="$(bash "${SCRIPT_DIR}/global_code_label_doc_kpi.sh" "${ASM_FILE}" 2>/dev/null || true)"
global_total="$(printf '%s\n' "${global_doc_report}" | awk -F= '/strict_global_code_labels_total=/{print $2}')"
global_documented="$(printf '%s\n' "${global_doc_report}" | awk -F= '/strict_global_code_labels_documented=/{print $2}')"
global_total="${global_total:-unknown}"
global_documented="${global_documented:-unknown}"

scorecard_tbd_count="$({ rg -o 'TBD' "${PROGRESS_SCORECARD_FILE}" 2>/dev/null || true; } | wc -l | tr -d ' ')"
scorecard_tbd_count="${scorecard_tbd_count:-0}"

fail=0
if ! data_extent_report="$(bash "${SCRIPT_DIR}/data_extent_assertions_check.sh" "${ASM_FILE}" "${DATA_EXTENT_ASSERTIONS_FILE}" 2>&1)"; then
  printf '%s\n' "${data_extent_report}" >&2
  echo "maturity gate failed: data extent assertions failed" >&2
  fail=1
fi
if [[ -f "${EMBEDDED_POINTER_TARGETS_FILE}" ]]; then
  if ! embedded_targets_report="$(bash "${SCRIPT_DIR}/embedded_pointer_targets_check.sh" "${ASM_FILE}" "${EMBEDDED_POINTER_TARGETS_FILE}" 2>&1)"; then
    printf '%s\n' "${embedded_targets_report}" >&2
    echo "maturity gate failed: embedded pointer target registry is stale" >&2
    fail=1
  fi
fi
if [[ "${EMBEDDED_POINTER_AUDIT_REQUIRED}" == "1" ]]; then
  if ! embedded_audit_report="$(python3 "${SCRIPT_DIR}/embedded_pointer_audit.py" "${ASM_FILE}" 2>&1)"; then
    printf '%s\n' "${embedded_audit_report}" >&2
    echo "maturity gate failed: embedded pointer audit failed" >&2
    fail=1
  fi
fi
if ! pointer_table_report="$(python3 "${SCRIPT_DIR}/pointer_table_body_check.py" "${ASM_FILE}" --strict 2>&1)"; then
  printf '%s\n' "${pointer_table_report}" >&2
  echo "maturity gate failed: pointer-table bodies must be symbolic" >&2
  fail=1
fi
if [[ "${raw_lowaddr}" != "0" || "${raw_absrom}" != "0" ]]; then
  echo "maturity gate failed: raw-address debt is not zero (${raw_lowaddr}/${raw_absrom})" >&2
  fail=1
fi
if [[ "${data_noncompliant}" != "0" ]]; then
  echo "maturity gate failed: noncompliant data labels remain (${data_noncompliant})" >&2
  fail=1
fi
if [[ "${PROCEDURE_CONTRACTS_REQUIRED}" == "1" ]]; then
  if [[ "${proc_total}" == "unknown" || "${proc_documented}" == "unknown" ]]; then
    echo "maturity gate failed: procedure-contract audit could not read callable procedure counts" >&2
    fail=1
  elif (( proc_total > 0 && proc_documented < MIN_MATURITY_DOCUMENTED_PROCEDURES )); then
    echo "maturity gate failed: procedure-contract audit skipped (${proc_documented}/${proc_total} documented callables; minimum ${MIN_MATURITY_DOCUMENTED_PROCEDURES})" >&2
    fail=1
  fi
  if [[ "${global_total}" == "unknown" || "${global_documented}" == "unknown" ]]; then
    echo "maturity gate failed: procedure-contract audit could not read global code-label counts" >&2
    fail=1
  elif (( global_total > 0 && global_documented < MIN_MATURITY_DOCUMENTED_GLOBAL_CODE_LABELS )); then
    echo "maturity gate failed: procedure-contract audit skipped (${global_documented}/${global_total} documented global code labels; minimum ${MIN_MATURITY_DOCUMENTED_GLOBAL_CODE_LABELS})" >&2
    fail=1
  fi
fi

# Semantic-claims gold-closeout gate. Opted-in projects (SEMANTIC_CLAIMS_REQUIRED=1,
# set by new scaffolds) use maturity mode, which additionally requires at least
# one real claim — a sparse ledger is only acceptable pass-time, not at maturity.
# Legacy projects are advisory and the checker exits 0 on its own, so this never
# fails an unopted legacy project.
sc_mode="advisory"
if [[ "${SEMANTIC_CLAIMS_REQUIRED}" == "1" ]]; then
  sc_mode="maturity"
fi
if ! python3 "${SCRIPT_DIR}/project_semantic_claims_check.py" \
    "${ASM_FILE}" "${SEMANTIC_CLAIMS_FILE}" --mode "${sc_mode}"; then
  echo "maturity gate failed: semantic-claims check failed" >&2
  fail=1
fi

if [[ "${LEGACY_RETROFIT_REQUIRED}" == "1" ]]; then
  if ! bash "${SCRIPT_DIR}/project_legacy_retrofit_check.sh" "$1" --require; then
    echo "maturity gate failed: legacy retrofit audit check failed" >&2
    fail=1
  fi
fi

if [[ "${WORKING_NOTES_MATURITY_REQUIRED}" == "1" ]]; then
  if ! bash "${SCRIPT_DIR}/working_notes_maturity_check.sh" \
      "${WORKING_NOTES_FILE}" "${MAX_MATURITY_WORKING_NOTES_LINES}"; then
    echo "maturity gate failed: working-notes pruning check failed" >&2
    fail=1
  fi
fi

# Constantization smell (advisory, independent of the hard gates): a game of any
# size should reach maturity with some intentional raw literals recorded in the
# allowlist. A magic-immediate count of 0 alongside an empty allowlist usually
# means every literal was symbolized rather than judged (mundane constantisation),
# not that the code genuinely has no clearer-raw literals.
const_report="$(bash "${SCRIPT_DIR}/constant_kpi.sh" "${ASM_FILE}" 2>/dev/null || true)"
magic_count="$(printf '%s\n' "${const_report}" | awk -F= '/strict_active_magic_immediates=/{print $2}')"
allowlist_rows="$(awk -F',' 'NR>1 && $0 !~ /^[[:space:]]*(#|$)/ && NF>=3 {c++} END{print c+0}' \
  "${DOC_ROOT}/inventory/constant_magic_allowlist.csv" 2>/dev/null || echo 0)"
if [[ "${magic_count:-x}" == "0" && "${allowlist_rows}" == "0" ]]; then
  echo "warn: strict_active_magic_immediates=0 with an empty constant_magic_allowlist.csv — likely over-constantisation (every literal symbolized rather than judged); expect a game of any size to retain some intentional raw literals (see agent_playbook/ASM_STYLE.md readability-first constantization)" >&2
fi

if [[ ${fail} -ne 0 ]]; then
  exit 1
fi

echo "OK: maturity hard gates passed"
if [[ "${scorecard_tbd_count}" != "0" ]]; then
  echo "warn: scorecard still contains ${scorecard_tbd_count} TBD fields" >&2
fi
