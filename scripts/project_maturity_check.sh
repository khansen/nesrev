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

scorecard_tbd_count="$({ rg -o 'TBD' "${PROGRESS_SCORECARD_FILE}" 2>/dev/null || true; } | wc -l | tr -d ' ')"
scorecard_tbd_count="${scorecard_tbd_count:-0}"

fail=0
if [[ "${raw_lowaddr}" != "0" || "${raw_absrom}" != "0" ]]; then
  echo "maturity gate failed: raw-address debt is not zero (${raw_lowaddr}/${raw_absrom})" >&2
  fail=1
fi
if [[ "${data_noncompliant}" != "0" ]]; then
  echo "maturity gate failed: noncompliant data labels remain (${data_noncompliant})" >&2
  fail=1
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

if [[ ${fail} -ne 0 ]]; then
  exit 1
fi

echo "OK: maturity hard gates passed"
if [[ "${scorecard_tbd_count}" != "0" ]]; then
  echo "warn: scorecard still contains ${scorecard_tbd_count} TBD fields" >&2
fi
