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

required_files=(
  "${CROSSWALK_FILE}"
  "${ONBOARDING_FILE}"
  "${QUICK_REFERENCE_FILE}"
  "${PROGRESS_SCORECARD_FILE}"
  "${RENAMES_FILE}"
)

echo "[1/4] Checking required process artifacts"
missing=0
for path in "${required_files[@]}"; do
  if [[ ! -f "${path}" ]]; then
    echo "missing required process file: ${path}" >&2
    missing=1
  fi
done

if [[ ${missing} -ne 0 ]]; then
  exit 1
fi

# Scorecard cells must not contain a raw '|' (the Markdown-table column
# delimiter): a pipe inside a cell breaks rendering and the row parsers.
python3 "${SCRIPT_DIR}/scorecard_cell_check.py" "${PROGRESS_SCORECARD_FILE}"
if [[ "${SCORECARD_LIFECYCLE_REQUIRED}" == "1" ]]; then
  python3 "${SCRIPT_DIR}/scorecard_lifecycle_check.py" "${PROGRESS_SCORECARD_FILE}"
fi

# The proof-debt ledgers are authored artifacts; validate their shape here
# alongside the others rather than discovering a malformed row a pass later.
for _pd_ledger in \
  "${DOC_ROOT}/inventory/deferrals.csv:pass_id,corridor,subject,kind,deferral,revisit_condition,status" \
  "${DOC_ROOT}/inventory/proof_debt_acknowledged.csv:signal,reason,pass_id"; do
  _pd_path="${_pd_ledger%%:*}"
  _pd_want="${_pd_ledger#*:}"
  if [[ -f "${_pd_path}" ]]; then
    _pd_have="$(head -n 1 "${_pd_path}" || true)"
    if [[ "${_pd_have}" != "${_pd_want}" ]]; then
      echo "invalid header in ${_pd_path}" >&2
      echo "expected: ${_pd_want}" >&2
      exit 1
    fi
    python3 - "${_pd_path}" "${_pd_want}" <<'PDPY'
import csv, sys
from pathlib import Path
path, header = Path(sys.argv[1]), sys.argv[2].split(",")
with path.open(newline="", encoding="utf-8") as fh:
    for i, row in enumerate(csv.reader(fh), start=1):
        if i == 1:
            continue
        if len(row) != len(header):
            print(f"{path}:{i}: expected {len(header)} fields, found {len(row)}", file=sys.stderr)
            raise SystemExit(1)
        # Enum columns, because a typo that lands outside the set is read as
        # "not runtime" / "not open" and silently suppresses a signal.
        cells = dict(zip(header, row))
        for column, allowed in (("kind", {"static", "runtime"}),
                                ("status", {"open", "closed"})):
            value = (cells.get(column) or "").strip()
            if column in header and value not in allowed:
                print(
                    f"{path}:{i}: {column}={value!r} is not one of "
                    f"{sorted(allowed)}",
                    file=sys.stderr,
                )
                raise SystemExit(1)
PDPY
  fi
done

renames_header="$(head -n 1 "${RENAMES_FILE}" || true)"
if [[ "${renames_header}" != "old_name,new_name,reason,confidence,pass_id" ]]; then
  echo "invalid renames.csv header in ${RENAMES_FILE}" >&2
  exit 1
fi

analogue_slug=""
if [[ "${NESREV_RECOVERY_STATUS}" != "legacy" ]]; then
  crosswalk_header="$(
    rg -m1 '^\| Reference term / aliases \| Asm symbol\(s\) \| Mapping confidence \| Evidence \|$' \
      "${CROSSWALK_FILE}" || true
  )"
  if [[ -z "${crosswalk_header}" ]]; then
    echo "invalid terminology crosswalk header in ${CROSSWALK_FILE}" >&2
    echo "expected: | Reference term / aliases | Asm symbol(s) | Mapping confidence | Evidence |" >&2
    exit 1
  fi

  analogue_slug="$(
    python3 "${SCRIPT_DIR}/scorecard_analogue.py" "${PROGRESS_SCORECARD_FILE}"
  )"
fi

echo "[inventory] Checking generated inventory and raw-RAM owner sync"
python3 "${SCRIPT_DIR}/inventory_sync_check.py" \
  "$1" \
  "${ASM_FILE}" \
  "${DOC_ROOT}" \
  "${SCRIPT_DIR}/refresh_inventory.sh"

echo "[2/4] Checking RAM/ZP symbol naming"
python3 "${SCRIPT_DIR}/check_symbol_naming.py" "${ASM_FILE}"

echo "[3/4] Checking for suspicious RAM/ZP immediates"
if rg -n '^\s+[A-Z]{3}(?:\.[A-Z])?\s+#(?:ZP_|RAM_)[A-Za-z0-9_]+' "${ASM_FILE}" >/dev/null; then
  echo "suspicious RAM/ZP symbol used as immediate in ${ASM_FILE}" >&2
  rg -n '^\s+[A-Z]{3}(?:\.[A-Z])?\s+#(?:ZP_|RAM_)[A-Za-z0-9_]+' "${ASM_FILE}" >&2
  exit 1
fi

# Advisory only (must not fail the gate): warn on project-local hardware-prefixed
# .EQU names that are not canonical and not allowlisted.
echo "[4/4] Checking canonical hardware-constant drift (advisory)"
python3 "${SCRIPT_DIR}/check_hardware_constant_drift.py" \
  "${ASM_FILE}" \
  "${SCRIPT_DIR}/../agent_playbook/ASM_STYLE.md" \
  "${DOC_ROOT}/inventory/hardware_local_allowlist.txt" || true

# The scorecard-selected analogue supplies the comparison input. This remains
# advisory because same-valued literals can be semantically unrelated; the
# checker requires family evidence to keep the review shortlist narrow.
if [[ -n "${analogue_slug}" && "${analogue_slug}" != "none" ]]; then
  echo "[prior-project-reuse] Checking evidence-backed analogue constants (advisory)"
  bash "${SCRIPT_DIR}/project_prior_reuse_check.sh" "$1"
fi

# New projects already opt into proof-debt signals. Keep this source-level
# family-completeness scan advisory until corpus calibration supports a hard
# gate; --strict remains available for a reviewed project-local zero baseline.
if [[ "${PROOF_DEBT_REQUIRED}" == "1" ]]; then
  echo "[constant-family] Checking raw state/request writers against existing constants (advisory)"
  python3 "${SCRIPT_DIR}/raw_immediate_constant_check.py" "${ASM_FILE}"

  echo "[semantic-evidence] Checking reference-order claims and derived-constant anchors (advisory)"
  python3 "${SCRIPT_DIR}/semantic_evidence_check.py" \
    "${ASM_FILE}" \
    "${CROSSWALK_FILE}"

  echo "[ppu-packet-lines] Checking declared packet-stream line boundaries (advisory)"
  python3 "${SCRIPT_DIR}/ppu_packet_line_check.py" "${ASM_FILE}"

  echo "[data-boundary] Checking small negative indexed data-label offsets (advisory)"
  python3 "${SCRIPT_DIR}/negative_data_offset_check.py" "${ASM_FILE}"
fi

# Advisory only (must not fail the gate): flag data tables whose index is
# provably bounded (mask or compare, resolved by xasm's index-pattern analysis)
# but that have no data_extent_assertions.csv entry pinning their size.
# Complements data_extent_assertions_check.sh, which only validates listed rows.
# Reads two cached pass-prep artifacts; never assembles.
echo "[data-extent-scan] Scanning for bounded-index tables missing an extent assertion (advisory)"
python3 "${SCRIPT_DIR}/data_extent_missing_scan.py" \
  "${DOC_ROOT}/inventory/pass/index_patterns.json" \
  "${DOC_ROOT}/inventory/pass/data_consumers.json" \
  "${DATA_EXTENT_ASSERTIONS_FILE}" || true

if [[ "${DATA_FORMAT_TARGETS_REQUIRED}" == "1" || -f "${DATA_FORMAT_TARGETS_FILE}" ]]; then
  echo "[data-format] Checking data-format target inventory"
  data_format_args=(
    "${DATA_FORMAT_TARGETS_FILE}"
    --doc-root "${DOC_ROOT}"
    --mode process
  )
  if [[ "${DATA_FORMAT_TARGETS_REQUIRED}" == "1" ]]; then
    data_format_args+=(--required)
  fi
  python3 "${SCRIPT_DIR}/data_format_targets_check.py" \
    "${data_format_args[@]}"
fi

if [[ "${DATA_BLOB_DISPOSITIONS_REQUIRED}" == "1" || -f "${DATA_BLOB_DISPOSITIONS_FILE}" ]]; then
  echo "[data-blobs] Checking data-blob disposition inventory"
  data_blob_args=(
    "${DATA_BLOB_DISPOSITIONS_FILE}"
    --doc-root "${DOC_ROOT}"
    --data-coverage "${DOC_ROOT}/inventory/pass/data_coverage.json"
    --asm "${ASM_FILE}"
    --mode process
  )
  if [[ -n "${DATA_BLOB_RENAMED_PASS:-}" ]]; then
    data_blob_args+=(
      --renames "${RENAMES_FILE}"
      --renamed-pass "${DATA_BLOB_RENAMED_PASS}"
    )
  fi
  if [[ "${DATA_BLOB_DISPOSITIONS_REQUIRED}" == "1" ]]; then
    data_blob_args+=(--required)
  fi
  python3 "${SCRIPT_DIR}/data_blob_dispositions_check.py" \
    "${data_blob_args[@]}"
fi

echo "OK: project process checks passed"
