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
if [[ -n "${NESREV_ANALYSIS_BUNDLE+x}" || -n "${NESREV_ANALYSIS_BUILD_DIR+x}" || -n "${NESREV_XREF_FILE+x}" ]]; then
  echo "error: pass prep requires fresh owned analysis; do not supply analysis inputs" >&2
  exit 65
fi

pass_dir="${DOC_ROOT}/inventory/pass"
mkdir -p "${pass_dir}" "$(dirname "${OUT_BIN}")"

slug="$1"
generated="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
XASM_BIN="${XASM_BIN:-xasm}"
XASM_COMPARE_MISMATCH_EXIT=5
TMPDIR_PASS_PREP="$(mktemp -d)"
trap 'rm -rf "${TMPDIR_PASS_PREP}"' EXIT
prepare_project_analysis_bundle "$1" "${TMPDIR_PASS_PREP}" pass-prep-instructions-v1

status_json() {
  local status="$1"
  local exit_code="$2"
  local stdout_file="$3"
  local stderr_file="$4"
  python3 - "$status" "$exit_code" "$stdout_file" "$stderr_file" <<'PY'
import json
import sys

status, exit_code, stdout_file, stderr_file = sys.argv[1:]
print(json.dumps({
    "status": status,
    "exit_code": int(exit_code),
    "stdout": stdout_file,
    "stderr": stderr_file,
}))
PY
}

run_status() {
  local name="$1"
  shift

  local stdout_file="${pass_dir}/${name}.stdout"
  local stderr_file="${pass_dir}/${name}.stderr"
  local status="pass"
  local exit_code=0

  if "$@" >"${stdout_file}" 2>"${stderr_file}"; then
    status="pass"
  else
    exit_code=$?
    status="fail"
  fi

  status_json "$status" "$exit_code" "$stdout_file" "$stderr_file"
}

compare_stdout_file="${pass_dir}/compare.stdout"
compare_stderr_file="${pass_dir}/compare.stderr"
compare_ref_prg="${TMPDIR_PASS_PREP}/reference_prg.bin"
compare_status="pass"
compare_exit_code=0
compare_args=()

if extract_reference_prg_from_ines "${REF_NES}" "${compare_ref_prg}" >"${compare_stdout_file}" 2>"${compare_stderr_file}"; then
  compare_args=("--compare=${compare_ref_prg}" "--compare-format=json")
  if [[ -n "${XASM_COMPARE_CPU_BASE:-}" ]]; then
    compare_args+=("--compare-cpu-base=${XASM_COMPARE_CPU_BASE}")
  fi
else
  compare_exit_code=$?
  compare_status="fail"
fi

echo "[1/5] Generating primary xasm analysis bundle"
if python3 "${SCRIPT_DIR}/analysis_bundle.py" produce --profile pass-prep-instructions-v1 \
    "${TMPDIR_PASS_PREP}" "${ASM_FILE}" "${OUT_BIN}" >"${TMPDIR_PASS_PREP}/primary.stdout" 2>"${TMPDIR_PASS_PREP}/primary.stderr"; then
  :
else
  bundle_exit_code=$?
  cat "${TMPDIR_PASS_PREP}/primary.stderr" >&2
  exit "${bundle_exit_code}"
fi
export NESREV_ANALYSIS_BUNDLE="${TMPDIR_PASS_PREP}/bundle.json"
export NESREV_XREF_FILE="${TMPDIR_PASS_PREP}/xref_with_data.json"
if (( ${#compare_args[@]} > 0 )); then
  cp "${TMPDIR_PASS_PREP}/primary.stderr" "${compare_stderr_file}"
  if python3 "${SCRIPT_DIR}/analysis_prefix_compare.py" "${NESREV_ANALYSIS_BUNDLE}" "${compare_ref_prg}" \
      >"${compare_stdout_file}" 2>>"${compare_stderr_file}"; then
    :
  else
    compare_exit_code=$?
    compare_status="fail"
    if (( compare_exit_code == XASM_COMPARE_MISMATCH_EXIT )); then
      diagnostic_exit_code=0
      "${XASM_BIN}" --pure-binary -o "${TMPDIR_PASS_PREP}/diagnostic.o" "${compare_args[@]}" "${ASM_FILE}" \
        >"${compare_stdout_file}" 2>>"${compare_stderr_file}" || diagnostic_exit_code=$?
      if (( diagnostic_exit_code != XASM_COMPARE_MISMATCH_EXIT )); then
        echo "error: mismatch diagnostic returned unexpected exit ${diagnostic_exit_code}" >>"${compare_stderr_file}"
        if (( diagnostic_exit_code == 0 )); then
          exit 65
        fi
        exit "${diagnostic_exit_code}"
      fi
    else
      cat "${compare_stderr_file}" >&2
      exit "${compare_exit_code}"
    fi
  fi
fi
validate_project_analysis_bundle "$1"
cp "${TMPDIR_PASS_PREP}/summary.json" "${pass_dir}/xref_summary_all.json"
cp "${TMPDIR_PASS_PREP}/coverage.json" "${pass_dir}/data_coverage.json"
for artifact in xref_with_data index_patterns data_consumers; do
  cp "${TMPDIR_PASS_PREP}/${artifact}.json" "${pass_dir}/${artifact}.json"
done
echo "[2/5] Refreshing inventory from the primary xref"
bash "${SCRIPT_DIR}/refresh_inventory.sh" "${slug}"

echo "[3/5] Generating xref summary (generic labels)"
"${XASM_BIN}" --pure-binary -o "${TMPDIR_PASS_PREP}/generic.o" \
  --xref-summary \
  --xref-summary-output="${pass_dir}/xref_summary_generic.json" \
  --xref-summary-format=json \
  --xref-summary-include='^L[0-9A-F]{4,5}$' \
  "${ASM_FILE}" >/dev/null

if [[ "${PROJECT_PASS_PREP_WRITE_RAW_RAM_REVIEW:-1}" == "1" ]]; then
  echo "[4/5] Refreshing raw-RAM review queue"
  PROJECT_NEXT_PASS_AUTO_PREP=0 \
  PROJECT_NEXT_PASS_WRITE_RAW_RAM_REVIEW=1 \
  PROJECT_NEXT_PASS_RAW_RAM_REFRESH_ONLY=1 \
    bash "${SCRIPT_DIR}/project_next_pass.sh" "${slug}" json >/dev/null
else
  echo "[4/5] Skipping raw-RAM review queue refresh"
fi

echo "[5/5] Capturing baseline status"
compare_status_json="$(status_json "${compare_status}" "${compare_exit_code}" "${compare_stdout_file}" "${compare_stderr_file}")"
docs_status_json="$(run_status docs_check bash "${SCRIPT_DIR}/project_docs_check.sh" "${slug}")"
process_status_json="$(run_status process_check bash "${SCRIPT_DIR}/project_process_check.sh" "${slug}")"
raw_report="$(bash "${SCRIPT_DIR}/raw_address_kpi.sh" "${ASM_FILE}")"
raw_lowaddr="$(printf '%s\n' "${raw_report}" | awk -F= '/strict_active_raw_lowaddr=/{print $2}')"
raw_absrom="$(printf '%s\n' "${raw_report}" | awk -F= '/strict_active_raw_absrom=/{print $2}')"
if [[ ! "${raw_lowaddr}" =~ ^[0-9]+$ || ! "${raw_absrom}" =~ ^[0-9]+$ ]]; then
  echo "error: raw-address analysis returned no measured counts" >&2
  exit 65
fi
validate_project_analysis_bundle "$1"

python3 - \
  "${slug}" \
  "${generated}" \
  "${pass_dir}" \
  "${compare_status_json}" \
  "${docs_status_json}" \
  "${process_status_json}" \
  "${ASM_FILE}" \
  "${WARN_BASELINE_FILE}" \
  "${DOC_ROOT}/inventory/unknowns.md" \
  "${raw_lowaddr}" <<'PY' > "${pass_dir}/baseline_status.json"
import json
import os
import re
import sys
from pathlib import Path

slug = sys.argv[1]
generated = sys.argv[2]
pass_dir = sys.argv[3]
compare = json.loads(sys.argv[4])
docs = json.loads(sys.argv[5])
process = json.loads(sys.argv[6])
asm_file = Path(sys.argv[7])
warn_file = Path(sys.argv[8])
unknowns_file = Path(sys.argv[9])
raw_lowaddr = int(sys.argv[10] or 0)

GENERIC_RE = re.compile(r"\bL[0-9A-F]{4,5}\b")
GENERIC_DEF_RE = re.compile(r"(?m)^L[0-9A-F]{4,5}:")

def read_text(path):
    if not path.exists():
        return ""
    return path.read_text(encoding="utf-8")

def count_warning_lines(path):
    count = 0
    for line in read_text(path).splitlines():
        s = line.strip()
        if not s or s.startswith("#"):
            continue
        count += 1
    return count

def parse_unknowns(path):
    text = read_text(path)
    patterns = {
        "undocumented_callables": r"Undocumented callable procedures:\s+(\d+)\s*/\s*(\d+)",
        "noncompliant_data_labels": r"Noncompliant data labels .*:\s+(\d+)\s*/\s*(\d+)",
    }
    out = {}
    for key, pat in patterns.items():
        m = re.search(pat, text)
        if not m:
            continue
        out[key] = int(m.group(1))
        out[f"{key}_total"] = int(m.group(2))
    return out

asm_text = read_text(asm_file)
unknowns = parse_unknowns(unknowns_file)

payload = {
    "project": slug,
    "generated": generated,
    "artifacts_dir": pass_dir,
    "checks": {
        "parity": compare,
        "docs_check": docs,
        "process_check": process,
    },
    "artifacts": {
        "xref_summary_all": os.path.join(pass_dir, "xref_summary_all.json"),
        "xref_summary_generic": os.path.join(pass_dir, "xref_summary_generic.json"),
        "xref_with_data": os.path.join(pass_dir, "xref_with_data.json"),
        "index_patterns": os.path.join(pass_dir, "index_patterns.json"),
        "data_consumers": os.path.join(pass_dir, "data_consumers.json"),
        "data_coverage": os.path.join(pass_dir, "data_coverage.json"),
    },
    "metrics": {
        "lxxxx_definitions": len(GENERIC_DEF_RE.findall(asm_text)),
        "lxxxx_occurrences": len(GENERIC_RE.findall(asm_text)),
        "undocumented_callables": unknowns.get("undocumented_callables"),
        "undocumented_callables_total": unknowns.get("undocumented_callables_total"),
        "noncompliant_data_labels": unknowns.get("noncompliant_data_labels"),
        "noncompliant_data_labels_total": unknowns.get("noncompliant_data_labels_total"),
        "warning_baseline_count": count_warning_lines(warn_file),
        "strict_active_raw_lowaddr": raw_lowaddr,
    },
}

print(json.dumps(payload, indent=2))
PY

echo "pass prep complete: ${slug} -> ${pass_dir}"
