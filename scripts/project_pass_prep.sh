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

pass_dir="${DOC_ROOT}/inventory/pass"
mkdir -p "${pass_dir}" "$(dirname "${OUT_BIN}")"

slug="$1"
generated="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
XASM_BIN="${XASM_BIN:-xasm}"
XASM_COMPARE_MISMATCH_EXIT=5
TMPDIR_PASS_PREP="$(mktemp -d)"
trap 'rm -rf "${TMPDIR_PASS_PREP}"' EXIT

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

echo "[1/4] Refreshing inventory"
bash "${SCRIPT_DIR}/refresh_inventory.sh" "${slug}"

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

bundle_stdout_file="/dev/null"
bundle_stderr_file="${TMPDIR_PASS_PREP}/primary_bundle.stderr"
if (( ${#compare_args[@]} > 0 )); then
  bundle_stdout_file="${compare_stdout_file}"
  bundle_stderr_file="${compare_stderr_file}"
fi

primary_artifacts=(
  "${pass_dir}/xref_summary_all.json"
  "${pass_dir}/xref_with_data.json"
  "${pass_dir}/index_patterns.json"
  "${pass_dir}/data_consumers.json"
  "${pass_dir}/data_coverage.json"
)

echo "[2/4] Generating primary xasm analysis/compare bundle"
bundle_cmd=("${XASM_BIN}" --pure-binary -o "${OUT_BIN}")
if (( ${#compare_args[@]} > 0 )); then
  bundle_cmd+=("${compare_args[@]}")
fi
bundle_cmd+=(
  --xref-summary
  --xref-summary-output="${pass_dir}/xref_summary_all.json"
  --xref-summary-format=json
  --xref="${pass_dir}/xref_with_data.json"
  --xref-format=json
  --xref-include-owner=true
  --xref-data=true
  --analyze-index-patterns
  --index-patterns-output="${pass_dir}/index_patterns.json"
  --index-patterns-format=json
  --data-consumers
  --data-consumers-output="${pass_dir}/data_consumers.json"
  --data-consumers-format=json
  --analyze-data-coverage
  --data-coverage-output="${pass_dir}/data_coverage.json"
  --data-coverage-format=json
  "${ASM_FILE}"
)
bundle_exit_code=0
if "${bundle_cmd[@]}" >"${bundle_stdout_file}" 2>"${bundle_stderr_file}"; then
  bundle_exit_code=0
else
  bundle_exit_code=$?
  if (( ${#compare_args[@]} > 0 )); then
    compare_status="fail"
    compare_exit_code="${bundle_exit_code}"
  fi
fi

if (( bundle_exit_code != 0 )); then
  missing_primary=0
  for path in "${primary_artifacts[@]}"; do
    if [[ ! -f "${path}" ]]; then
      echo "error: primary xasm analysis bundle did not produce ${path}" >&2
      missing_primary=1
    fi
  done
  if (( ${#compare_args[@]} == 0 || bundle_exit_code != XASM_COMPARE_MISMATCH_EXIT || missing_primary != 0 )); then
    if [[ -s "${bundle_stderr_file}" ]]; then
      cat "${bundle_stderr_file}" >&2
    fi
    exit "${bundle_exit_code}"
  fi
fi

echo "[3/4] Generating xref summary (generic labels)"
"${XASM_BIN}" --pure-binary -o "${OUT_BIN}" \
  --xref-summary \
  --xref-summary-output="${pass_dir}/xref_summary_generic.json" \
  --xref-summary-format=json \
  --xref-summary-include='^L[0-9A-F]{4,5}$' \
  "${ASM_FILE}" >/dev/null

echo "[4/4] Capturing baseline status"
compare_status_json="$(status_json "${compare_status}" "${compare_exit_code}" "${compare_stdout_file}" "${compare_stderr_file}")"
docs_status_json="$(run_status docs_check bash "${SCRIPT_DIR}/project_docs_check.sh" "${slug}")"
process_status_json="$(run_status process_check bash "${SCRIPT_DIR}/project_process_check.sh" "${slug}")"
raw_report="$(bash "${SCRIPT_DIR}/raw_address_kpi.sh" "${ASM_FILE}")"
raw_lowaddr="$(printf '%s\n' "${raw_report}" | awk -F= '/strict_active_raw_lowaddr=/{print $2}')"

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
