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

echo "[1/8] Refreshing inventory"
bash "${SCRIPT_DIR}/refresh_inventory.sh" "${slug}"

echo "[2/8] Generating xref summary (all symbols)"
xasm --pure-binary -o "${OUT_BIN}" \
  --xref-summary \
  --xref-summary-output="${pass_dir}/xref_summary_all.json" \
  --xref-summary-format=json \
  "${ASM_FILE}" >/dev/null

echo "[3/8] Generating xref summary (generic labels)"
xasm --pure-binary -o "${OUT_BIN}" \
  --xref-summary \
  --xref-summary-output="${pass_dir}/xref_summary_generic.json" \
  --xref-summary-format=json \
  --xref-summary-include='^L[0-9A-F]{4,5}$' \
  "${ASM_FILE}" >/dev/null

echo "[4/8] Generating xref with data edges"
xasm --pure-binary -o "${OUT_BIN}" \
  --xref="${pass_dir}/xref_with_data.json" \
  --xref-format=json \
  --xref-include-owner=true \
  --xref-data=true \
  "${ASM_FILE}" >/dev/null

echo "[5/8] Generating index-pattern analysis"
xasm --pure-binary -o "${OUT_BIN}" \
  --analyze-index-patterns \
  --index-patterns-output="${pass_dir}/index_patterns.json" \
  --index-patterns-format=json \
  "${ASM_FILE}" >/dev/null

echo "[6/8] Generating data-consumer analysis"
xasm --pure-binary -o "${OUT_BIN}" \
  --data-consumers \
  --data-consumers-output="${pass_dir}/data_consumers.json" \
  --data-consumers-format=json \
  "${ASM_FILE}" >/dev/null

echo "[7/8] Generating data-coverage analysis"
xasm --pure-binary -o "${OUT_BIN}" \
  --analyze-data-coverage \
  --data-coverage-output="${pass_dir}/data_coverage.json" \
  --data-coverage-format=json \
  "${ASM_FILE}" >/dev/null

echo "[8/8] Capturing baseline status"
compare_status_json="$(run_status compare bash "${SCRIPT_DIR}/project_compare.sh" "${slug}" json)"
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
