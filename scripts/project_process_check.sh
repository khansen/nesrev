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

renames_header="$(head -n 1 "${RENAMES_FILE}" || true)"
if [[ "${renames_header}" != "old_name,new_name,reason,confidence,pass_id" ]]; then
  echo "invalid renames.csv header in ${RENAMES_FILE}" >&2
  exit 1
fi

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

  python3 - "${PROGRESS_SCORECARD_FILE}" <<'PY'
import re
import sys
from pathlib import Path

path = Path(sys.argv[1])
header = None
pass_one_rows = []

for lineno, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
    line = raw.strip()
    if not (line.startswith("|") and line.endswith("|")):
        continue
    cells = [cell.strip() for cell in line.strip("|").split("|")]
    if cells and cells[0] == "pass_id":
        header = cells
    elif cells and cells[0] == "1":
        pass_one_rows.append((lineno, cells))

if not pass_one_rows:
    raise SystemExit(0)
if header is None or "notes" not in header:
    print(f"invalid scorecard header in {path}: missing notes column", file=sys.stderr)
    raise SystemExit(1)
if len(pass_one_rows) != 1:
    lines = ", ".join(str(lineno) for lineno, _ in pass_one_rows)
    print(f"invalid pass-1 scorecard rows in {path}: found at lines {lines}", file=sys.stderr)
    raise SystemExit(1)

lineno, cells = pass_one_rows[0]
if len(cells) != len(header):
    print(f"invalid pass-1 scorecard row at {path}:{lineno}: column count mismatch", file=sys.stderr)
    raise SystemExit(1)

notes = cells[header.index("notes")]
analogue = re.search(
    r"\bAnalogue:\s*[a-z0-9_-]+\s*\([^)]+\S\)",
    notes,
    flags=re.IGNORECASE,
)
if analogue is None:
    print(
        f"{path}:{lineno}: pass 1 notes must record "
        "'Analogue: <project_slug|none> (<applied pattern or reason it did not fit>)'",
        file=sys.stderr,
    )
    raise SystemExit(1)
PY
fi

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
  data_format_required_args=()
  if [[ "${DATA_FORMAT_TARGETS_REQUIRED}" == "1" ]]; then
    data_format_required_args=(--required)
  fi
  python3 "${SCRIPT_DIR}/data_format_targets_check.py" \
    "${DATA_FORMAT_TARGETS_FILE}" \
    --doc-root "${DOC_ROOT}" \
    --mode process \
    "${data_format_required_args[@]}"
fi

echo "OK: project process checks passed"
