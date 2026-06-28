#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 <asm_file> <data_extent_assertions_csv>" >&2
  exit 64
fi

ASM_FILE="$1"
ASSERTIONS_FILE="$2"

if [[ ! -f "${ASM_FILE}" ]]; then
  echo "error: asm file not found: ${ASM_FILE}" >&2
  exit 65
fi

if [[ ! -f "${ASSERTIONS_FILE}" ]]; then
  echo "data_extent_assertions_total=0"
  echo "OK: no data extent assertions configured"
  exit 0
fi

tmpdir="$(mktemp -d -t nesrev_data_extent.XXXXXX)"
trap 'rm -rf "${tmpdir}"' EXIT

data_json="${tmpdir}/data_consumers.json"
out_bin="${tmpdir}/out.o"
xasm_stdout="${tmpdir}/xasm.stdout"
xasm_stderr="${tmpdir}/xasm.stderr"

if ! xasm --pure-binary \
    -o "${out_bin}" \
    --data-consumers \
    --data-consumers-output="${data_json}" \
    --data-consumers-format=json \
    "${ASM_FILE}" >"${xasm_stdout}" 2>"${xasm_stderr}"; then
  cat "${xasm_stdout}" >&2 || true
  cat "${xasm_stderr}" >&2 || true
  exit 66
fi

python3 - "${data_json}" "${ASSERTIONS_FILE}" <<'PY'
import csv
import json
import sys
from pathlib import Path

data_path = Path(sys.argv[1])
assertions_path = Path(sys.argv[2])

entries = json.loads(data_path.read_text(encoding="utf-8"))
sizes = {entry["label"]: int(entry["declared_size"]) for entry in entries}

raw_lines = [
    line
    for line in assertions_path.read_text(encoding="utf-8").splitlines()
    if line.strip() and not line.lstrip().startswith("#")
]

if not raw_lines:
    print("data_extent_assertions_total=0")
    print("OK: no data extent assertions configured")
    raise SystemExit(0)

reader = csv.DictReader(raw_lines)
expected_header = ["label", "expected_size", "reason"]
if reader.fieldnames != expected_header:
    print(
        f"invalid data extent assertion header in {assertions_path}: "
        f"expected {','.join(expected_header)}",
        file=sys.stderr,
    )
    raise SystemExit(67)

seen = set()
failures = []
count = 0
for row_num, row in enumerate(reader, start=2):
    count += 1
    label = (row.get("label") or "").strip()
    expected_raw = (row.get("expected_size") or "").strip()
    reason = (row.get("reason") or "").strip()
    if not label or not expected_raw or not reason:
        failures.append(f"row {row_num}: label, expected_size, and reason are required")
        continue
    if label in seen:
        failures.append(f"row {row_num}: duplicate label {label}")
        continue
    seen.add(label)
    try:
        expected = int(expected_raw, 0)
    except ValueError:
        failures.append(f"row {row_num}: expected_size is not an integer: {expected_raw}")
        continue
    if expected < 0:
        failures.append(f"row {row_num}: expected_size must be non-negative: {expected}")
        continue
    actual = sizes.get(label)
    if actual is None:
        failures.append(f"row {row_num}: asserted label not found in data spans: {label}")
        continue
    if actual != expected:
        failures.append(
            f"{label}: declared_size {actual} != expected_size {expected} ({reason})"
        )

print(f"data_extent_assertions_total={count}")
if failures:
    for failure in failures:
        print(f"FAIL: {failure}", file=sys.stderr)
    raise SystemExit(1)

print("OK: data extent assertions passed")
PY
