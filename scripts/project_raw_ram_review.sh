#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 3 || $# -gt 6 ]]; then
  echo "usage: $0 <project_slug> <addr_hex> <status> [proposed_symbol] [notes] [pass_id]" >&2
  exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=scripts/project_common.sh
source "${SCRIPT_DIR}/project_common.sh"

load_project_conf "$1"

ADDR_HEX="$2"
STATUS="$3"
PROPOSED_SYMBOL="${4:-}"
NOTES="${5:-}"
PASS_ID="${6:-}"

python3 - "${DOC_ROOT}/inventory/raw_ram_review.csv" "${ADDR_HEX}" "${STATUS}" "${PROPOSED_SYMBOL}" "${NOTES}" "${PASS_ID}" <<'PY'
import csv
import re
import sys
from pathlib import Path

review_path = Path(sys.argv[1])
addr_in = sys.argv[2].strip().lower()
status = sys.argv[3].strip()
proposed_symbol = sys.argv[4]
notes = sys.argv[5]
pass_id = sys.argv[6].strip()

allowed = {
    "candidate",
    "unreviewed",
    "deferred",
    "revisit",
    "not_semantic_yet",
    "symbolized",
}
if status not in allowed:
    raise SystemExit(f"error: invalid status {status!r}; expected one of {sorted(allowed)}")

m = re.fullmatch(r"(?:0x|\$)?([0-9a-f]{1,4})", addr_in)
if not m:
    raise SystemExit(f"error: invalid raw RAM address {addr_in!r}")
addr_hex = f"0x{int(m.group(1), 16):04x}"

fields = [
    "addr_hex",
    "status",
    "proposed_symbol",
    "notes",
    "last_pass_reviewed",
    "active",
    "operand_count",
    "distinct_owner_count",
    "read_count",
    "write_count",
    "top_readers",
    "top_writers",
]

if not review_path.exists():
    review_path.parent.mkdir(parents=True, exist_ok=True)
    with review_path.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fields, lineterminator='\n')
        writer.writeheader()

rows = []
updated = False
with review_path.open("r", encoding="utf-8", newline="") as f:
    reader = csv.DictReader(f)
    if reader.fieldnames != fields:
        raise SystemExit("error: raw_ram_review.csv header mismatch")
    for row in reader:
        if (row.get("addr_hex") or "").strip().lower() == addr_hex:
            row["status"] = status
            if proposed_symbol:
                row["proposed_symbol"] = proposed_symbol
            if notes:
                row["notes"] = notes
            if pass_id:
                row["last_pass_reviewed"] = pass_id
            updated = True
        rows.append({field: row.get(field, "") for field in fields})

if not updated:
    row = {field: "" for field in fields}
    row["addr_hex"] = addr_hex
    row["status"] = status
    row["proposed_symbol"] = proposed_symbol
    row["notes"] = notes
    row["last_pass_reviewed"] = pass_id
    row["active"] = "yes"
    rows.append(row)

with review_path.open("w", encoding="utf-8", newline="") as f:
    writer = csv.DictWriter(f, fieldnames=fields, lineterminator='\n')
    writer.writeheader()
    writer.writerows(rows)

print(f"updated {review_path} -> {addr_hex} status={status}")
PY
