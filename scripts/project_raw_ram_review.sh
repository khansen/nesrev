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

python3 - "${DOC_ROOT}/inventory/raw_ram_review.csv" "${ADDR_HEX}" "${STATUS}" "${PROPOSED_SYMBOL}" "${NOTES}" "${PASS_ID}" "${SCRIPT_DIR}" <<'PY'
import csv
import sys
from pathlib import Path

sys.path.insert(0, sys.argv[7])
from raw_ram_review import FIELDS as fields, parse_address, read_review

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

try:
    addr_hex = parse_address(addr_in)
    existing = read_review(review_path, require_field_order=True)
except (OSError, ValueError, csv.Error) as exc:
    raise SystemExit(f"error: {exc}") from exc

rows = []
updated = False
for address, row in existing.items():
    if address == addr_hex:
        row["status"] = status
        if proposed_symbol:
            row["proposed_symbol"] = proposed_symbol
        if notes:
            row["notes"] = notes
        if pass_id:
            row["last_pass_reviewed"] = pass_id
        updated = True
    rows.append(row)

if not updated:
    row = {field: "" for field in fields}
    row["addr_hex"] = addr_hex
    row["status"] = status
    row["proposed_symbol"] = proposed_symbol
    row["notes"] = notes
    row["last_pass_reviewed"] = pass_id
    row["active"] = "yes"
    rows.append(row)

review_path.parent.mkdir(parents=True, exist_ok=True)
with review_path.open("w", encoding="utf-8", newline="") as f:
    writer = csv.DictWriter(f, fieldnames=fields, lineterminator='\n')
    writer.writeheader()
    writer.writerows(rows)

print(f"updated {review_path} -> {addr_hex} status={status}")
PY
