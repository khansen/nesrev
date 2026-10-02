"""Read-only comparison with the raw-RAM rows computed by next-pass/closeout."""

import csv
from pathlib import Path
import re


FACT_FIELDS = (
    "active", "operand_count", "distinct_owner_count", "read_count",
    "write_count", "top_readers", "top_writers",
)


def read_review(path, fields):
    path = Path(path)
    if not path.exists():
        return {}
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, strict=True)
        if (reader.fieldnames is None or len(reader.fieldnames) != len(fields)
                or set(reader.fieldnames) != set(fields)):
            raise ValueError(f"{path}: invalid raw-RAM ledger columns")
        rows = {}
        for number, row in enumerate(reader, 2):
            if None in row or any(value is None for value in row.values()):
                raise ValueError(f"{path}:{number}: invalid raw-RAM row width")
            address = row["addr_hex"].strip().lower()
            if not re.fullmatch(r"0x[0-9a-f]{4}", address) or address in rows:
                raise ValueError(f"{path}:{number}: invalid or duplicate address {address!r}")
            rows[address] = row
        return rows


def compare(path, actual, expected):
    changes = []
    for row in expected:
        address = row["addr_hex"].strip().lower()
        before = actual.get(address)
        fields = {
            field: {"actual": before[field] if before else None, "expected": row[field]}
            for field in FACT_FIELDS
            if before is None or before[field] != row[field]
        }
        if fields:
            changes.append({"addr_hex": address, "missing_row": before is None, "fields": fields})
    return {"check": "raw_ram_reconciliation", "ledger": str(path),
            "status": "stale" if changes else "pass", "checked_rows": len(expected),
            "changed_rows": len(changes), "changes": changes}
