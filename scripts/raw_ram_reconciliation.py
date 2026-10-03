"""Read-only comparison with the raw-RAM rows computed by next-pass/closeout."""

import csv
import io
from pathlib import Path
import re


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


def render_review(rows, fieldnames):
    output = io.StringIO(newline="")
    writer = csv.DictWriter(output, fieldnames=fieldnames, lineterminator="\n")
    writer.writeheader()
    for row in rows:
        writer.writerow({field: row.get(field, "") for field in fieldnames})
    return output.getvalue().encode("utf-8")


def compare(path, actual, expected, fieldnames):
    path = Path(path)
    before_bytes = path.read_bytes() if path.exists() else None
    expected_bytes = render_review(expected, fieldnames)
    # An absent queue with no candidates remains optional.
    bytes_changed = before_bytes != expected_bytes if before_bytes is not None else bool(expected)
    serialization_changed = (bytes_changed and before_bytes is not None
                             and before_bytes != render_review(actual.values(), fieldnames))
    changes = []
    for row in expected:
        address = row["addr_hex"].strip().lower()
        before = actual.get(address)
        fields = {
            field: {"actual": before[field] if before else None, "expected": row[field]}
            for field in fieldnames
            if before is None or before[field] != row[field]
        }
        if fields:
            changes.append({"addr_hex": address, "missing_row": before is None, "fields": fields})
    return {"check": "raw_ram_reconciliation", "ledger": str(path),
            "status": "stale" if bytes_changed else "pass", "checked_rows": len(expected),
            "bytes_changed": bytes_changed, "serialization_changed": serialization_changed,
            "changed_rows": len(changes), "changes": changes}
