"""Read-only comparison with the raw-RAM rows computed by next-pass/closeout."""

import csv
import io
from pathlib import Path

from raw_ram_review import read_review


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
