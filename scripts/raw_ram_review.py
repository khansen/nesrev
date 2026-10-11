"""Address contract and lossless admission of the authored raw-RAM queue."""

import csv
from pathlib import Path
import re


FIELDS = [
    "addr_hex", "status", "proposed_symbol", "notes", "last_pass_reviewed",
    "active", "operand_count", "distinct_owner_count", "read_count",
    "write_count", "top_readers", "top_writers",
]


def parse_address(value, *, ledger=False):
    text = value.strip().lower()
    pattern = r"0x([0-9a-f]{4})" if ledger else r"(?:0x|\$)?([0-9a-f]{1,4})"
    match = re.fullmatch(pattern, text)
    if not match:
        raise ValueError(f"invalid raw-RAM address {value!r}")
    address = int(match.group(1), 16)
    if not (0 <= address <= 0x1FFF or 0x6000 <= address <= 0x7FFF):
        raise ValueError(
            f"raw-RAM address {value!r} is outside supported RAM windows "
            "0x0000-0x1fff and 0x6000-0x7fff"
        )
    # Keep CPU operand addresses distinct, including aliases of internal RAM.
    return f"0x{address:04x}"


def read_review(path, fields=FIELDS, *, require_field_order=False):
    path = Path(path)
    if not path.exists():
        return {}
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, strict=True)
        if (reader.fieldnames is None or len(reader.fieldnames) != len(fields)
                or set(reader.fieldnames) != set(fields)
                or (require_field_order and reader.fieldnames != fields)):
            raise ValueError(f"{path}: invalid raw-RAM ledger columns")
        rows = {}
        for number, row in enumerate(reader, 2):
            if None in row or any(value is None for value in row.values()):
                raise ValueError(f"{path}:{number}: invalid raw-RAM row width")
            try:
                address = parse_address(row["addr_hex"], ledger=True)
            except ValueError as exc:
                raise ValueError(f"{path}:{number}: {exc}") from exc
            if address in rows:
                raise ValueError(f"{path}:{number}: duplicate raw-RAM address {address!r}")
            rows[address] = row
        return rows
