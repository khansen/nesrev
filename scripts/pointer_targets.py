#!/usr/bin/env python3
"""Build the .DW pointer inventory from xasm JSON xref version 2."""

from __future__ import annotations

import csv
import sys
from pathlib import Path
from typing import Any, TextIO

from data_directive_xref import ContractError, load_xref, pointer_metadata, require


HEADER = ("source", "entry", "target_label", "target_type", "confidence", "notes")
CPU_VECTOR_ADDRESSES = {"0XFFFA", "0XFFFC", "0XFFFE"}
def inventory_rows(payload: dict[str, Any]) -> list[tuple[Any, ...]]:
    rows: list[tuple[Any, ...]] = []
    records = payload["data_directive_references"]
    for index, raw_record in enumerate(records):
        if not isinstance(raw_record, dict):
            raise ContractError(f"data_directive_references[{index}] must be an object")
        directive = require(raw_record, "directive", str, index)
        if directive != ".DW":
            continue
        width = require(raw_record, "width_bytes", int, index)
        if width != 2:
            raise ContractError(
                f"data_directive_references[{index}] has .DW width_bytes={width}, expected 2"
            )

        use_cpu_address = require(raw_record, "use_cpu_address", str, index).upper()
        if use_cpu_address in CPU_VECTOR_ADDRESSES:
            continue

        # Unowned symbolic words are not pointer-table inventory rows. xasm's
        # lexical owner is the source identity; do not reconstruct one from
        # neighbouring source text.
        owner = raw_record.get("owner_symbol")
        if owner is None:
            continue
        if not isinstance(owner, str) or not owner:
            raise ContractError(
                f"data_directive_references[{index}].owner_symbol must be a non-empty string"
            )

        owner_item_index = require(raw_record, "owner_item_index", int, index)
        expression = require(raw_record, "expression", str, index)
        if not expression:
            raise ContractError(
                f"data_directive_references[{index}].expression must not be empty"
            )

        target_type, confidence, notes = pointer_metadata(
            raw_record,
            index,
            "auto-extracted from .DW entry (target kind unresolved)",
        )
        rows.append(
            (owner, owner_item_index, expression, target_type, confidence, notes)
        )
    return rows


def write_inventory(rows: list[tuple[Any, ...]], output: TextIO) -> None:
    writer = csv.writer(output, lineterminator="\n")
    writer.writerow(HEADER)
    writer.writerows(rows)


def main() -> int:
    if len(sys.argv) not in (2, 3):
        print(f"usage: {sys.argv[0]} <xref_v2_json> [out_csv]", file=sys.stderr)
        return 64

    try:
        payload = load_xref(Path(sys.argv[1]))
        rows = inventory_rows(payload)
        if len(sys.argv) == 3:
            output_path = Path(sys.argv[2])
            with output_path.open("w", encoding="utf-8", newline="") as output:
                write_inventory(rows, output)
        else:
            write_inventory(rows, sys.stdout)
    except (ContractError, OSError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 65
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
