#!/usr/bin/env python3
"""Build the .DW pointer inventory from xasm JSON xref version 2."""

from __future__ import annotations

import csv
import json
import sys
from pathlib import Path
from typing import Any, TextIO


HEADER = ("source", "entry", "target_label", "target_type", "confidence", "notes")
CPU_VECTOR_ADDRESSES = {"0XFFFA", "0XFFFC", "0XFFFE"}
TARGET_TYPES = {
    "code": (
        "code_pointer",
        "high confidence",
        "auto-classified from target label leading instruction",
    ),
    "data": (
        "data_pointer",
        "high confidence",
        "auto-classified from target label leading data directive",
    ),
    "equate": (
        "data_pointer",
        "high confidence",
        "auto-classified from target label leading data directive",
    ),
    "unknown": (
        "unknown_pointer",
        "inferred",
        "auto-extracted from .DW entry (target kind unresolved)",
    ),
}


class ContractError(ValueError):
    pass


def load_xref(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise ContractError(f"xref file not found: {path}") from exc
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise ContractError(f"could not read xref JSON {path}: {exc}") from exc

    if not isinstance(payload, dict):
        raise ContractError(f"xref root must be an object: {path}")
    version = payload.get("version")
    if version != "2":
        raise ContractError(
            f"xref schema version 2 required, got {version!r}; "
            "use the lockstep xasm data-directive-reference build"
        )
    records = payload.get("data_directive_references")
    if not isinstance(records, list):
        raise ContractError("xref version 2 is missing data_directive_references")
    return payload


def require(record: dict[str, Any], field: str, expected: type, index: int) -> Any:
    value = record.get(field)
    if not isinstance(value, expected) or (expected is int and isinstance(value, bool)):
        raise ContractError(
            f"data_directive_references[{index}].{field} must be "
            f"{expected.__name__}"
        )
    return value


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

        target_kind = raw_record.get("target_kind", "unknown")
        if target_kind not in TARGET_TYPES:
            raise ContractError(
                f"data_directive_references[{index}].target_kind has unsupported value "
                f"{target_kind!r}"
            )
        target_type, confidence, notes = TARGET_TYPES[target_kind]
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
