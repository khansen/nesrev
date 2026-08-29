#!/usr/bin/env python3
"""Build paired low/high .DB pointer-table inventory from xasm xref v2."""

from __future__ import annotations

import csv
import sys
from pathlib import Path
from typing import Any, TextIO

from data_directive_xref import ContractError, load_xref, pointer_metadata, require
from embedded_pointer_targets import canonical_expr, db_records, record_owner


FIELDNAMES = (
    "lo_source",
    "hi_source",
    "entry",
    "target_label",
    "target_type",
    "confidence",
    "notes",
)

SPLIT_POINTER_SUFFIXES = (
    ("PtrLoTable", "PtrHiTable"),
    ("PointerLoTable", "PointerHiTable"),
    ("PtrLowTable", "PtrHighTable"),
    ("LoPtrTable", "HiPtrTable"),
    ("LowPtrTable", "HighPtrTable"),
)


def split_counterpart(label: str, from_lo: bool) -> str:
    for lo_suffix, hi_suffix in SPLIT_POINTER_SUFFIXES:
        source, dest = (lo_suffix, hi_suffix) if from_lo else (hi_suffix, lo_suffix)
        if label.endswith(source):
            return f"{label[:-len(source)]}{dest}"
    return ""


def is_split_table_label(label: str) -> bool:
    return bool(split_counterpart(label, True) or split_counterpart(label, False))


def table_records(
    payload: dict[str, Any],
) -> dict[str, list[tuple[int, dict[str, Any]]]]:
    symbols = payload.get("symbols")
    if not isinstance(symbols, list):
        raise ContractError("xref version 2 is missing symbols")

    definitions: dict[str, tuple[str, int, int]] = {}
    ordered_definitions: list[tuple[str, int, int]] = []
    for symbol_index, symbol in enumerate(symbols):
        if not isinstance(symbol, dict):
            raise ContractError(f"symbols[{symbol_index}] must be an object")
        if symbol.get("scope") != "global" or symbol.get("kind") != "label":
            continue
        name = symbol.get("name")
        definition = symbol.get("definition")
        if not isinstance(name, str) or not isinstance(definition, dict):
            continue
        file_name = definition.get("file")
        line = definition.get("line")
        output_offset = definition.get("output_offset")
        if (
            isinstance(file_name, str)
            and isinstance(line, int)
            and not isinstance(line, bool)
            and isinstance(output_offset, int)
            and not isinstance(output_offset, bool)
        ):
            definitions[name] = (file_name, line, output_offset)
            ordered_definitions.append((file_name, line, output_offset))

    tables: dict[str, list[tuple[int, dict[str, Any]]]] = {}
    for index, record in db_records(payload):
        owner = record_owner(record, index)
        if owner is None or not is_split_table_label(owner):
            continue
        require(record, "owner_item_index", int, index)
        tables.setdefault(owner, []).append((index, record))

    for owner, records in tables.items():
        records.sort(key=lambda item: require(item[1], "owner_item_index", int, item[0]))
        indexes = [require(record, "owner_item_index", int, index) for index, record in records]
        if indexes != list(range(len(indexes))):
            raise ContractError(
                f"{owner}: split pointer table contains an operand without a symbolic xref record"
            )
        owner_definition = definitions.get(owner)
        if owner_definition is None:
            raise ContractError(f"{owner}: split pointer table owner definition is missing")
        owner_file, owner_line, owner_offset = owner_definition
        later_definitions = [
            (line, output_offset)
            for file_name, line, output_offset in ordered_definitions
            if file_name == owner_file and line > owner_line
        ]
        if later_definitions:
            _, table_end = min(later_definitions)
            if table_end >= owner_offset and table_end - owner_offset != len(records):
                raise ContractError(
                    f"{owner}: split pointer table body contains bytes without symbolic "
                    "xref records"
                )
    return tables


def inventory_rows(
    payload: dict[str, Any],
) -> tuple[list[dict[str, object]], list[str]]:
    tables = table_records(payload)
    rows: list[dict[str, object]] = []
    errors: list[str] = []

    for owner in sorted(tables, key=lambda name: tables[name][0][0]):
        lo_label = owner
        hi_label = split_counterpart(lo_label, True)
        if not hi_label:
            continue
        hi_records = tables.get(hi_label)
        if hi_records is None:
            continue
        lo_records = tables[lo_label]
        if len(lo_records) != len(hi_records):
            errors.append(
                f"{lo_label}/{hi_label}: split pointer table entry count mismatch "
                f"({len(lo_records)} low bytes, {len(hi_records)} high bytes)"
            )
            continue

        for entry, ((lo_index, lo_record), (hi_index, hi_record)) in enumerate(
            zip(lo_records, hi_records)
        ):
            lo_projection = lo_record.get("target_projection")
            if lo_projection != "low":
                errors.append(
                    f"{lo_label}: entry {entry} must use symbolic <Target; "
                    f"got {require(lo_record, 'expression', str, lo_index)!r}"
                )
                continue
            hi_projection = hi_record.get("target_projection")
            if hi_projection != "high":
                errors.append(
                    f"{hi_label}: entry {entry} must use symbolic >Target; "
                    f"got {require(hi_record, 'expression', str, hi_index)!r}"
                )
                continue

            lo_expr = canonical_expr(require(lo_record, "expression", str, lo_index))
            hi_expr = canonical_expr(require(hi_record, "expression", str, hi_index))
            if lo_expr != hi_expr:
                errors.append(
                    f"{lo_label}/{hi_label}: entry {entry} target mismatch: "
                    f"<{lo_expr} vs >{hi_expr}"
                )
                continue

            lo_kind = lo_record.get("target_kind", "unknown")
            hi_kind = hi_record.get("target_kind", "unknown")
            if lo_kind != hi_kind:
                errors.append(
                    f"{lo_label}/{hi_label}: entry {entry} target kind mismatch: "
                    f"{lo_kind!r} vs {hi_kind!r}"
                )
                continue
            pointer_kind, confidence, notes = pointer_metadata(
                lo_record,
                lo_index,
                "auto-extracted from .DB <label,>label pair (target kind unresolved)",
            )
            rows.append(
                {
                    "lo_source": lo_label,
                    "hi_source": hi_label,
                    "entry": entry,
                    "target_label": lo_expr,
                    "target_type": pointer_kind,
                    "confidence": confidence,
                    "notes": f"{notes}; split low/high table pair",
                }
            )

    return rows, errors


def write_inventory(rows: list[dict[str, object]], output: TextIO) -> None:
    writer = csv.DictWriter(output, fieldnames=FIELDNAMES, lineterminator="\n")
    writer.writeheader()
    writer.writerows(rows)


def main() -> int:
    if len(sys.argv) not in (2, 3):
        print(f"usage: {sys.argv[0]} <xref_v2_json> [out_csv]", file=sys.stderr)
        return 64

    try:
        payload = load_xref(Path(sys.argv[1]))
        rows, errors = inventory_rows(payload)
        if errors:
            for error in errors:
                print(error, file=sys.stderr)
            return 68
        if len(sys.argv) == 3:
            with Path(sys.argv[2]).open(
                "w", encoding="utf-8", newline=""
            ) as output:
                write_inventory(rows, output)
        else:
            write_inventory(rows, sys.stdout)
    except (ContractError, OSError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 65
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
