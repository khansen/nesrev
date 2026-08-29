#!/usr/bin/env python3
"""Build adjacent low/high .DB pointer inventory from xasm xref version 2."""

from __future__ import annotations

import csv
import sys
from pathlib import Path
from typing import Any, TextIO

from data_directive_xref import ContractError, load_xref, pointer_metadata, require


FIELDNAMES = (
    "source",
    "entry",
    "target_label",
    "target_type",
    "confidence",
    "notes",
)


def canonical_expr(expression: str) -> str:
    expr = expression.strip()
    if expr.startswith("<") or expr.startswith(">"):
        expr = expr[1:].strip()
    while expr.startswith("(") and expr.endswith(")"):
        inner = expr[1:-1].strip()
        if not inner:
            break
        expr = inner
    return expr


def db_records(payload: dict[str, Any]) -> list[tuple[int, dict[str, Any]]]:
    records: list[tuple[int, dict[str, Any]]] = []
    for index, raw_record in enumerate(payload["data_directive_references"]):
        if not isinstance(raw_record, dict):
            raise ContractError(f"data_directive_references[{index}] must be an object")
        directive = require(raw_record, "directive", str, index)
        if directive != ".DB":
            continue
        width = require(raw_record, "width_bytes", int, index)
        if width != 1:
            raise ContractError(
                f"data_directive_references[{index}] has .DB width_bytes={width}, expected 1"
            )
        records.append((index, raw_record))
    return records


def record_owner(record: dict[str, Any], index: int) -> str | None:
    owner = record.get("owner_symbol")
    if owner is None:
        return None
    if not isinstance(owner, str) or not owner:
        raise ContractError(
            f"data_directive_references[{index}].owner_symbol must be a non-empty string"
        )
    return owner


def projected_expr(
    record: dict[str, Any], index: int, expected_projection: str
) -> str:
    projection = require(record, "target_projection", str, index)
    if projection != expected_projection:
        raise ContractError(
            f"data_directive_references[{index}].target_projection must be "
            f"{expected_projection!r}"
        )
    expression = require(record, "expression", str, index)
    prefix = "<" if projection == "low" else ">"
    if not expression.lstrip().startswith(prefix):
        raise ContractError(
            f"data_directive_references[{index}].expression must preserve its "
            f"{projection} projection"
        )
    result = canonical_expr(expression)
    if not result:
        raise ContractError(
            f"data_directive_references[{index}].expression must not be empty"
        )
    return result


def inventory_rows(payload: dict[str, Any]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    entry_by_owner: dict[str, int] = {}
    records = db_records(payload)

    position = 0
    while position + 1 < len(records):
        lo_index, lo_record = records[position]
        hi_index, hi_record = records[position + 1]
        if lo_record.get("target_projection") != "low" or hi_record.get(
            "target_projection"
        ) != "high":
            position += 1
            continue

        lo_owner = record_owner(lo_record, lo_index)
        hi_owner = record_owner(hi_record, hi_index)
        # File/line adjacency plus consecutive owner indexes already implies
        # one owner in ordinary source. Keep the explicit check for macro
        # expansions whose operands can share an invocation location while
        # retaining distinct lexical provenance.
        if lo_owner is None or hi_owner is None or lo_owner != hi_owner:
            position += 1
            continue

        lo_file = require(lo_record, "file", str, lo_index)
        hi_file = require(hi_record, "file", str, hi_index)
        lo_line = require(lo_record, "line", int, lo_index)
        hi_line = require(hi_record, "line", int, hi_index)
        lo_operand = require(lo_record, "operand_index", int, lo_index)
        hi_operand = require(hi_record, "operand_index", int, hi_index)
        lo_owner_item = require(lo_record, "owner_item_index", int, lo_index)
        hi_owner_item = require(hi_record, "owner_item_index", int, hi_index)
        if not (
            lo_file == hi_file
            and lo_line == hi_line
            and hi_operand == lo_operand + 1
            and hi_owner_item == lo_owner_item + 1
        ):
            position += 1
            continue

        lo_expr = projected_expr(lo_record, lo_index, "low")
        hi_expr = projected_expr(hi_record, hi_index, "high")
        if lo_expr != hi_expr:
            position += 1
            continue

        lo_kind = lo_record.get("target_kind", "unknown")
        hi_kind = hi_record.get("target_kind", "unknown")
        if lo_kind != hi_kind:
            raise ContractError(
                f"data_directive_references[{lo_index}] and [{hi_index}] "
                "disagree on target_kind"
            )
        pointer_kind, confidence, notes = pointer_metadata(
            lo_record,
            lo_index,
            "auto-extracted from .DB <label,>label pair (target kind unresolved)",
        )
        entry = entry_by_owner.get(lo_owner, 0)
        rows.append(
            {
                "source": lo_owner,
                "entry": entry,
                "target_label": lo_expr,
                "target_type": pointer_kind,
                "confidence": confidence,
                "notes": notes,
            }
        )
        entry_by_owner[lo_owner] = entry + 1
        position += 2

    return rows


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
        rows = inventory_rows(payload)
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
