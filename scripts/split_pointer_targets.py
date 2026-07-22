#!/usr/bin/env python3
"""Emit symbolic pointer targets stored in split low/high .DB tables.

This covers the common NES layout where one table stores `<Target` bytes and a
sibling table stores `>Target` bytes.  `pointer_targets.csv` owns `.DW` tables
and `embedded_pointer_targets.csv` owns adjacent `<label,>label` record fields;
this registry makes the split-table shape visible to inventory checks too.
"""

from __future__ import annotations

import csv
import sys
from dataclasses import dataclass
from pathlib import Path

from embedded_pointer_targets import (
    LABEL_RE,
    build_label_kinds,
    canonical_expr,
    db_payload,
    split_operands,
    strip_comment,
    strip_label,
    target_type,
)


FIELDNAMES = [
    "lo_source",
    "hi_source",
    "entry",
    "target_label",
    "target_type",
    "confidence",
    "notes",
]

SPLIT_POINTER_SUFFIXES = (
    ("PtrLoTable", "PtrHiTable"),
    ("PointerLoTable", "PointerHiTable"),
    ("PtrLowTable", "PtrHighTable"),
    ("LoPtrTable", "HiPtrTable"),
    ("LowPtrTable", "HighPtrTable"),
)


@dataclass
class TableBody:
    label: str
    operands: list[tuple[int, str]]


def global_label(line: str) -> str:
    match = LABEL_RE.match(line)
    if not match or match.group(1):
        return ""
    return match.group(2)


def split_counterpart(label: str, from_lo: bool) -> str:
    for lo_suffix, hi_suffix in SPLIT_POINTER_SUFFIXES:
        source, dest = (lo_suffix, hi_suffix) if from_lo else (hi_suffix, lo_suffix)
        if label.endswith(source):
            return f"{label[:-len(source)]}{dest}"
    return ""


def is_split_table_label(label: str) -> bool:
    return bool(split_counterpart(label, True) or split_counterpart(label, False))


def meaningful_body_text(line: str) -> str:
    return strip_comment(strip_label(line)).strip()


def collect_candidate_tables(lines: list[str]) -> tuple[dict[str, TableBody], list[str]]:
    tables: dict[str, TableBody] = {}
    errors: list[str] = []
    current: TableBody | None = None

    for line_no, line in enumerate(lines, start=1):
        label = global_label(line)
        if label:
            current = TableBody(label=label, operands=[]) if is_split_table_label(label) else None
            if current:
                tables[label] = current

        if not current:
            continue

        text = meaningful_body_text(line)
        if not text:
            continue

        payload = db_payload(line)
        if payload:
            operands = split_operands(payload)
            for operand in operands:
                operand = operand.strip()
                if not operand:
                    errors.append(f"{current.label}:{line_no}: empty .DB operand in split pointer table")
                else:
                    current.operands.append((line_no, operand))
            continue

        errors.append(
            f"{current.label}:{line_no}: split pointer table body contains non-.DB content: {text}"
        )

    return tables, errors


def emit_rows(lines: list[str]) -> tuple[list[dict[str, object]], list[str]]:
    label_kinds = build_label_kinds(lines)
    tables, errors = collect_candidate_tables(lines)
    rows: list[dict[str, object]] = []

    for lo_label, lo_table in tables.items():
        hi_label = split_counterpart(lo_label, True)
        if not hi_label:
            continue
        hi_table = tables.get(hi_label)
        if not hi_table:
            continue

        if len(lo_table.operands) != len(hi_table.operands):
            errors.append(
                f"{lo_label}/{hi_label}: split pointer table entry count mismatch "
                f"({len(lo_table.operands)} low bytes, {len(hi_table.operands)} high bytes)"
            )
            continue

        for entry, ((lo_line, lo_operand), (hi_line, hi_operand)) in enumerate(
            zip(lo_table.operands, hi_table.operands)
        ):
            if not lo_operand.startswith("<"):
                errors.append(
                    f"{lo_label}:{lo_line}: entry {entry} must use symbolic <Target; got {lo_operand!r}"
                )
                continue
            if not hi_operand.startswith(">"):
                errors.append(
                    f"{hi_label}:{hi_line}: entry {entry} must use symbolic >Target; got {hi_operand!r}"
                )
                continue

            lo_expr = canonical_expr(lo_operand)
            hi_expr = canonical_expr(hi_operand)
            if lo_expr != hi_expr:
                errors.append(
                    f"{lo_label}/{hi_label}: entry {entry} target mismatch: "
                    f"<{lo_expr} vs >{hi_expr}"
                )
                continue

            pointer_kind, confidence, notes = target_type(lo_expr, label_kinds)
            rows.append({
                "lo_source": lo_label,
                "hi_source": hi_label,
                "entry": entry,
                "target_label": lo_expr,
                "target_type": pointer_kind,
                "confidence": confidence,
                "notes": f"{notes}; split low/high table pair",
            })

    return rows, errors


def write_csv(rows: list[dict[str, object]], out_path: str | None) -> None:
    out = open(out_path, "w", newline="", encoding="utf-8") if out_path else sys.stdout
    close_out = out is not sys.stdout
    try:
        writer = csv.DictWriter(out, fieldnames=FIELDNAMES, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)
    finally:
        if close_out:
            out.close()


def main() -> int:
    if len(sys.argv) not in (2, 3):
        print("usage: split_pointer_targets.py <asm_file> [out_csv]", file=sys.stderr)
        return 64

    asm_path = Path(sys.argv[1])
    if not asm_path.is_file():
        print(f"error: asm file not found: {asm_path}", file=sys.stderr)
        return 65

    lines = asm_path.read_text(encoding="utf-8").splitlines()
    rows, errors = emit_rows(lines)
    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 68

    write_csv(rows, sys.argv[2] if len(sys.argv) == 3 else None)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
