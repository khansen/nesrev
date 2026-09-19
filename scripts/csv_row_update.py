#!/usr/bin/env python3
"""Update one or more fields on an existing CSV ledger row, safely.

A pass that edits `data_blob_dispositions.csv`, `data_format_targets.csv`, or
any similar comma-delimited ledger by hand — reading it as raw text, matching
a row by regex, splicing in new field text, and rejoining lines — has no
defense against a field's own prose containing a bare comma. That comma
silently becomes an extra column, and the corruption is invisible until a
much later checker run reports an opaque "too many CSV columns" on some
unrelated row number.

Going through `csv.DictReader`/`csv.DictWriter` instead makes the bug
impossible: the writer quotes any field containing the delimiter, a quote
character, or a newline unconditionally, because that is what the CSV module
already does by default. The fix is routing every ledger edit through the
module instead of through text splicing, not remembering to quote by hand.

Exit status is 0 on a successful update, 1 if the match count was not
exactly one (unless `--allow-multiple` is given), 2 on a usage/read error.
"""

from __future__ import annotations

import argparse
import csv
import io
import os
import sys
import tempfile
from pathlib import Path


def parse_kv(pairs: list[str], flag: str) -> dict[str, str]:
    out: dict[str, str] = {}
    for raw in pairs:
        if "=" not in raw:
            raise SystemExit(f"csv_row_update: {flag} expects field=value, got {raw!r}")
        field, value = raw.split("=", 1)
        field = field.strip()
        if not field:
            raise SystemExit(f"csv_row_update: {flag} field name must not be empty")
        out[field] = value
    return out


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("ledger", type=Path)
    ap.add_argument(
        "--where",
        action="append",
        default=[],
        required=True,
        help="field=value filter selecting the row(s) to update; repeat to AND "
        "several filters together (e.g. --where label=Foo --where disposition=queued_static_pass)",
    )
    ap.add_argument(
        "--set",
        action="append",
        default=[],
        required=True,
        help="field=value to write into every matched row; repeat for multiple fields",
    )
    ap.add_argument(
        "--allow-multiple",
        action="store_true",
        help="update every matching row instead of requiring exactly one match",
    )
    args = ap.parse_args(argv)

    where = parse_kv(args.where, "--where")
    updates = parse_kv(args.set, "--set")

    if not args.ledger.is_file():
        print(f"csv_row_update: no such file: {args.ledger}", file=sys.stderr)
        return 2

    with args.ledger.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        fieldnames = reader.fieldnames
        if not fieldnames:
            print(f"csv_row_update: {args.ledger}: no header row", file=sys.stderr)
            return 2
        rows = list(reader)

    # A row with more fields than the header (an unquoted comma split it, or
    # a prior hand-edit corrupted it) carries the extras under DictReader's
    # `None` key. DictWriter.writerow raises ValueError on that key later,
    # by which point some good rows may already be written to the truncated
    # target file. Refuse before any output exists, so this tool never turns
    # a pre-existing corruption it did not cause into a partial-file loss.
    bad_rows = [
        (line_no, row) for line_no, row in enumerate(rows, start=2) if None in row
    ]
    if bad_rows:
        line_no, row = bad_rows[0]
        known = {k: v for k, v in row.items() if k is not None}
        print(
            f"csv_row_update: {args.ledger}:{line_no}: row already has more fields "
            f"than the header ({len(fieldnames)}); refusing to write until it is "
            f"fixed. Parsed fields: {known!r}; extra: {row[None]!r}",
            file=sys.stderr,
        )
        return 2

    unknown_where = set(where) - set(fieldnames)
    unknown_set = set(updates) - set(fieldnames)
    if unknown_where or unknown_set:
        print(
            f"csv_row_update: {args.ledger}: unknown field(s) "
            f"{sorted(unknown_where | unknown_set)}; header is {fieldnames}",
            file=sys.stderr,
        )
        return 2

    matched = [
        row for row in rows
        if all(row.get(field, "") == value for field, value in where.items())
    ]
    if not matched:
        print(f"csv_row_update: {args.ledger}: no row matches {where}", file=sys.stderr)
        return 1
    if len(matched) > 1 and not args.allow_multiple:
        print(
            f"csv_row_update: {args.ledger}: {len(matched)} rows match {where}; "
            "pass --allow-multiple if that is intended",
            file=sys.stderr,
        )
        return 1

    for row in matched:
        row.update(updates)

    # Render fully in memory, then publish with a rename. Writing straight
    # into the ledger truncates it first; any failure partway through
    # writerows (a row this process itself now mis-shapes, a disk-full, a
    # permission error) would otherwise leave a half-written, data-losing
    # file in the original's place instead of the original being untouched.
    buffer = io.StringIO()
    writer = csv.DictWriter(buffer, fieldnames=fieldnames, lineterminator="\n")
    writer.writeheader()
    writer.writerows(rows)

    fd, tmp_name = tempfile.mkstemp(
        dir=args.ledger.parent, prefix=f".{args.ledger.name}.", suffix=".tmp"
    )
    try:
        with os.fdopen(fd, "w", encoding="utf-8", newline="") as handle:
            handle.write(buffer.getvalue())
        os.replace(tmp_name, args.ledger)
    except BaseException:
        Path(tmp_name).unlink(missing_ok=True)
        raise

    print(f"csv_row_update: updated {len(matched)} row(s) in {args.ledger}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
