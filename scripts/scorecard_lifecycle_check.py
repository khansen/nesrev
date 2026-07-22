#!/usr/bin/env python3
"""Validate pass-lifecycle invariants in PROGRESS_SCORECARD.md.

This complements scorecard_cell_check.py. That script protects the Markdown
table shape; this one protects the pass ledger semantics: pass IDs must be
unique and increasing, and completed historical rows must not be left in a
pending gate state. The latest row may be pending while a pass is actively
being finished.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path


REQUIRED_COLUMNS = {"pass_id", "verify", "docs_check"}


def markdown_cells(raw: str) -> list[str] | None:
    line = raw.strip()
    if not (line.startswith("|") and line.endswith("|")):
        return None
    return [cell.strip() for cell in line.strip("|").split("|")]


def is_separator_row(cells: list[str]) -> bool:
    return bool(cells) and all(re.fullmatch(r":?-{3,}:?", cell or "") for cell in cells)


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: scorecard_lifecycle_check.py <progress_scorecard.md>", file=sys.stderr)
        return 64

    path = Path(sys.argv[1])
    if not path.is_file():
        print(f"error: scorecard not found: {path}", file=sys.stderr)
        return 65

    header: list[str] | None = None
    header_index: dict[str, int] = {}
    rows: list[tuple[int, int, list[str]]] = []
    errors: list[str] = []

    for lineno, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        cells = markdown_cells(raw)
        if cells is None:
            continue
        if REQUIRED_COLUMNS.issubset(set(cells)):
            header = cells
            header_index = {name: idx for idx, name in enumerate(header)}
            continue
        if header is None:
            continue
        if is_separator_row(cells):
            continue
        if len(cells) != len(header):
            # scorecard_cell_check.py owns the clearer raw-pipe diagnostic.
            continue
        pass_cell = cells[header_index["pass_id"]]
        if not pass_cell.isdigit():
            continue
        rows.append((lineno, int(pass_cell), cells))

    if header is None:
        errors.append(f"{path}: scorecard table header missing required columns {sorted(REQUIRED_COLUMNS)}")
    if not rows:
        errors.append(f"{path}: no scorecard pass rows found")

    seen: dict[int, int] = {}
    previous_pass: int | None = None
    for lineno, pass_id, _cells in rows:
        if pass_id in seen:
            errors.append(
                f"{path}:{lineno}: duplicate pass_id {pass_id}; first seen at line {seen[pass_id]}"
            )
        else:
            seen[pass_id] = lineno
        if previous_pass is not None and pass_id <= previous_pass:
            errors.append(
                f"{path}:{lineno}: pass_id {pass_id} is out of order after {previous_pass}"
            )
        previous_pass = pass_id

    if rows:
        latest_pass = max(pass_id for _lineno, pass_id, _cells in rows)
        verify_col = header_index["verify"]
        docs_col = header_index["docs_check"]
        for lineno, pass_id, cells in rows:
            if pass_id == latest_pass:
                continue
            for col_name, col_idx in (("verify", verify_col), ("docs_check", docs_col)):
                value = cells[col_idx].strip().lower()
                if value in {"", "pending"}:
                    errors.append(
                        f"{path}:{lineno}: non-latest pass {pass_id} has {col_name}={cells[col_idx]!r}"
                    )

    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1

    print("OK: scorecard pass lifecycle is consistent")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
