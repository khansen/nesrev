#!/usr/bin/env python3
"""One-line advisory summary of the data-format target ledger.

Used by project-maturity-summary so the families that block maturity are
visible between passes, not only when the terminal maturity gate runs.
"""

from __future__ import annotations

import csv
import sys
from collections import Counter
from pathlib import Path

# Dispositions that still block gold closeout.
OPEN = ("not_yet_reviewed", "queued_static_pass")


def main(argv: list[str]) -> int:
    if len(argv) != 1:
        print("usage: data_format_targets_summary.py <data_format_targets.csv>", file=sys.stderr)
        return 64
    path = Path(argv[0])
    if not path.is_file():
        print(f"- DEFECT: required data-format ledger missing: {path}")
        return 0

    with path.open(newline="", encoding="utf-8") as fh:
        counts = Counter((row.get("disposition") or "").strip() for row in csv.DictReader(fh))

    total = sum(counts.values())
    detail = ", ".join(f"{k}={v}" for k, v in sorted(counts.items()) if k)
    print(f"- data-format families: {total} rows ({detail or 'none'})")

    open_rows = sum(counts.get(k, 0) for k in OPEN)
    if open_rows:
        print(
            f"  {open_rows} family/families still block maturity "
            f"({' or '.join(OPEN)})"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
