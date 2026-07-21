#!/usr/bin/env python3
"""Reject raw '|' in PROGRESS_SCORECARD.md table cells.

The scorecard is a GitHub-flavored Markdown table, so '|' is the column
delimiter. A pipe inside a cell (e.g. a codeentries reference written as
`bank|$addr`) adds a phantom column: it breaks the rendered table and the
row parsers used by the pass lifecycle. The scorecard is a ledger, not the
recovery-control file -- reference codeentries in prose ('codeentries bank 1
$A64C'), never with a raw pipe.

Detection is structural: a data row whose cell count differs from the header's
contains a stray delimiter. Fails with a clear message and the offending line.
"""
import sys
from pathlib import Path


def main():
    if len(sys.argv) != 2:
        sys.stderr.write("usage: scorecard_cell_check.py <progress_scorecard.md>\n")
        raise SystemExit(64)
    path = Path(sys.argv[1])
    if not path.is_file():
        sys.stderr.write(f"error: scorecard not found: {path}\n")
        raise SystemExit(65)

    header_n = None
    errors = []
    for lineno, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        line = raw.strip()
        if not (line.startswith("|") and line.endswith("|")):
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        if not cells:
            continue
        if cells[0] == "pass_id":
            header_n = len(cells)
            continue
        if header_n is None:
            continue
        if all(set(c) <= set("-: ") for c in cells):  # separator row
            continue
        if len(cells) != header_n:
            errors.append(
                f"{path}:{lineno}: scorecard row has {len(cells)} cells, expected "
                f"{header_n}; a raw '|' is not allowed in scorecard cells "
                "(use prose, e.g. 'codeentries bank 1 $A64C')"
            )

    if errors:
        for e in errors:
            print(e, file=sys.stderr)
        raise SystemExit(1)
    print("OK: scorecard cells contain no raw pipes")


if __name__ == "__main__":
    main()
