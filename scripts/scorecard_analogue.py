#!/usr/bin/env python3
"""Print and validate the pass-1 prior-project analogue from a scorecard."""

from __future__ import annotations

import re
import sys
from pathlib import Path


ANALOGUE_RE = re.compile(
    r"\bAnalogue:\s*([a-z0-9_-]+)\s*\([^)]+\S\)",
    flags=re.IGNORECASE,
)


def error(message: str) -> None:
    print(f"scorecard_analogue: {message}", file=sys.stderr)


def main(argv: list[str]) -> int:
    optional = "--optional" in argv
    paths = [arg for arg in argv if arg != "--optional"]
    if len(paths) != 1 or len(paths) != len(argv) - int(optional):
        error("usage: scorecard_analogue.py <PROGRESS_SCORECARD.md> [--optional]")
        return 64

    path = Path(paths[0])
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeError) as exc:
        error(f"failed to read {path}: {exc}")
        return 65

    header: list[str] | None = None
    pass_one_rows: list[tuple[int, list[str]]] = []
    for lineno, raw in enumerate(lines, start=1):
        line = raw.strip()
        if not (line.startswith("|") and line.endswith("|")):
            continue
        cells = [cell.strip() for cell in line.strip("|").split("|")]
        if cells and cells[0] == "pass_id":
            header = cells
        elif cells and cells[0] == "1":
            pass_one_rows.append((lineno, cells))

    if not pass_one_rows:
        return 0
    if header is None or "notes" not in header:
        error(f"invalid scorecard header in {path}: missing notes column")
        return 1
    if len(pass_one_rows) != 1:
        row_lines = ", ".join(str(lineno) for lineno, _ in pass_one_rows)
        error(f"invalid pass-1 scorecard rows in {path}: found at lines {row_lines}")
        return 1

    lineno, cells = pass_one_rows[0]
    if len(cells) != len(header):
        error(f"invalid pass-1 scorecard row at {path}:{lineno}: column count mismatch")
        return 1

    notes = cells[header.index("notes")]
    analogue = ANALOGUE_RE.search(notes)
    if analogue is None:
        if optional:
            return 0
        error(
            f"{path}:{lineno}: pass 1 notes must record "
            "'Analogue: <project_slug|none> "
            "(<applied pattern or reason it did not fit>)'"
        )
        return 1

    print(analogue.group(1).lower())
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
