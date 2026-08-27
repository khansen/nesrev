#!/usr/bin/env python3
"""Report project prose that repeats the canonical four-byte OAM field order.

ASM comments and live project Markdown should cite ``OAM_FIELD_*`` (and, in
Markdown, the canonical ASM_STYLE section) instead of restating the NES-wide
``Y/tile/attributes/X`` order.  Project-specific record shapes remain valid.
Review archives and generated inventory snapshots are immutable provenance and
are deliberately excluded.

Report mode exits zero for process-check use.  ``--strict`` exits 69 when a
candidate remains.
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path


USAGE = "usage: oam_standard_prose_check.py <asm_file> <project_root> [--strict]"
SKIP_DIRS = {"inventory", "reviews"}
STANDARD_ORDER_RE = re.compile(
    r"[\[(]\s*y\s*,\s*tile\s*,\s*"
    r"(?:attr|attrs|attrib|attribs|attribute|attributes)\s*,\s*x\s*[\])]",
    re.IGNORECASE,
)


@dataclass(frozen=True)
class Finding:
    path: Path
    line: int
    text: str


def markdown_files(project_root: Path) -> list[Path]:
    docs_root = project_root / "docs"
    if not docs_root.is_dir():
        return []
    files: list[Path] = []
    for path in docs_root.rglob("*.md"):
        relative_parts = set(path.relative_to(docs_root).parts[:-1])
        if relative_parts & SKIP_DIRS:
            continue
        files.append(path)
    return sorted(files)


def scan_asm(path: Path) -> list[Finding]:
    findings: list[Finding] = []
    for line_number, raw in enumerate(
        path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        if ";" not in raw:
            continue
        comment = raw.split(";", 1)[1]
        if STANDARD_ORDER_RE.search(comment):
            findings.append(Finding(path, line_number, raw.strip()))
    return findings


def scan_markdown(path: Path) -> list[Finding]:
    findings: list[Finding] = []
    for line_number, raw in enumerate(
        path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        if STANDARD_ORDER_RE.search(raw):
            findings.append(Finding(path, line_number, raw.strip()))
    return findings


def main(argv: list[str]) -> int:
    strict = False
    args: list[str] = []
    for arg in argv:
        if arg == "--strict":
            strict = True
        elif arg.startswith("-"):
            print(USAGE, file=sys.stderr)
            return 64
        else:
            args.append(arg)
    if len(args) != 2:
        print(USAGE, file=sys.stderr)
        return 64

    asm_path = Path(args[0])
    project_root = Path(args[1])
    if not asm_path.is_file() or not project_root.is_dir():
        print(
            f"error: missing asm file or project root: {asm_path}, {project_root}",
            file=sys.stderr,
        )
        return 65

    try:
        findings = scan_asm(asm_path)
        for path in markdown_files(project_root):
            findings.extend(scan_markdown(path))
    except (OSError, UnicodeError) as exc:
        print(f"error: cannot scan project OAM prose: {exc}", file=sys.stderr)
        return 65

    findings.sort(key=lambda finding: (str(finding.path), finding.line))
    for finding in findings:
        print(
            f"advisory: {finding.path}:{finding.line}: repeats the standard OAM "
            "field order; cite OAM_FIELD_* and retain only project-specific "
            f"encoding or invariants: {finding.text}",
            file=sys.stderr,
        )
    print(f"[oam-standard-prose] candidates={len(findings)}")
    if strict and findings:
        print(
            f"FAIL: {len(findings)} repeated standard OAM field-order line(s) remain",
            file=sys.stderr,
        )
        return 69
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
