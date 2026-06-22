#!/usr/bin/env python3
"""Advisory check for canonical NES hardware-constant drift.

A project should use the canonical hardware register/bit/field names defined in
``agent_playbook/ASM_STYLE.md#hardware-constants``. This check warns when a
project defines a ``.EQU`` whose name uses a canonical-looking hardware prefix
(``PPUCTRL_``, ``PPUMASK_``, ``PPUSTATUS_``, ``PAD_``, ``OAM_``, ``APU_``,
``JOY1_``, ``JOY2_``) but is not one of the canonical names and is not listed in
the project-local allowlist.

It is advisory by default: it prints ``warn:`` lines and exits 0 so it can be run
from ``project-process-check`` without failing the gate. Pass ``--strict`` to make
it exit non-zero when drift remains (for a future promotion to a hard gate once
existing projects are clean or allowlisted).

Usage:
    check_hardware_constant_drift.py <asm_file> <asm_style_md> <allowlist_file> [--strict]

The allowlist is one symbol per line; ``#`` comments and blank lines are ignored.
A missing allowlist file is treated as empty.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

# Canonical-looking family prefixes. Prefix match only: a project-local symbol
# that merely contains "PPU"/"OAM" in the middle (e.g. ZP_PpuCtrlShadow,
# RAM_OamShadowBase) is never flagged. The bare register aliases (PPUCTRL,
# PPUADDR, OAMDMA, ...) are canonical names parsed from the table, not prefixes.
TRIGGER_PREFIXES = (
    "PPUCTRL_",
    "PPUMASK_",
    "PPUSTATUS_",
    "PAD_",
    "OAM_",
    "APU_",
    "JOY1_",
    "JOY2_",
)

HARDWARE_ANCHOR = '<a id="hardware-constants"></a>'
NEXT_ANCHOR_RE = re.compile(r'<a\s+id="[^"]+"\s*></a>')
# First column of a markdown table row: | `NAME` | ... — conservative, so prose
# backticks and composite examples outside the tables are not treated as canonical.
TABLE_NAME_RE = re.compile(r"^\|\s*`([A-Za-z0-9_]+)`\s*\|")
# A symbol definition: NAME .EQU ... (xasm), case-insensitive directive.
EQU_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s+\.EQU\b", re.IGNORECASE)


def parse_canonical_names(asm_style_path: Path) -> set[str]:
    text = asm_style_path.read_text(encoding="utf-8") if asm_style_path.exists() else ""
    lines = text.splitlines()
    start = None
    for i, line in enumerate(lines):
        if HARDWARE_ANCHOR in line:
            start = i + 1
            break
    if start is None:
        return set()
    names: set[str] = set()
    for line in lines[start:]:
        if NEXT_ANCHOR_RE.search(line):
            break
        m = TABLE_NAME_RE.match(line)
        if m:
            names.add(m.group(1))
    return names


def parse_allowlist(allowlist_path: Path) -> set[str]:
    if not allowlist_path.exists():
        return set()
    out: set[str] = set()
    for raw in allowlist_path.read_text(encoding="utf-8").splitlines():
        line = raw.split("#", 1)[0].strip()
        if line:
            out.add(line)
    return out


def project_equ_names(asm_path: Path):
    out = []
    if not asm_path.exists():
        return out
    for lineno, raw in enumerate(asm_path.read_text(encoding="utf-8").splitlines(), start=1):
        m = EQU_RE.match(raw)
        if m:
            out.append((lineno, m.group(1)))
    return out


def main() -> int:
    args = [a for a in sys.argv[1:] if a != "--strict"]
    strict = "--strict" in sys.argv[1:]
    if len(args) != 3:
        print(
            "usage: check_hardware_constant_drift.py <asm_file> <asm_style_md> "
            "<allowlist_file> [--strict]",
            file=sys.stderr,
        )
        return 64

    asm_path, asm_style_path, allowlist_path = (Path(a) for a in args)
    canonical = parse_canonical_names(asm_style_path)
    allowlist = parse_allowlist(allowlist_path)

    drift = []
    for lineno, name in project_equ_names(asm_path):
        if not name.startswith(TRIGGER_PREFIXES):
            continue
        if name in canonical or name in allowlist:
            continue
        drift.append((lineno, name))

    if not drift:
        print("OK: no canonical hardware-constant drift")
        return 0

    print(
        f"warn: {len(drift)} project-local hardware-prefixed constant(s) are not "
        "canonical. For each, either rename to a canonical constant if one fits; "
        "add it to agent_playbook/ASM_STYLE.md#hardware-constants if it is globally "
        "reusable; or allowlist it in "
        f"{allowlist_path} if it is a project-local composite/encoding constant."
    )
    for lineno, name in drift:
        print(f"warn:   {asm_path}:{lineno}: {name}")

    return 3 if strict else 0


if __name__ == "__main__":
    raise SystemExit(main())
