#!/usr/bin/env python3
"""Advisory check for canonical NES hardware-constant drift.

A project should use the canonical hardware register/bit/field names defined in
``agent_playbook/ASM_STYLE.md#hardware-constants``. This check warns when a
project defines a ``.EQU`` whose name uses a canonical-looking hardware prefix
(``PPUCTRL_``, ``PPUMASK_``, ``PPUSTATUS_``, ``PAD_``, ``OAM_``, ``APU_``,
``JOY1_``, ``JOY2_``), or a legacy ``PPU_NAMETABLE_*_BIT``/``*_CLEAR_MASK``
shape, but is not canonical or listed in the project-local allowlist.

It is advisory by default: it prints ``warn:`` lines and exits 0 so it can be run
from ``project-process-check`` without failing the gate. When ``--projects-root``
is supplied, it also reports noncanonical constants independently allowlisted in
peer projects under the same name or a same-prefix, same-literal value. Those
recurrence findings are promotion evidence only and never affect the exit code.
Pass ``--strict`` to make unresolved drift exit non-zero (for a future promotion
to a hard gate once existing projects are clean or allowlisted).

Usage:
    check_hardware_constant_drift.py <asm_file> <asm_style_md> <allowlist_file>
        [--projects-root <dir>] [--strict]

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
PPU_NAMETABLE_NEAR_MISS_RE = re.compile(
    r"^PPU_NAMETABLE_(?:[XY]_BIT|[0-9A-F]{4}(?:_BIT|_CLEAR_MASK))$"
)

HARDWARE_ANCHOR = '<a id="hardware-constants"></a>'
NEXT_ANCHOR_RE = re.compile(r'<a\s+id="[^"]+"\s*></a>')
# First column of a markdown table row: | `NAME` | ... — conservative, so prose
# backticks and composite examples outside the tables are not treated as canonical.
TABLE_NAME_RE = re.compile(r"^\|\s*`([A-Za-z0-9_]+)`\s*\|")
# A symbol definition: NAME .EQU ... (xasm), case-insensitive directive.
EQU_RE = re.compile(
    r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s+\.EQU\s+([^;]+)", re.IGNORECASE
)
LITERAL_RES = (
    (re.compile(r"^\$([0-9A-Fa-f]+)$"), 16),
    (re.compile(r"^%([01]+)$"), 2),
    (re.compile(r"^0[xX]([0-9A-Fa-f]+)$"), 16),
    (re.compile(r"^([0-9]+)$"), 10),
)


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


def parse_literal(expression: str) -> int | None:
    text = expression.strip()
    for pattern, base in LITERAL_RES:
        match = pattern.fullmatch(text)
        if match:
            return int(match.group(1), base)
    return None


def project_equ_constants(asm_path: Path):
    out = {}
    if not asm_path.exists():
        return out
    for lineno, raw in enumerate(asm_path.read_text(encoding="utf-8").splitlines(), start=1):
        m = EQU_RE.match(raw)
        if m:
            name = m.group(1)
            expression = m.group(2).strip()
            out[name] = (lineno, parse_literal(expression))
    return out


def hardware_family(name: str) -> str | None:
    for prefix in TRIGGER_PREFIXES:
        if name.startswith(prefix):
            return prefix
    if PPU_NAMETABLE_NEAR_MISS_RE.fullmatch(name):
        return "PPU_NAMETABLE_"
    return None


def project_asm_constants(project_dir: Path):
    out = {}
    asm_paths = sorted((project_dir / "asm").glob("*.asm"))
    for asm_path in asm_paths:
        out.update(project_equ_constants(asm_path))
    return asm_paths, out


def allowlist_recurrences(
    asm_path: Path,
    allowlist: set[str],
    canonical: set[str],
    projects_root: Path | None,
):
    if projects_root is None or not projects_root.is_dir():
        return {}

    current = project_equ_constants(asm_path)
    current_candidates = {
        name: current[name]
        for name in allowlist
        if name in current and name not in canonical and hardware_family(name)
    }
    if not current_candidates:
        return {}

    current_resolved = asm_path.resolve()
    recurrences: dict[str, set[str]] = {}
    for project_dir in sorted(path for path in projects_root.iterdir() if path.is_dir()):
        peer_asm_paths, peer_constants = project_asm_constants(project_dir)
        if any(path.resolve() == current_resolved for path in peer_asm_paths):
            continue
        peer_allowlist = parse_allowlist(
            project_dir
            / "docs"
            / "reverse_engineering"
            / "inventory"
            / "hardware_local_allowlist.txt"
        )
        peer_candidates = {
            name: peer_constants[name]
            for name in peer_allowlist
            if name in peer_constants and name not in canonical and hardware_family(name)
        }
        for name, (_, value) in current_candidates.items():
            if name in peer_candidates:
                recurrences.setdefault(name, set()).add(
                    f"exact-name in {project_dir.name}"
                )
                continue
            if value is None:
                continue
            family = hardware_family(name)
            for peer_name, (_, peer_value) in peer_candidates.items():
                if peer_value == value and hardware_family(peer_name) == family:
                    recurrences.setdefault(name, set()).add(
                        f"same {family} literal ${value:02X} as "
                        f"{project_dir.name}:{peer_name}"
                    )
    return recurrences


def parse_args(argv: list[str]):
    positional = []
    strict = False
    projects_root = None
    index = 0
    while index < len(argv):
        arg = argv[index]
        if arg == "--strict":
            strict = True
        elif arg == "--projects-root":
            index += 1
            if index >= len(argv):
                return None
            projects_root = Path(argv[index])
        elif arg.startswith("--"):
            return None
        else:
            positional.append(arg)
        index += 1
    if len(positional) != 3:
        return None
    return tuple(Path(value) for value in positional), projects_root, strict


def main() -> int:
    parsed = parse_args(sys.argv[1:])
    if parsed is None:
        print(
            "usage: check_hardware_constant_drift.py <asm_file> <asm_style_md> "
            "<allowlist_file> [--projects-root <dir>] [--strict]",
            file=sys.stderr,
        )
        return 64

    (asm_path, asm_style_path, allowlist_path), projects_root, strict = parsed
    canonical = parse_canonical_names(asm_style_path)
    allowlist = parse_allowlist(allowlist_path)

    drift = []
    for name, (lineno, _) in project_equ_constants(asm_path).items():
        if not (
            name.startswith(TRIGGER_PREFIXES)
            or PPU_NAMETABLE_NEAR_MISS_RE.fullmatch(name)
        ):
            continue
        if name in canonical or name in allowlist:
            continue
        drift.append((lineno, name))

    if not drift:
        print("OK: no canonical hardware-constant drift")
    else:
        print(
            f"warn: {len(drift)} project-local hardware-prefixed constant(s) are not "
            "canonical. For each, either rename to a canonical constant if one fits; "
            "add it to agent_playbook/ASM_STYLE.md#hardware-constants if it is globally "
            "reusable; or allowlist it in "
            f"{allowlist_path} if it is a project-local composite/encoding constant."
        )
        for lineno, name in drift:
            print(f"warn:   {asm_path}:{lineno}: {name}")

    recurrences = allowlist_recurrences(
        asm_path, allowlist, canonical, projects_root
    )
    if recurrences:
        print(
            "advisory: "
            f"{len(recurrences)} allowlisted project-local hardware constant(s) "
            "recur in peer projects; review this evidence before canonical promotion."
        )
        for name, evidence in sorted(recurrences.items()):
            print(f"advisory:   {name}: {'; '.join(sorted(evidence))}")

    return 3 if strict and drift else 0


if __name__ == "__main__":
    raise SystemExit(main())
