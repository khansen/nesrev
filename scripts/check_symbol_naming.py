#!/usr/bin/env python3
"""Validate canonical project symbol definitions."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
DEFINITION_RE = re.compile(
    r"^\s*((?:ZP|RAM)_[A-Za-z0-9_]+)\s+\.EQU\b",
    re.MULTILINE,
)
BODY_RE = re.compile(r"^[A-Z][A-Za-z0-9]*$")
UPPERCASE_ACRONYM_RE = re.compile(
    r"(?:PPU|NMI|OAM|APU|BCD|RNG|SFX|DMC|PRG|CHR|VRAM|CPU|IRQ|DMA)"
)
PPUCTRL_PATTERN_RE = re.compile(
    r"^\s*(PPUCTRL_[A-Za-z0-9_]+)\s+\.EQU\s+(\$[0-9A-Fa-f]+|%[01]+)\b",
    re.MULTILINE,
)
PPUCTRL_PATTERN_NAMES = {
    0x08: "PPUCTRL_SPRITE_PT_1000",
    0x10: "PPUCTRL_BG_PT_1000",
}
PATTERN_ROLE_RE = re.compile(r"(?:BG|BACKGROUND|SPR|SPRITE).*(?:PT|PATTERN|CHR|TABLE)")
DIRECT_EQU_RE = re.compile(
    r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s+\.EQU\s+\$([0-9A-Fa-f]{4})\b",
    re.MULTILINE,
)
DATA_BYTE_DIRECTIVE_RE = re.compile(
    r"^\s*(?:[A-Za-z_][A-Za-z0-9_]*:\s*)?\.(?:DB|BYTE)\b(?P<payload>.*)",
    re.IGNORECASE,
)
LOWADDR_SYMBOL_RE = re.compile(r"\b(?:ZP|RAM)_[A-Za-z0-9_]+\b")
CANONICAL_HARDWARE_REGISTERS = {
    0x2000: "PPUCTRL",
    0x2001: "PPUMASK",
    0x2002: "PPUSTATUS",
    0x2003: "OAMADDR",
    0x2004: "OAMDATA",
    0x2005: "PPUSCROLL",
    0x2006: "PPUADDR",
    0x2007: "PPUDATA",
    0x4000: "APU_PULSE1_CTRL",
    0x4001: "APU_PULSE1_SWEEP",
    0x4002: "APU_PULSE1_TIMER_LO",
    0x4003: "APU_PULSE1_TIMER_HI",
    0x4004: "APU_PULSE2_CTRL",
    0x4005: "APU_PULSE2_SWEEP",
    0x4006: "APU_PULSE2_TIMER_LO",
    0x4007: "APU_PULSE2_TIMER_HI",
    0x4008: "APU_TRI_LINEAR",
    0x400A: "APU_TRI_TIMER_LO",
    0x400B: "APU_TRI_TIMER_HI",
    0x400C: "APU_NOISE_CTRL",
    0x400E: "APU_NOISE_PERIOD",
    0x400F: "APU_NOISE_LENGTH",
    0x4010: "APU_DMC_CTRL",
    0x4011: "APU_DMC_DA",
    0x4012: "APU_DMC_ADDR",
    0x4013: "APU_DMC_LEN",
    0x4014: "OAMDMA",
    0x4015: "APU_STATUS",
    0x4016: "JOY1_STROBE",
    0x4017: "APU_FRAME_COUNTER",
}


def has_pointer_byte_prefix(payload: str, symbol_start: int) -> bool:
    prefix = payload[:symbol_start].rstrip()
    while prefix.endswith("("):
        prefix = prefix[:-1].rstrip()
    return prefix.endswith("<") or prefix.endswith(">")


def tracked_primary_asm() -> list[Path]:
    result = subprocess.run(
        ["git", "ls-files", "projects/*/asm/*.asm"],
        cwd=REPO,
        check=True,
        capture_output=True,
        text=True,
    )
    paths: list[Path] = []
    for line in result.stdout.splitlines():
        relative = Path(line)
        if (
            len(relative.parts) == 4
            and relative.parts[0] == "projects"
            and relative.parts[2] == "asm"
        ):
            paths.append(REPO / relative)
    return paths


def validate(path: Path) -> list[str]:
    errors: list[str] = []
    text = path.read_text(encoding="utf-8")
    try:
        display_path = path.relative_to(REPO)
    except ValueError:
        display_path = path
    for match in DEFINITION_RE.finditer(text):
        name = match.group(1)
        body = name.split("_", 1)[1]
        if (
            not BODY_RE.fullmatch(body)
            or UPPERCASE_ACRONYM_RE.search(body)
            or (len(body) > 1 and body.isupper())
        ):
            line = text.count("\n", 0, match.start()) + 1
            errors.append(
                f"{display_path}:{line}: {name} must use "
                "ZP_<UpperCamelRole> or RAM_<UpperCamelRole> with no "
                "additional underscores (for example ZP_PpuCtrlShadow)"
            )
    for match in PPUCTRL_PATTERN_RE.finditer(text):
        name, raw_value = match.groups()
        if not PATTERN_ROLE_RE.search(name):
            continue
        value = int(raw_value[1:], 16 if raw_value.startswith("$") else 2)
        expected = PPUCTRL_PATTERN_NAMES.get(value)
        if expected is None or name == expected:
            continue
        line = text.count("\n", 0, match.start()) + 1
        errors.append(
            f"{display_path}:{line}: {name} assigns PPUCTRL pattern-table "
            f"bit {value:#04x}; use canonical {expected}"
        )
    for match in DIRECT_EQU_RE.finditer(text):
        name, raw_value = match.groups()
        value = int(raw_value, 16)
        expected = CANONICAL_HARDWARE_REGISTERS.get(value)
        if expected is None or name == expected:
            continue
        line = text.count("\n", 0, match.start()) + 1
        errors.append(
            f"{display_path}:{line}: {name} aliases NES hardware register "
            f"${value:04X}; use canonical {expected}"
        )
    for line_number, raw_line in enumerate(text.splitlines(), start=1):
        code = raw_line.split(";", 1)[0]
        directive = DATA_BYTE_DIRECTIVE_RE.match(code)
        if directive is None:
            continue
        payload = directive.group("payload")
        for match in LOWADDR_SYMBOL_RE.finditer(payload):
            if has_pointer_byte_prefix(payload, match.start()):
                continue
            errors.append(
                f"{display_path}:{line_number}: bare {match.group(0)} in .DB/.BYTE "
                "payload is suspicious; use raw byte data or an explicit "
                "pointer-byte expression such as <Symbol, >Symbol, "
                "<(Symbol + offset), or >(Symbol + offset)"
            )
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--tracked-primary",
        action="store_true",
        help="check every tracked projects/<slug>/asm/*.asm file",
    )
    parser.add_argument("paths", nargs="*", type=Path)
    args = parser.parse_args()

    if args.tracked_primary:
        paths = tracked_primary_asm()
    else:
        paths = [path if path.is_absolute() else REPO / path for path in args.paths]

    if not paths and not args.tracked_primary:
        parser.error("provide an asm path or --tracked-primary")

    errors: list[str] = []
    for path in paths:
        errors.extend(validate(path))

    if errors:
        for error in errors:
            print(f"FAIL: {error}", file=sys.stderr)
        return 1

    print(f"OK: canonical symbol naming in {len(paths)} asm file(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
