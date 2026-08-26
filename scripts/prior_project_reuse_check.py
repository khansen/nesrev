#!/usr/bin/env python3
"""Surface concrete constant-reuse candidates from a recorded analogue.

The prior-project reuse gate is semantic, so this checker is deliberately an
advisory shortlist rather than an automatic rename rule. It reports an
analogue constant only when all of these are true:

* the current project does not define that name;
* both projects expose a directly numeric, byte-sized value for comparison;
* the current assembly still uses that value as a raw immediate in nearby
  same-family code context; and
* the constant family is already reused by name, or at least two missing
  bit/mask constants from the same otherwise-unanchored family have matching
  bitwise sites.

The comparison is limited to reusable NES subsystem families and omits values
zero and one. Those conditions suppress the large number of accidental
same-value collisions between unrelated game-specific constants. Findings are
advisory by default. ``--strict`` is available for tests and for a project that
has reviewed its own zero baseline.
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path


EQU_RE = re.compile(
    r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s+\.EQU\s+([^;]+?)\s*$",
    re.IGNORECASE,
)
IMMEDIATE_RE = re.compile(
    r"^\s*(?:(?:@@)?[A-Za-z_][A-Za-z0-9_]*:\s*)?"
    r"([A-Za-z]{3}(?:\.[A-Za-z])?)\s+#\s*"
    r"(\$[0-9A-Fa-f]+|%[01]+|[0-9]+)\b"
)
DIRECT_LITERAL_RE = re.compile(r"^(\$[0-9A-Fa-f]+|%[01]+|[0-9]+)$")
BITMASK_NAME_RE = re.compile(
    r"(?:_BIT|_MASK|_ENABLE|_DISABLE|_SHOW_[A-Z0-9_]+)$"
)
BITWISE_MNEMONICS = {"AND", "BIT", "CMP", "CPX", "CPY", "EOR", "ORA"}
EXCLUDED_FAMILIES = {"RAM", "ZP"}
REUSABLE_FAMILIES = {
    "ACTOR",
    "APU",
    "AUDIO",
    "BCD",
    "HUD",
    "JOY1",
    "JOY2",
    "METASPRITE",
    "MUSIC",
    "NAMETABLE",
    "OAM",
    "OBJECT",
    "PAD",
    "PPU",
    "PPUCTRL",
    "PPUMASK",
    "PPUSTATUS",
    "RNG",
    "SCORE",
    "SFX",
    "SPRITE",
    "VRAM",
    "ZAPPER",
}
UNANCHORED_HARDWARE_FAMILIES = {
    "APU",
    "JOY1",
    "JOY2",
    "OAM",
    "PAD",
    "PPUCTRL",
    "PPUMASK",
    "PPUSTATUS",
    "ZAPPER",
}
FAMILY_CONTEXT_ALIASES = {
    "PAD": ("PAD", "JOYPAD", "JOY1"),
    "ZAPPER": ("ZAPPER", "JOY2"),
}
HARDWARE_CONTEXT_FAMILIES = {
    "APU",
    "JOY1",
    "JOY2",
    "OAM",
    "PAD",
    "PPUCTRL",
    "PPUMASK",
    "PPUSTATUS",
    "ZAPPER",
}
GENERIC_NAME_TOKENS = {
    "ACTIVE",
    "BASE",
    "BIT",
    "BITS",
    "BYTE",
    "BYTES",
    "CODE",
    "COUNT",
    "CTRL",
    "DELTA",
    "FLAG",
    "FRAME",
    "INDEX",
    "LEN",
    "LENGTH",
    "LIMIT",
    "MASK",
    "OFFSET",
    "PARAM",
    "PTR",
    "RELOAD",
    "REQUEST",
    "SLOT",
    "STATE",
    "STATUS",
    "STEP",
    "TABLE",
    "TIMER",
    "VALUE",
}


@dataclass(frozen=True)
class Equate:
    name: str
    value: int
    line: int
    literal: str


@dataclass(frozen=True)
class ImmediateSite:
    line: int
    mnemonic: str
    literal: str
    value: int
    context: str


@dataclass(frozen=True)
class Candidate:
    equate: Equate
    family: str
    sites: tuple[ImmediateSite, ...]
    aliases: tuple[str, ...]
    anchored: bool


def error(message: str) -> None:
    print(f"prior_project_reuse_check: error: {message}", file=sys.stderr)


def parse_literal(text: str) -> int | None:
    text = text.strip()
    if not DIRECT_LITERAL_RE.fullmatch(text):
        return None
    if text.startswith("$"):
        return int(text[1:], 16)
    if text.startswith("%"):
        return int(text[1:], 2)
    return int(text, 10)


def read_text(path: Path, role: str) -> list[str] | None:
    try:
        return path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeError) as exc:
        error(f"failed to read {role} {path}: {exc}")
        return None


def parse_equates(lines: list[str]) -> dict[str, Equate]:
    equates: dict[str, Equate] = {}
    for lineno, raw in enumerate(lines, start=1):
        match = EQU_RE.match(raw)
        if match is None:
            continue
        literal = match.group(2).strip()
        value = parse_literal(literal)
        if value is None:
            continue
        equates[match.group(1)] = Equate(
            name=match.group(1),
            value=value,
            line=lineno,
            literal=literal,
        )
    return equates


def parse_immediates(lines: list[str]) -> list[ImmediateSite]:
    sites: list[ImmediateSite] = []
    for lineno, raw in enumerate(lines, start=1):
        code = raw.split(";", 1)[0]
        match = IMMEDIATE_RE.match(code)
        if match is None:
            continue
        value = parse_literal(match.group(2))
        if value is None or not 0 <= value <= 0xFF:
            continue
        mnemonic = match.group(1).upper().split(".", 1)[0]
        # Producers normally load the owning field/register immediately before
        # the literal operation. Looking only two source lines backward keeps
        # adjacent routines or later unrelated operations from lending false
        # family context to the site.
        context_start = max(0, lineno - 3)
        context_end = lineno
        context_lines = []
        for context_raw in lines[context_start:context_end]:
            context_code = context_raw.split(";", 1)[0]
            if EQU_RE.match(context_code):
                continue
            context_lines.append(context_code.upper())
        context = "\n".join(context_lines)
        sites.append(
            ImmediateSite(
                line=lineno,
                mnemonic=mnemonic,
                literal=match.group(2),
                value=value,
                context=context,
            )
        )
    return sites


def constant_family(name: str) -> str | None:
    if "_" not in name:
        return None
    family = name.split("_", 1)[0]
    if family in EXCLUDED_FAMILIES:
        return None
    return family


def site_matches_family(site: ImmediateSite, equate: Equate, family: str) -> bool:
    tokens = FAMILY_CONTEXT_ALIASES.get(family, (family,))
    if not any(token in site.context for token in tokens):
        return False
    if family in HARDWARE_CONTEXT_FAMILIES:
        return True
    distinctive_tokens = {
        token
        for token in equate.name.split("_")[1:]
        if len(token) >= 3 and token not in GENERIC_NAME_TOKENS
    }
    return bool(distinctive_tokens) and any(
        token in site.context for token in distinctive_tokens
    )


def site_matches_value(site: ImmediateSite, equate: Equate, family: str) -> bool:
    if (
        family in {"METASPRITE", "OAM", "SPRITE"}
        and re.search(r"_(?:X|Y)$", equate.name)
        and site.mnemonic in {"AND", "BIT", "EOR", "ORA"}
    ):
        return False
    if site.value == equate.value:
        return True
    # A single-bit analogue constant can be hidden inside a combined AND/ORA
    # mask (for example START|SELECT). Context proof still applies, so
    # this does not turn every coincidental composite into a candidate.
    is_single_bit = equate.value > 0 and equate.value & (equate.value - 1) == 0
    if not is_single_bit or site.value & equate.value != equate.value:
        return False
    if (
        site.mnemonic in {"ORA", "EOR"}
        and family in HARDWARE_CONTEXT_FAMILIES
        and BITMASK_NAME_RE.search(equate.name)
    ):
        return True
    input_bit_name = (
        family == "ZAPPER"
        or equate.name.startswith("PAD_BTN_")
        or equate.name.startswith("PAD_DIR_")
        or BITMASK_NAME_RE.search(equate.name) is not None
    )
    return (
        site.mnemonic == "AND"
        and family in {"PAD", "ZAPPER"}
        and input_bit_name
        and site.value.bit_count() <= 4
    )


def find_candidates(
    current_equates: dict[str, Equate],
    analogue_equates: dict[str, Equate],
    immediate_sites: list[ImmediateSite],
) -> list[Candidate]:
    shared_families = {
        family
        for name, analogue in analogue_equates.items()
        if (current := current_equates.get(name)) is not None
        and current.value == analogue.value
        and (family := constant_family(name)) is not None
    }
    aliases_by_value: dict[int, list[str]] = defaultdict(list)
    for equate in current_equates.values():
        if constant_family(equate.name) is None:
            continue
        aliases_by_value[equate.value].append(equate.name)

    prelim: list[Candidate] = []
    for name, equate in analogue_equates.items():
        # Zero/one produce too many semantically unrelated cross-project
        # matches to be a useful reuse signal. Same-file state/value coverage
        # belongs to raw_immediate_constant_check.py instead.
        if name in current_equates or not 2 <= equate.value <= 0xFF:
            continue
        family = constant_family(name)
        if family is None or family not in REUSABLE_FAMILIES:
            continue
        if family == "ZAPPER" and not BITMASK_NAME_RE.search(name):
            continue
        sites = [
            site
            for site in immediate_sites
            if site_matches_value(site, equate, family)
            and site_matches_family(site, equate, family)
        ]
        if not sites:
            continue
        prelim.append(
            Candidate(
                equate=equate,
                family=family,
                sites=tuple(sites),
                aliases=tuple(sorted(aliases_by_value.get(equate.value, []))),
                anchored=family in shared_families,
            )
        )

    unanchored_bitmask_families: dict[str, set[str]] = defaultdict(set)
    for candidate in prelim:
        if candidate.anchored or not BITMASK_NAME_RE.search(candidate.equate.name):
            continue
        if any(site.mnemonic in BITWISE_MNEMONICS for site in candidate.sites):
            unanchored_bitmask_families[candidate.family].add(candidate.equate.name)

    allowed_unanchored = {
        family
        for family, names in unanchored_bitmask_families.items()
        if family in UNANCHORED_HARDWARE_FAMILIES and len(names) >= 2
    }
    return sorted(
        (
            candidate
            for candidate in prelim
            if candidate.anchored
            or (
                candidate.family in allowed_unanchored
                and BITMASK_NAME_RE.search(candidate.equate.name)
                and any(
                    site.mnemonic in BITWISE_MNEMONICS
                    for site in candidate.sites
                )
            )
        ),
        key=lambda candidate: (candidate.family, candidate.equate.name),
    )


def report(
    candidates: list[Candidate],
    current_path: Path,
    analogue_path: Path,
    analogue_slug: str,
) -> None:
    if not candidates:
        print(
            "OK: no evidence-backed prior-project constant reuse candidates "
            f"from analogue {analogue_slug}"
        )
        return

    family_count = len({candidate.family for candidate in candidates})
    print(
        f"warn: {len(candidates)} evidence-backed constant reuse candidate(s) "
        f"across {family_count} family/families from analogue {analogue_slug}. "
        "Review applicability; symbolize matching raw sites or record why the "
        "analogue pattern does not fit."
    )
    for candidate in candidates:
        equate = candidate.equate
        support = "shared-family" if candidate.anchored else "paired-bitmask-family"
        aliases = ",".join(candidate.aliases[:4]) if candidate.aliases else "none"
        print(
            f"warn:   {equate.name}={equate.literal} "
            f"({analogue_path}:{equate.line}; {support}; "
            f"current_same_value={aliases})"
        )
        for site in candidate.sites[:4]:
            print(
                f"warn:     {current_path}:{site.line}: "
                f"{site.mnemonic} #{site.literal}"
            )
        if len(candidate.sites) > 4:
            print(f"warn:     ... +{len(candidate.sites) - 4} more matching raw site(s)")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("current_asm", type=Path)
    parser.add_argument("analogue_asm", type=Path)
    parser.add_argument("--analogue-slug", required=True)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args(argv)

    current_lines = read_text(args.current_asm, "current asm")
    analogue_lines = read_text(args.analogue_asm, "analogue asm")
    if current_lines is None or analogue_lines is None:
        return 65

    current_equates = parse_equates(current_lines)
    analogue_equates = parse_equates(analogue_lines)
    immediate_sites = parse_immediates(current_lines)
    candidates = find_candidates(current_equates, analogue_equates, immediate_sites)
    report(
        candidates,
        current_path=args.current_asm,
        analogue_path=args.analogue_asm,
        analogue_slug=args.analogue_slug,
    )
    return 3 if args.strict and candidates else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
