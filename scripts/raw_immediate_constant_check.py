#!/usr/bin/env python3
"""Find raw state/request writers that bypass an applicable existing constant.

The check is deliberately narrow. It looks for a numeric immediate loaded into
A, X, or Y and stored by the next executable instruction into a symbol whose
name describes state-like control data. A same-valued .EQU is reported only
when its semantic tokens overlap the destination by at least two words.

Report mode exits zero and is suitable for corpus calibration. ``--strict``
exits 68 when findings remain; callers should enable strict mode only after the
project has reviewed or fixed every reported site.
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path


USAGE = "usage: raw_immediate_constant_check.py <asm_file> [--strict]"
EQU_RE = re.compile(
    r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s+\.EQU\s+([^;\s]+)", re.IGNORECASE
)
LOAD_RE = re.compile(
    r"^\s*(LDA|LDX|LDY)\s+#(\$[0-9A-Fa-f]+|%[01]+|\d+)\b", re.IGNORECASE
)
STORE_RE = re.compile(
    r"^\s*(STA|STX|STY)\s+([A-Za-z_][A-Za-z0-9_]*)\b", re.IGNORECASE
)
LABEL_ONLY_RE = re.compile(
    r"^\s*((?:[A-Za-z_][A-Za-z0-9_]*)|(?:@@?[A-Za-z0-9_]+))(:?)\s*$"
)
DESTINATION_ROLE_RE = re.compile(
    r"(State|Request|Mode|Phase|Action|Status|Result)"
    r"(?:Base|Bits|Flag|Flags|Id|BySlot)?$",
    re.IGNORECASE,
)
CAMEL_RE = re.compile(r"[A-Z]+(?=[A-Z][a-z]|\d|$)|[A-Z]?[a-z]+|\d+")
REGISTER_STORE = {"LDA": "STA", "LDX": "STX", "LDY": "STY"}
OPCODES = frozenset(
    "ADC AND ASL BCC BCS BEQ BIT BMI BNE BPL BRK BVC BVS CLC CLD CLI CLV "
    "CMP CPX CPY DEC DEX DEY EOR INC INX INY JMP JSR LDA LDX LDY LSR NOP "
    "ORA PHA PHP PLA PLP ROL ROR RTI RTS SBC SEC SED SEI STA STX STY TAX "
    "TAY TSX TXA TXS TYA".split()
)
IGNORED_TOKENS = {"zp", "ram", "id", "value", "current", "next"}
STRUCTURAL_CONSTANT_TOKENS = {
    "field",
    "offset",
    "stride",
    "count",
    "index",
    "ptr",
    "lo",
    "hi",
}


@dataclass(frozen=True)
class Constant:
    name: str
    value: int


@dataclass(frozen=True)
class Finding:
    line: int
    load: str
    immediate: str
    destination: str
    constants: tuple[str, ...]


def parse_number(text: str) -> int | None:
    if re.fullmatch(r"\$[0-9A-Fa-f]+", text):
        return int(text[1:], 16)
    if re.fullmatch(r"%[01]+", text):
        return int(text[1:], 2)
    if re.fullmatch(r"\d+", text):
        return int(text, 10)
    return None


def semantic_tokens(name: str) -> set[str]:
    pieces: list[str] = []
    for part in name.split("_"):
        pieces.extend(CAMEL_RE.findall(part))
    return {piece.lower() for piece in pieces if piece.lower() not in IGNORED_TOKENS}


def strip_comment(line: str) -> str:
    return line.split(";", 1)[0].rstrip()


def next_executable(lines: list[str], start: int) -> tuple[int, str] | None:
    for index in range(start, len(lines)):
        code = strip_comment(lines[index]).strip()
        if not code:
            continue
        label = LABEL_ONLY_RE.fullmatch(code)
        if label and (label.group(2) == ":" or label.group(1).upper() not in OPCODES):
            continue
        return index, code
    return None


def collect_constants(lines: list[str]) -> list[Constant]:
    constants: list[Constant] = []
    for raw in lines:
        match = EQU_RE.match(strip_comment(raw))
        if not match:
            continue
        value = parse_number(match.group(2))
        if value is not None:
            constants.append(Constant(match.group(1), value))
    return constants


def analyze(lines: list[str]) -> list[Finding]:
    constants = collect_constants(lines)
    by_value: dict[int, list[Constant]] = {}
    for constant in constants:
        by_value.setdefault(constant.value, []).append(constant)

    findings: list[Finding] = []
    for index, raw in enumerate(lines):
        load_match = LOAD_RE.match(strip_comment(raw))
        if not load_match:
            continue
        following = next_executable(lines, index + 1)
        if following is None:
            continue
        _, code = following
        store_match = STORE_RE.match(code)
        if not store_match or store_match.group(1).upper() != REGISTER_STORE[load_match.group(1).upper()]:
            continue
        destination = store_match.group(2)
        destination_role_match = DESTINATION_ROLE_RE.search(destination)
        if not destination_role_match:
            continue
        value = parse_number(load_match.group(2))
        if value is None:
            continue
        destination_tokens = semantic_tokens(destination)
        destination_role = destination_role_match.group(1).lower()
        applicable = []
        for constant in by_value.get(value, []):
            if constant.name.startswith(("ZP_", "RAM_")):
                continue
            constant_tokens = semantic_tokens(constant.name)
            if destination_role not in constant_tokens:
                continue
            if constant_tokens & STRUCTURAL_CONSTANT_TOKENS:
                continue
            overlap = destination_tokens & constant_tokens
            if len(overlap) >= 2:
                applicable.append(constant.name)
        if applicable:
            findings.append(
                Finding(
                    line=index + 1,
                    load=load_match.group(1).upper(),
                    immediate=load_match.group(2),
                    destination=destination,
                    constants=tuple(sorted(applicable)),
                )
            )
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
    if len(args) != 1:
        print(USAGE, file=sys.stderr)
        return 64
    path = Path(args[0])
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeError) as exc:
        print(f"error: cannot read asm file {path}: {exc}", file=sys.stderr)
        return 65

    findings = analyze(lines)
    for finding in findings:
        candidates = ", ".join(finding.constants)
        print(
            f"advisory: {path}:{finding.line}: {finding.load} #{finding.immediate} "
            f"stored to {finding.destination}; applicable constant(s): {candidates}",
            file=sys.stderr,
        )
    print(f"[raw-immediate-constant] bypassed_constant_writers={len(findings)}")
    if strict and findings:
        print(
            f"FAIL: {len(findings)} raw state/request writer(s) bypass applicable constants",
            file=sys.stderr,
        )
        return 68
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
