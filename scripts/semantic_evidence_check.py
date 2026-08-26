#!/usr/bin/env python3
"""Surface narrow semantic-evidence gaps in crosswalks and .EQU families.

Two advisory signals are intentionally combined here because both ask whether
a semantic claim has a real source anchor:

* a confidence-bearing crosswalk row relies on reference ordering without
  citing an assembly symbol in its Evidence cell;
* a numeric constant seeds a same-family ``+N``/``-N`` chain but appears only
  in other ``.EQU`` declarations, never in an instruction or data operand.

Report mode exits zero for corpus calibration. ``--strict`` exits 68 when a
finding remains; projects should opt into strict mode only after reviewing and
disposing every advisory.
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path


USAGE = "usage: semantic_evidence_check.py <asm_file> <crosswalk.md> [--strict]"
EQU_RE = re.compile(
    r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s+\.EQU\s+(.+?)\s*$", re.IGNORECASE
)
LABEL_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*):")
IDENT_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_]*\b")
BACKTICK_SYMBOL_RE = re.compile(r"`([A-Za-z_][A-Za-z0-9_]*)`")
REFERENCE_SOURCE_RE = re.compile(
    r"\b(?:instruction\s+booklet|booklet|manual|guide|faq|"
    r"reference(?:\s+(?:document|material|source))?)\b",
    re.IGNORECASE,
)
ORDERING_RE = re.compile(r"\b(?:order(?:ed|ing)?|listed)\b", re.IGNORECASE)
CONFIDENCE_LEVELS = {"high", "medium", "inferred"}
NUMBER_RE = r"(?:\$[0-9A-Fa-f]+|%[01]+|\d+)"
STRUCTURAL_WORDS = {
    "byte",
    "bytes",
    "cols",
    "count",
    "field",
    "idx",
    "index",
    "last",
    "len",
    "length",
    "limit",
    "mask",
    "minus",
    "offset",
    "param",
    "record",
    "records",
    "rows",
    "size",
    "stride",
}


@dataclass(frozen=True)
class EquDefinition:
    name: str
    line: int
    expression: str


@dataclass(frozen=True)
class CrosswalkFinding:
    line: int
    term: str
    confidence: str


@dataclass(frozen=True)
class ConstantFinding:
    line: int
    root: str
    derived: tuple[str, ...]


def strip_comment(line: str) -> str:
    return line.split(";", 1)[0].rstrip()


def symbol_words(name: str) -> list[str]:
    """Return underscore-delimited family words, ignoring empty segments."""
    return [word.lower() for word in name.split("_") if word]


def same_family(left: str, right: str) -> bool:
    """Require a two-word shared prefix before treating constants as a family."""
    left_words = symbol_words(left)
    right_words = symbol_words(right)
    if set(left_words + right_words) & STRUCTURAL_WORDS:
        return False
    common = 0
    for left_word, right_word in zip(left_words, right_words):
        if left_word != right_word:
            break
        common += 1
    return common >= 2


def parse_equ_definitions(lines: list[str]) -> dict[str, EquDefinition]:
    definitions: dict[str, EquDefinition] = {}
    for line_number, raw in enumerate(lines, start=1):
        match = EQU_RE.match(strip_comment(raw))
        if match:
            definitions[match.group(1)] = EquDefinition(
                name=match.group(1),
                line=line_number,
                expression=match.group(2).strip(),
            )
    return definitions


def external_symbol_uses(
    lines: list[str], definitions: dict[str, EquDefinition]
) -> set[str]:
    """Constants referenced outside declarations, excluding comments."""
    used: set[str] = set()
    names = set(definitions)
    for raw in lines:
        code = strip_comment(raw)
        if EQU_RE.match(code):
            continue
        used.update(token for token in IDENT_RE.findall(code) if token in names)
    return used


def offset_dependencies(
    definitions: dict[str, EquDefinition]
) -> dict[str, set[str]]:
    """Map a root constant to same-family constants defined as root +/- N."""
    dependencies: dict[str, set[str]] = {}
    by_lower_name = {name.lower(): definition for name, definition in definitions.items()}
    offset_expression = re.compile(
        rf"^\(?([A-Za-z_][A-Za-z0-9_]*)[+-]{NUMBER_RE}\)?$", re.IGNORECASE
    )
    for derived in definitions.values():
        expression = derived.expression.replace(" ", "")
        match = offset_expression.fullmatch(expression)
        if not match:
            continue
        root = by_lower_name.get(match.group(1).lower())
        if root is None or root.name == derived.name:
            continue
        if same_family(root.name, derived.name):
            dependencies.setdefault(root.name, set()).add(derived.name)
    return dependencies


def find_unanchored_constant_roots(lines: list[str]) -> list[ConstantFinding]:
    definitions = parse_equ_definitions(lines)
    external_uses = external_symbol_uses(lines, definitions)
    dependencies = offset_dependencies(definitions)
    findings = [
        ConstantFinding(
            line=definitions[root].line,
            root=root,
            derived=tuple(sorted(derived)),
        )
        for root, derived in dependencies.items()
        if root not in external_uses
    ]
    return sorted(findings, key=lambda finding: (finding.line, finding.root))


def table_cells(line: str) -> list[str] | None:
    stripped = line.strip()
    if not (stripped.startswith("|") and stripped.endswith("|")):
        return None
    return [cell.strip() for cell in stripped.strip("|").split("|")]


def find_reference_order_findings(
    crosswalk_lines: list[str], asm_symbols: set[str]
) -> list[CrosswalkFinding]:
    findings: list[CrosswalkFinding] = []
    in_crosswalk_table = False
    for line_number, raw in enumerate(crosswalk_lines, start=1):
        cells = table_cells(raw)
        if cells is None:
            in_crosswalk_table = False
            continue
        if (
            len(cells) >= 2
            and cells[0].lower().startswith("reference term")
            and "asm symbol" in cells[1].lower()
        ):
            in_crosswalk_table = True
            continue
        if not in_crosswalk_table or len(cells) < 4:
            continue
        if set("".join(cells)) <= set("-: "):
            continue

        term, mapped, confidence_cell, evidence = cells[:4]
        confidence = confidence_cell.lower().replace(" confidence", "").strip()
        if confidence not in CONFIDENCE_LEVELS or not mapped:
            continue
        if not (REFERENCE_SOURCE_RE.search(evidence) and ORDERING_RE.search(evidence)):
            continue
        cited_symbols = set(BACKTICK_SYMBOL_RE.findall(evidence)) & asm_symbols
        if cited_symbols:
            continue
        findings.append(
            CrosswalkFinding(
                line=line_number,
                term=term,
                confidence=confidence,
            )
        )
    return findings


def asm_symbols(lines: list[str]) -> set[str]:
    symbols = set(parse_equ_definitions(lines))
    for raw in lines:
        match = LABEL_RE.match(strip_comment(raw))
        if match:
            symbols.add(match.group(1))
    return symbols


def read_lines(path: Path, role: str) -> list[str] | None:
    try:
        return path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeError) as exc:
        print(f"error: cannot read {role} {path}: {exc}", file=sys.stderr)
        return None


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
    crosswalk_path = Path(args[1])
    asm_lines = read_lines(asm_path, "asm file")
    if asm_lines is None:
        return 65
    crosswalk_lines = read_lines(crosswalk_path, "crosswalk")
    if crosswalk_lines is None:
        return 65

    crosswalk_findings = find_reference_order_findings(
        crosswalk_lines, asm_symbols(asm_lines)
    )
    constant_findings = find_unanchored_constant_roots(asm_lines)

    for finding in crosswalk_findings:
        print(
            f"advisory: {crosswalk_path}:{finding.line}: {finding.confidence} "
            f"mapping for {finding.term!r} relies on reference ordering without "
            "an assembly-symbol citation in Evidence",
            file=sys.stderr,
        )
    for finding in constant_findings:
        derived = ", ".join(finding.derived)
        print(
            f"advisory: {asm_path}:{finding.line}: {finding.root} seeds "
            f"same-family offset constant(s) {derived} but has no non-.EQU use",
            file=sys.stderr,
        )

    print(
        "[semantic-evidence] "
        f"reference_order_without_code_citation={len(crosswalk_findings)} "
        f"unanchored_derived_constant_roots={len(constant_findings)}"
    )
    total = len(crosswalk_findings) + len(constant_findings)
    if strict and total:
        print(f"FAIL: {total} semantic evidence gap(s) require review", file=sys.stderr)
        return 68
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
