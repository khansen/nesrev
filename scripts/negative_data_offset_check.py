#!/usr/bin/env python3
"""Report small negative indexed operands anchored to source data labels.

An operand such as ``LDA Table-3,X`` addresses bytes before ``Table`` unless
the runtime index compensates for the subtraction. That can be intentional,
but it is also a useful signal that the preceding bytes need their own label
or that ``Table`` is not the true record boundary.

The checker deliberately stays narrow: it reports direct numeric offsets from
labels whose first source statement is .DB/.DW/.BYTE/.WORD, only for X/Y
indexed instruction operands, and only for offsets 1 through 16. Report mode
exits zero for process-check use; ``--strict`` exits 68 when candidates remain.
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path


USAGE = "usage: negative_data_offset_check.py <asm_file> [--strict]"
MAX_OFFSET = 16
LABEL_NAME = r"(?:[A-Za-z_][A-Za-z0-9_]*|@@?[A-Za-z0-9_]+)"
LABEL_PREFIX_RE = re.compile(
    rf"^\s*(?P<label>{LABEL_NAME}):\s*(?P<rest>.*)$"
)
DATA_DIRECTIVE_RE = re.compile(r"^\s*\.(?:DB|DW|BYTE|WORD)\b", re.IGNORECASE)
INSTRUCTION_RE = re.compile(
    r"^\s*(?P<mnemonic>[A-Za-z]{3})(?:\.[A-Za-z])?\s+(?P<operand>.+?)\s*$"
)
NUMBER = r"(?:\$[0-9A-Fa-f]+|%[01]+|[0-9]+)"
DIRECT_INDEXED_RE = re.compile(
    rf"^\s*[\[(]?\s*(?P<label>{LABEL_NAME})\s*-\s*"
    rf"(?P<literal>{NUMBER})\s*[\])]?\s*,\s*(?P<index>[XY])\s*$",
    re.IGNORECASE,
)
ENCLOSED_INDEXED_RE = re.compile(
    rf"^\s*[\[(]\s*(?P<label>{LABEL_NAME})\s*-\s*"
    rf"(?P<literal>{NUMBER})\s*,\s*(?P<index>[XY])\s*[\])]\s*$",
    re.IGNORECASE,
)


@dataclass(frozen=True)
class Finding:
    line: int
    mnemonic: str
    operand: str
    label: str
    offset: int
    index: str


def strip_comment(line: str) -> str:
    return line.split(";", 1)[0].rstrip()


def strip_leading_labels(code: str) -> tuple[list[str], str]:
    labels: list[str] = []
    rest = code
    while True:
        match = LABEL_PREFIX_RE.match(rest)
        if not match:
            break
        labels.append(match.group("label"))
        rest = match.group("rest")
        if not rest.strip():
            break
    return labels, rest.strip()


def collect_data_labels(lines: list[str]) -> set[str]:
    data_labels: set[str] = set()
    pending: list[str] = []
    for raw in lines:
        code = strip_comment(raw).strip()
        if not code:
            continue
        labels, remainder = strip_leading_labels(code)
        pending.extend(labels)
        if not remainder:
            continue
        if DATA_DIRECTIVE_RE.match(remainder):
            data_labels.update(pending)
        pending.clear()
    return data_labels


def parse_number(text: str) -> int:
    if text.startswith("$"):
        return int(text[1:], 16)
    if text.startswith("%"):
        return int(text[1:], 2)
    return int(text, 10)


def analyze(lines: list[str]) -> list[Finding]:
    data_labels = collect_data_labels(lines)
    findings: list[Finding] = []
    for index, raw in enumerate(lines):
        code = strip_comment(raw).strip()
        if not code:
            continue
        _, code = strip_leading_labels(code)
        if not code:
            continue
        instruction = INSTRUCTION_RE.match(code)
        if not instruction:
            continue
        operand = instruction.group("operand")
        offset_match = DIRECT_INDEXED_RE.match(operand)
        if offset_match is None:
            offset_match = ENCLOSED_INDEXED_RE.match(operand)
        if offset_match is None:
            continue
        label = offset_match.group("label")
        if label not in data_labels:
            continue
        offset = parse_number(offset_match.group("literal"))
        if not 1 <= offset <= MAX_OFFSET:
            continue
        findings.append(
            Finding(
                line=index + 1,
                mnemonic=instruction.group("mnemonic").upper(),
                operand=operand.strip(),
                label=label,
                offset=offset,
                index=offset_match.group("index").upper(),
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
        print(
            f"advisory: {path}:{finding.line}: {finding.mnemonic} "
            f"{finding.operand} uses an indexed base {finding.offset} byte(s) "
            f"before data label {finding.label}; add/reuse the true boundary label or "
            "prove the index bias is intentional",
            file=sys.stderr,
        )
    print(
        f"[negative-data-offset] candidates={len(findings)} "
        f"max_offset={MAX_OFFSET}"
    )
    if strict and findings:
        print(
            f"FAIL: {len(findings)} small negative indexed data-label "
            "offset candidate(s) remain",
            file=sys.stderr,
        )
        return 68
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
