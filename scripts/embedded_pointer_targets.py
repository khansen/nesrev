#!/usr/bin/env python3
"""Emit symbolic pointer pairs embedded in .DB records.

This complements pointer_targets.sh, which owns .DW entries.  Some fixed-stride
records must remain .DB but can still carry relocatable <label,>label source
fields; this script makes those fields visible to inventory checks.
"""

from __future__ import annotations

import csv
import re
import sys
from pathlib import Path


LABEL_RE = re.compile(r"^\s*(@@)?([A-Za-z_][A-Za-z0-9_]*):")
EQU_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s+\.EQU\s+", re.IGNORECASE)
OPCODE_RE = re.compile(r"^[A-Z]{3}(\.[A-Z])?$")


def strip_comment(line: str) -> str:
    return line.split(";", 1)[0]


def line_label(line: str) -> str:
    match = LABEL_RE.match(line)
    if not match:
        return ""
    return match.group(2)


def strip_label(line: str) -> str:
    return LABEL_RE.sub("", line, count=1)


def token_kind(line: str) -> str:
    text = line.strip()
    if not text or text.startswith(";"):
        return ""
    if text.startswith("."):
        return "data"
    token = text.split(None, 1)[0]
    return "code" if OPCODE_RE.match(token.upper()) else "unknown"


def db_payload(line: str) -> str:
    text = strip_comment(strip_label(line)).strip()
    if not re.match(r"^\.DB(\s|$)", text, re.IGNORECASE):
        return ""
    return re.sub(r"^\.DB\s*", "", text, count=1, flags=re.IGNORECASE).strip()


def split_operands(payload: str) -> list[str]:
    operands: list[str] = []
    cur: list[str] = []
    depth = 0
    for ch in payload:
        if ch == "(":
            depth += 1
        elif ch == ")" and depth > 0:
            depth -= 1
        if ch == "," and depth == 0:
            operands.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    if cur or payload.endswith(","):
        operands.append("".join(cur).strip())
    return operands


def canonical_expr(token: str) -> str:
    expr = token.strip()
    if expr.startswith("<") or expr.startswith(">"):
        expr = expr[1:].strip()
    while expr.startswith("(") and expr.endswith(")"):
        inner = expr[1:-1].strip()
        if not inner:
            break
        expr = inner
    return expr


def base_label(expr: str) -> str:
    base = canonical_expr(expr)
    for sep in ("+", "-"):
        if sep in base:
            base = base.split(sep, 1)[0].strip()
    return base


def build_label_kinds(lines: list[str]) -> dict[str, str]:
    kinds: dict[str, str] = {}
    pending: list[str] = []

    def flush(kind: str) -> None:
        nonlocal pending
        for label in pending:
            kinds[label] = kind
        pending = []

    for line in lines:
        equ = EQU_RE.match(line)
        if equ:
            kinds[equ.group(1)] = "data"
            continue

        label = line_label(line)
        rest = line
        if label:
            if not line.lstrip().startswith("@@"):
                pending.append(label)
            rest = strip_label(line)
            if not rest.strip():
                continue

        kind = token_kind(rest)
        if kind and pending:
            flush(kind)

    if pending:
        flush("unknown")
    return kinds


def target_type(expr: str, label_kinds: dict[str, str]) -> tuple[str, str, str]:
    kind = label_kinds.get(base_label(expr), "unknown")
    if kind == "code":
        return "code_pointer", "high confidence", "auto-classified from target label leading instruction"
    if kind == "data":
        return "data_pointer", "high confidence", "auto-classified from target label leading data directive"
    return "unknown_pointer", "inferred", "auto-extracted from .DB <label,>label pair (target kind unresolved)"


def emit_rows(lines: list[str]) -> list[dict[str, object]]:
    label_kinds = build_label_kinds(lines)
    current_source = ""
    entry_by_source: dict[str, int] = {}
    rows: list[dict[str, object]] = []

    for line in lines:
        label = line_label(line)
        if label and not line.lstrip().startswith("@@"):
            current_source = label
            entry_by_source.setdefault(current_source, 0)

        payload = db_payload(line)
        if not payload or not current_source:
            continue

        operands = split_operands(payload)
        i = 0
        while i + 1 < len(operands):
            lo = operands[i].strip()
            hi = operands[i + 1].strip()
            if lo.startswith("<") and hi.startswith(">"):
                lo_expr = canonical_expr(lo)
                hi_expr = canonical_expr(hi)
                if lo_expr == hi_expr:
                    target, confidence, notes = target_type(lo_expr, label_kinds)
                    entry = entry_by_source[current_source]
                    rows.append({
                        "source": current_source,
                        "entry": entry,
                        "target_label": lo_expr,
                        "target_type": target,
                        "confidence": confidence,
                        "notes": notes,
                    })
                    entry_by_source[current_source] = entry + 1
                    i += 2
                    continue
            i += 1

    return rows


def main() -> int:
    if len(sys.argv) not in (2, 3):
        print("usage: embedded_pointer_targets.py <asm_file> [out_csv]", file=sys.stderr)
        return 64

    asm_path = Path(sys.argv[1])
    if not asm_path.is_file():
        print(f"error: asm file not found: {asm_path}", file=sys.stderr)
        return 65

    lines = asm_path.read_text(encoding="utf-8").splitlines()
    rows = emit_rows(lines)

    out = open(sys.argv[2], "w", newline="", encoding="utf-8") if len(sys.argv) == 3 else sys.stdout
    close_out = out is not sys.stdout
    try:
        writer = csv.DictWriter(out, fieldnames=[
            "source",
            "entry",
            "target_label",
            "target_type",
            "confidence",
            "notes",
        ], lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)
    finally:
        if close_out:
            out.close()

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
