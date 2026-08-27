#!/usr/bin/env python3
"""Surface narrow action disagreements in current-pass rename-ledger rows.

The free-text reason in ``renames.csv`` can preserve a routine's actual action
even when the selected procedure name asserts a different one.  This checker
does not attempt general natural-language validation.  It compares only
executable labels, only rows from the newest pass by default, and only a small
set of opposing concrete action classes such as payload writes, cursor motion,
payload reads, and clears.

Report mode exits zero for process-check use.  ``--strict`` exits 68 when a
candidate remains, and ``--all-passes`` is available for explicit migration
audits of historical ledger rows.
"""

from __future__ import annotations

import csv
import re
import sys
from dataclasses import dataclass
from pathlib import Path


USAGE = (
    "usage: rename_reason_consistency_check.py <asm_file> <renames.csv> "
    "[--all-passes] [--strict]"
)
EXPECTED_HEADER = ["old_name", "new_name", "reason", "confidence", "pass_id"]
LABEL_PREFIX_RE = re.compile(
    r"^\s*(?P<label>[A-Za-z_][A-Za-z0-9_]*):\s*(?P<rest>.*)$"
)
INSTRUCTION_RE = re.compile(r"^[A-Za-z]{3}(?:\.[A-Za-z])?(?:\s|$)")
CAMEL_LEAD_RE = re.compile(r"^([A-Z][a-z]+)")
REASON_LEAD_RE = re.compile(r"^(?:the\s+)?([A-Za-z]+)", re.IGNORECASE)


ACTION_FORMS = {
    # Payload writes.
    "append": "write",
    "appends": "write",
    "appended": "write",
    "appending": "write",
    "emit": "write",
    "emits": "write",
    "emitted": "write",
    "emitting": "write",
    "store": "write",
    "stores": "write",
    "stored": "write",
    "storing": "write",
    "write": "write",
    "writes": "write",
    "writing": "write",
    "written": "write",
    "wrote": "write",
    # Cursor or position motion.
    "advance": "motion",
    "advances": "motion",
    "advanced": "motion",
    "advancing": "motion",
    "increment": "motion",
    "increments": "motion",
    "incremented": "motion",
    "incrementing": "motion",
    "move": "motion",
    "moves": "motion",
    "moved": "motion",
    "moving": "motion",
    # Payload reads.
    "decode": "read",
    "decodes": "read",
    "decoded": "read",
    "decoding": "read",
    "load": "read",
    "loads": "read",
    "loaded": "read",
    "loading": "read",
    "read": "read",
    "reads": "read",
    "reading": "read",
    # Clears and visibility resets.
    "clear": "clear",
    "clears": "clear",
    "cleared": "clear",
    "clearing": "clear",
    "hide": "clear",
    "hides": "clear",
    "hid": "clear",
    "hiding": "clear",
    "reset": "clear",
    "resets": "clear",
    "resetting": "clear",
}


@dataclass(frozen=True)
class LedgerRow:
    line: int
    new_name: str
    reason: str
    pass_id: int


@dataclass(frozen=True)
class Finding:
    line: int
    new_name: str
    reason: str
    pass_id: int
    name_action: str
    reason_action: str


def strip_comment(line: str) -> str:
    return line.split(";", 1)[0].strip()


def executable_labels(lines: list[str]) -> set[str]:
    labels: set[str] = set()
    pending: list[str] = []
    for raw in lines:
        code = strip_comment(raw)
        if not code:
            continue
        while True:
            match = LABEL_PREFIX_RE.match(code)
            if match is None:
                break
            pending.append(match.group("label"))
            code = match.group("rest").strip()
            if not code:
                break
        if not code:
            continue
        if INSTRUCTION_RE.match(code):
            labels.update(pending)
        pending.clear()
    return labels


def read_ledger(path: Path) -> list[LedgerRow]:
    rows: list[LedgerRow] = []
    with path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames != EXPECTED_HEADER:
            raise ValueError(
                f"header mismatch: expected {EXPECTED_HEADER!r}, "
                f"found {reader.fieldnames!r}"
            )
        for line, row in enumerate(reader, start=2):
            if None in row:
                raise ValueError(f"row {line} has too many fields")
            missing = [key for key in EXPECTED_HEADER if not row.get(key, "").strip()]
            if missing:
                raise ValueError(f"row {line} has empty fields: {', '.join(missing)}")
            try:
                pass_id = int(row["pass_id"])
            except ValueError as exc:
                raise ValueError(f"row {line} has invalid pass_id {row['pass_id']!r}") from exc
            rows.append(
                LedgerRow(
                    line=line,
                    new_name=row["new_name"].strip(),
                    reason=row["reason"].strip(),
                    pass_id=pass_id,
                )
            )
    return rows


def action_for_name(name: str) -> str | None:
    match = CAMEL_LEAD_RE.match(name)
    if match is None:
        return None
    return ACTION_FORMS.get(match.group(1).lower())


def action_for_reason(reason: str) -> str | None:
    match = REASON_LEAD_RE.match(reason)
    if match is None:
        return None
    return ACTION_FORMS.get(match.group(1).lower())


def analyze(
    rows: list[LedgerRow], code_labels: set[str], all_passes: bool
) -> tuple[list[Finding], int | None]:
    latest_pass = max((row.pass_id for row in rows), default=None)
    findings: list[Finding] = []
    for row in rows:
        if not all_passes and row.pass_id != latest_pass:
            continue
        if row.new_name not in code_labels:
            continue
        name_action = action_for_name(row.new_name)
        reason_action = action_for_reason(row.reason)
        if name_action is None or reason_action is None or name_action == reason_action:
            continue
        findings.append(
            Finding(
                line=row.line,
                new_name=row.new_name,
                reason=row.reason,
                pass_id=row.pass_id,
                name_action=name_action,
                reason_action=reason_action,
            )
        )
    return findings, latest_pass


def main(argv: list[str]) -> int:
    strict = False
    all_passes = False
    args: list[str] = []
    for arg in argv:
        if arg == "--strict":
            strict = True
        elif arg == "--all-passes":
            all_passes = True
        elif arg.startswith("-"):
            print(USAGE, file=sys.stderr)
            return 64
        else:
            args.append(arg)
    if len(args) != 2:
        print(USAGE, file=sys.stderr)
        return 64

    asm_path = Path(args[0])
    ledger_path = Path(args[1])
    try:
        asm_lines = asm_path.read_text(encoding="utf-8").splitlines()
        rows = read_ledger(ledger_path)
    except (OSError, UnicodeError, ValueError) as exc:
        print(f"error: cannot analyze rename reasons: {exc}", file=sys.stderr)
        return 65

    findings, latest_pass = analyze(rows, executable_labels(asm_lines), all_passes)
    for finding in findings:
        print(
            f"advisory: {ledger_path}:{finding.line}: pass {finding.pass_id} "
            f"{finding.new_name} names a {finding.name_action} action but its "
            f"reason begins with a {finding.reason_action} action: {finding.reason!r}; "
            "confirm the routine body and reconcile the name or reason",
            file=sys.stderr,
        )
    scope = "all" if all_passes else str(latest_pass) if latest_pass is not None else "none"
    print(f"[rename-reason] candidates={len(findings)} pass_scope={scope}")
    if strict and findings:
        print(
            f"FAIL: {len(findings)} rename name/reason action candidate(s) remain",
            file=sys.stderr,
        )
        return 68
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
