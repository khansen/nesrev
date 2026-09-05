#!/usr/bin/env python3
"""Check one-packet-per-line formatting for declared PPU packet streams.

The checker is deliberately annotation-gated, not label-name-gated. It reports
coverage for PPU packet format declarations and checks the canonical
``zero-terminated PPU ... packet`` format. Other formats are explicitly not
checked. Each source ``.DB`` line must contain exactly one packet, except at
an explicitly declared field inside the current packet:

* three header bytes plus ``control & $3F`` payload bytes;
* or four total bytes when control bit 6 selects repeat mode;
* or one standalone zero terminator.

Report mode exits zero for corpus calibration. ``--strict`` exits 68 when a
declared stream is malformed, split across lines, joined on one line, missing
its terminator, or cannot be evaluated from its source expressions.
"""

from __future__ import annotations

import ast
import re
import sys
from dataclasses import dataclass
from pathlib import Path


USAGE = "usage: ppu_packet_line_check.py <asm_file> [--strict]"
LABEL_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*):")
EQU_RE = re.compile(
    r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s+\.EQU\s+(.+?)\s*$", re.IGNORECASE
)
DB_RE = re.compile(r"^\s*\.DB\s+(.+?)\s*$", re.IGNORECASE)
FORMAT_RE = re.compile(r"\bFormat:\s*(.*)", re.IGNORECASE)
PPU_PACKET_RE = re.compile(r"\bPPU\b.*\bpackets?\b", re.IGNORECASE)
CANONICAL_FORMAT_RE = re.compile(r"^zero-terminated\s+PPU\b.*\bpackets?\b", re.IGNORECASE)
GROUPED_STREAM_RE = re.compile(r"\b(?:streams|group(?:ed)?)\b", re.IGNORECASE)
ADDRESS_HIGH_VARIANT_RE = re.compile(
    r"(?:flags?.*address\s+high|address\s+high.*flags?|\bppu_hi\s*\|\s*flags?\b)", re.IGNORECASE
)


@dataclass(frozen=True)
class Finding:
    line: int
    stream: str
    message: str


@dataclass(frozen=True)
class Coverage:
    candidates: int
    checked: int
    findings: list[Finding]
    skipped: list[Finding]


class ExpressionResolver:
    def __init__(self, expressions: dict[str, str]):
        self.expressions = expressions
        self.by_lower = {name.lower(): name for name in expressions}
        self.cache: dict[str, int | None] = {}
        self.active: set[str] = set()

    @staticmethod
    def _pythonize(expression: str) -> str:
        expression = re.sub(r"\$([0-9A-Fa-f]+)", r"0x\1", expression)
        expression = re.sub(r"%([01]+)", r"0b\1", expression)
        return expression

    def resolve_name(self, name: str) -> int | None:
        canonical = self.by_lower.get(name.lower())
        if canonical is None:
            return None
        if canonical in self.cache:
            return self.cache[canonical]
        if canonical in self.active:
            return None
        self.active.add(canonical)
        value = self.resolve_expression(self.expressions[canonical])
        self.active.remove(canonical)
        self.cache[canonical] = value
        return value

    def resolve_expression(self, expression: str) -> int | None:
        try:
            node = ast.parse(self._pythonize(expression), mode="eval")
        except SyntaxError:
            return None
        return self._eval(node.body)

    def _eval(self, node: ast.AST) -> int | None:
        if isinstance(node, ast.Constant) and isinstance(node.value, int):
            return node.value
        if isinstance(node, ast.Name):
            return self.resolve_name(node.id)
        if isinstance(node, ast.UnaryOp) and isinstance(
            node.op, (ast.Invert, ast.UAdd, ast.USub)
        ):
            value = self._eval(node.operand)
            if value is None:
                return None
            if isinstance(node.op, ast.Invert):
                return ~value
            if isinstance(node.op, ast.USub):
                return -value
            return value
        if isinstance(node, ast.BinOp) and isinstance(
            node.op,
            (
                ast.Add,
                ast.Sub,
                ast.BitAnd,
                ast.BitOr,
                ast.BitXor,
                ast.LShift,
                ast.RShift,
            ),
        ):
            left = self._eval(node.left)
            right = self._eval(node.right)
            if left is None or right is None:
                return None
            operations = {
                ast.Add: lambda: left + right,
                ast.Sub: lambda: left - right,
                ast.BitAnd: lambda: left & right,
                ast.BitOr: lambda: left | right,
                ast.BitXor: lambda: left ^ right,
                ast.LShift: lambda: left << right,
                ast.RShift: lambda: left >> right,
            }
            return operations[type(node.op)]()
        return None


def strip_comment(line: str) -> str:
    return line.split(";", 1)[0].rstrip()


def equ_expressions(lines: list[str]) -> dict[str, str]:
    expressions: dict[str, str] = {}
    for raw in lines:
        match = EQU_RE.match(strip_comment(raw))
        if match:
            expressions[match.group(1)] = match.group(2).strip()
    return expressions


def comments_before(lines: list[str], label_index: int) -> list[str]:
    comments: list[str] = []
    for index in range(label_index - 1, -1, -1):
        stripped = lines[index].strip()
        if not stripped:
            continue
        if not stripped.startswith(";"):
            break
        comments.append(stripped)
    return list(reversed(comments))


def format_text_before(lines: list[str], label_index: int) -> str:
    parts: list[str] = []
    for comment in comments_before(lines, label_index):
        match = FORMAT_RE.search(comment)
        if match:
            parts = [match.group(1)]
        elif parts and re.match(r";\s*(?:Used by|Consumer|Index):", comment, re.IGNORECASE):
            break
        elif parts:
            parts.append(comment.lstrip("; "))
    return " ".join(parts)


def format_comment_before(lines: list[str], label_index: int) -> bool:
    text = format_text_before(lines, label_index)
    return bool(
        CANONICAL_FORMAT_RE.search(text)
        and not GROUPED_STREAM_RE.search(text)
        and not ADDRESS_HIGH_VARIANT_RE.search(text)
    )


def suffix_comment_before(lines: list[str], label_index: int) -> bool:
    return any(
        re.search(r"\bsuffix\b", comment, flags=re.IGNORECASE)
        for comment in comments_before(lines, label_index)
    )


def is_declared_stream_label(lines: list[str], index: int) -> bool:
    match = LABEL_RE.match(lines[index])
    return bool(
        match
        and format_comment_before(lines, index)
    )


def is_payload_field_label(lines: list[str], index: int, stream: str) -> bool:
    text = format_text_before(lines, index)
    return bool(re.search(
        rf"\b(?:field|payload)\b.*\b(?:inside|within)\s+`?{re.escape(stream)}\b",
        text,
        re.IGNORECASE,
    ))


def parse_db_values(
    raw: str, resolver: ExpressionResolver
) -> tuple[list[int] | None, str | None]:
    code = strip_comment(raw)
    match = DB_RE.match(code)
    if not match:
        return None, "body contains a non-.DB source line"
    values: list[int] = []
    for token in match.group(1).split(","):
        expression = token.strip()
        if not expression:
            return None, "body contains an empty .DB operand"
        value = resolver.resolve_expression(expression)
        if value is None or not 0 <= value <= 0xFF:
            return None, f"cannot resolve byte expression {expression!r}"
        values.append(value)
    return values, None


def analyze_stream(
    lines: list[str], label_index: int, resolver: ExpressionResolver
) -> list[Finding]:
    label_match = LABEL_RE.match(lines[label_index])
    assert label_match is not None
    stream = label_match.group(1)
    field_owners = {stream}
    findings: list[Finding] = []
    terminated = False
    has_body = False
    pending: tuple[int, int, list[int]] | None = None
    field_boundary = False

    def incomplete_packet(line: int, expected: int, values: list[int]) -> Finding:
        control = values[2]
        mode = "repeat" if control & 0x40 else "literal"
        return Finding(
            line, stream,
            f"{mode} packet control ${control:02X} requires {expected} byte(s) on the line; found {len(values)}",
        )

    for index in range(label_index, len(lines)):
        raw = lines[index]
        label = LABEL_RE.match(raw)
        if label and index != label_index:
            if pending and any(is_payload_field_label(lines, index, owner) for owner in field_owners):
                field_boundary = True
            elif (
                not has_body and (
                    not format_text_before(lines, index)
                    or is_declared_stream_label(lines, index)
                )
            ):
                field_owners.add(label.group(1))
            elif (
                not terminated
                and is_declared_stream_label(lines, index)
                and suffix_comment_before(lines, index)
            ):
                field_owners.add(label.group(1))
            else:
                break
        if label:
            raw = raw[label.end():]
        stripped = raw.strip()
        if not stripped or stripped.startswith(";"):
            continue
        has_body = True
        line_number = index + 1
        values, error = parse_db_values(raw, resolver)
        if pending:
            start_line, expected, previous = pending
            if (
                field_boundary and error is None and values is not None
                and len(previous) + len(values) <= expected
            ):
                combined = previous + values
                pending = (start_line, expected, combined) if len(combined) < expected else None
                field_boundary = False
                continue
            found = previous + values if field_boundary and values is not None else previous
            findings.append(incomplete_packet(start_line, expected, found))
            # Once alignment is lost, payload zeros cannot be interpreted as
            # terminators. Report the boundary defect without cascading noise.
            return findings
        field_boundary = False
        if error is not None:
            findings.append(Finding(line_number, stream, error))
            return findings
        assert values is not None
        if terminated:
            if "trailing bytes after stream terminator" not in raw.lower():
                findings.append(
                    Finding(
                        line_number,
                        stream,
                        "data follows the terminator without the sanctioned trailing-byte comment",
                    )
                )
            continue
        if values == [0]:
            terminated = True
            continue
        if values and values[0] == 0:
            findings.append(
                Finding(line_number, stream, "terminator must be a standalone .DB $00 line")
            )
            terminated = True
            continue
        if len(values) < 3:
            findings.append(
                Finding(line_number, stream, f"packet line has {len(values)} byte(s), fewer than the 3-byte header")
            )
            return findings
        control = values[2]
        payload_length = 1 if control & 0x40 else control & 0x3F
        expected = 3 + payload_length
        if len(values) < expected:
            pending = (line_number, expected, values)
        elif len(values) > expected:
            findings.append(incomplete_packet(line_number, expected, values))
            return findings
    if pending:
        findings.append(incomplete_packet(*pending))
    if not has_body:
        findings.append(Finding(label_index + 1, stream, "declared stream has no body"))
    elif not terminated:
        findings.append(
            Finding(label_index + 1, stream, "declared zero-terminated stream has no standalone terminator")
        )
    return findings


def analyze_coverage(lines: list[str]) -> Coverage:
    resolver = ExpressionResolver(equ_expressions(lines))
    streams = 0
    candidates = 0
    skipped: list[Finding] = []
    findings: list[Finding] = []
    for index, raw in enumerate(lines):
        label = LABEL_RE.match(raw)
        if not label:
            continue
        text = format_text_before(lines, index)
        if not PPU_PACKET_RE.search(text):
            continue
        candidates += 1
        if not is_declared_stream_label(lines, index):
            reason = (
                "address-high flag format is not supported by the control-byte decoder"
                if ADDRESS_HIGH_VARIANT_RE.search(text)
                else "format is not a single canonical zero-terminated PPU packet stream"
            )
            skipped.append(Finding(index + 1, label.group(1), reason))
            continue
        streams += 1
        findings.extend(analyze_stream(lines, index, resolver))
    return Coverage(candidates, streams, findings, skipped)


def analyze(lines: list[str]) -> tuple[int, list[Finding]]:
    coverage = analyze_coverage(lines)
    return coverage.checked, coverage.findings


def main(argv: list[str]) -> int:
    strict = False
    paths: list[str] = []
    for arg in argv:
        if arg == "--strict":
            strict = True
        elif arg.startswith("-"):
            print(USAGE, file=sys.stderr)
            return 64
        else:
            paths.append(arg)
    if len(paths) != 1:
        print(USAGE, file=sys.stderr)
        return 64

    path = Path(paths[0])
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeError) as exc:
        print(f"error: cannot read asm file {path}: {exc}", file=sys.stderr)
        return 65

    coverage = analyze_coverage(lines)
    streams, findings = coverage.checked, coverage.findings
    for skipped in coverage.skipped[:40]:
        print(
            f"NOT CHECKED: {path}:{skipped.line}: {skipped.stream}: {skipped.message}",
            file=sys.stderr,
        )
    if len(coverage.skipped) > 40:
        print(f"... {len(coverage.skipped) - 40} more skipped formats omitted", file=sys.stderr)
    for finding in findings:
        print(
            f"advisory: {path}:{finding.line}: {finding.stream}: {finding.message}",
            file=sys.stderr,
        )
    print(
        f"[ppu-packet-lines] declared_streams={streams} line_layout_findings={len(findings)} "
        f"format_candidates={coverage.candidates} checked_streams={streams} "
        f"skipped_formats={len(coverage.skipped)}"
    )
    if not streams:
        print("NOT CHECKED: no canonical PPU packet streams checked; unannotated data is outside this scan", file=sys.stderr)
    if strict and findings:
        print(
            f"FAIL: {len(findings)} declared PPU packet line-layout issue(s)",
            file=sys.stderr,
        )
        return 68
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
