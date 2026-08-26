#!/usr/bin/env python3
"""Check one-packet-per-line formatting for declared PPU packet streams.

The checker is deliberately annotation-gated. It inspects only global labels
whose nearby ``Format:`` comment says ``zero-terminated PPU ... packet`` and
whose name contains ``PpuPacketStream``. For the canonical NESrev format, each
source ``.DB`` line must contain exactly one packet:

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
LABEL_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*):")
EQU_RE = re.compile(
    r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s+\.EQU\s+(.+?)\s*$", re.IGNORECASE
)
DB_RE = re.compile(r"^\s*\.DB\s+(.+?)\s*$", re.IGNORECASE)
FORMAT_RE = re.compile(r"Format:\s*zero-terminated\s+PPU\b.*\bpacket", re.IGNORECASE)
ADDRESS_HIGH_VARIANT_RE = re.compile(
    r"(?:flags?.*address\s+high|address\s+high.*flags?|\bppu_hi\b)", re.IGNORECASE
)
STREAM_NAME_RE = re.compile(r"PpuPacketStream", re.IGNORECASE)


@dataclass(frozen=True)
class Finding:
    line: int
    stream: str
    message: str


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
    for index in range(label_index - 1, max(-1, label_index - 8), -1):
        stripped = lines[index].strip()
        if not stripped:
            continue
        if not stripped.startswith(";"):
            break
        comments.append(stripped)
    return comments


def format_comment_before(lines: list[str], label_index: int) -> bool:
    comments = comments_before(lines, label_index)
    return bool(
        any(FORMAT_RE.search(comment) for comment in comments)
        and not any(ADDRESS_HIGH_VARIANT_RE.search(comment) for comment in comments)
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
        and STREAM_NAME_RE.search(match.group(1))
        and format_comment_before(lines, index)
    )


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
    findings: list[Finding] = []
    terminated = False
    has_body = False
    for index in range(label_index + 1, len(lines)):
        if LABEL_RE.match(lines[index]):
            if (
                terminated
                or not is_declared_stream_label(lines, index)
                or not suffix_comment_before(lines, index)
            ):
                break
            # A second declared stream may be an entry into the unfinished
            # suffix of this stream. Continue until the shared terminator.
            continue
        raw = lines[index]
        stripped = raw.strip()
        if not stripped or stripped.startswith(";"):
            continue
        has_body = True
        line_number = index + 1
        values, error = parse_db_values(raw, resolver)
        if error is not None:
            findings.append(Finding(line_number, stream, error))
            continue
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
            continue
        control = values[2]
        payload_length = 1 if control & 0x40 else control & 0x3F
        expected = 3 + payload_length
        if len(values) != expected:
            mode = "repeat" if control & 0x40 else "literal"
            findings.append(
                Finding(
                    line_number,
                    stream,
                    f"{mode} packet control ${control:02X} requires {expected} byte(s) on the line; found {len(values)}",
                )
            )
    if not has_body:
        findings.append(Finding(label_index + 1, stream, "declared stream has no body"))
    elif not terminated:
        findings.append(
            Finding(label_index + 1, stream, "declared zero-terminated stream has no standalone terminator")
        )
    return findings


def analyze(lines: list[str]) -> tuple[int, list[Finding]]:
    resolver = ExpressionResolver(equ_expressions(lines))
    streams = 0
    findings: list[Finding] = []
    for index, raw in enumerate(lines):
        if not is_declared_stream_label(lines, index):
            continue
        streams += 1
        findings.extend(analyze_stream(lines, index, resolver))
    return streams, findings


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

    streams, findings = analyze(lines)
    for finding in findings:
        print(
            f"advisory: {path}:{finding.line}: {finding.stream}: {finding.message}",
            file=sys.stderr,
        )
    print(
        f"[ppu-packet-lines] declared_streams={streams} line_layout_findings={len(findings)}"
    )
    if strict and findings:
        print(
            f"FAIL: {len(findings)} declared PPU packet line-layout issue(s)",
            file=sys.stderr,
        )
        return 68
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
