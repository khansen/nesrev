#!/usr/bin/env python3
"""Advisory lint for reverse-engineering provenance in authored Markdown docs."""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from pathlib import Path


SKIP_FILENAMES = {
    "PROGRESS_SCORECARD.md",
}
SKIP_DIRS = {
    "inventory",
}
FENCE_RE = re.compile(r"^\s*```")

PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("pass_provenance", re.compile(r"\b(?:in|during|from|by|proven in)\s+pass\s+\d+\b", re.I)),
    ("proven_in_pass", re.compile(r"\bproven\s+(?:in|during|by)\s+(?:the\s+)?pass\b", re.I)),
    ("warning_baseline", re.compile(r"\bwarning-?baselined\b", re.I)),
    ("now_process", re.compile(r"\bnow\s+(?:explicit|documented|named|symbolized|recovered)\b", re.I)),
    ("unreferenced_claim", re.compile(r"\bcurrently\s+unreferenced\b|\bno\s+live\s+(?:caller|consumer)\b", re.I)),
    ("recovered_process", re.compile(r"\brecovered\s+(?:in|during|from|by)\s+(?:the\s+)?(?:pass|analysis|recovery)\b", re.I)),
    ("hidden_process", re.compile(r"\bhidden\s+(?:code|helper|entry|routine|label|dispatch|consumer)\b", re.I)),
)


@dataclass(frozen=True)
class Finding:
    path: Path
    line_no: int
    rule: str
    line: str


def markdown_files(roots: list[Path]) -> list[Path]:
    files: set[Path] = set()
    for root in roots:
        if root.is_file() and root.suffix == ".md":
            files.add(root)
            continue
        if not root.is_dir():
            continue
        for path in root.rglob("*.md"):
            parts = set(path.relative_to(root).parts[:-1])
            if path.name in SKIP_FILENAMES:
                continue
            if parts & SKIP_DIRS:
                continue
            files.add(path)
    return sorted(files)


def lint_file(path: Path) -> list[Finding]:
    findings: list[Finding] = []
    in_fence = False
    for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if FENCE_RE.match(line):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        for rule, pattern in PATTERNS:
            if pattern.search(line):
                findings.append(Finding(path, line_no, rule, line.strip()))
                break
    return findings


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", action="append", required=True, help="Markdown file or directory to scan")
    args = parser.parse_args()

    roots = [Path(root) for root in args.root]
    findings: list[Finding] = []
    for path in markdown_files(roots):
        findings.extend(lint_file(path))

    if not findings:
        print("OK: no docs provenance lint findings")
        return 0

    print(f"WARN: docs provenance lint found {len(findings)} issue(s)")
    for finding in findings:
        print(f"{finding.path}:{finding.line_no}: {finding.rule}: {finding.line}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
