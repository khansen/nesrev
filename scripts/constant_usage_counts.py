#!/usr/bin/env python3
"""Add lexical usage counts to refresh_inventory.sh's sorted name/value rows.

Keep ripgrep's Unicode word boundaries and physical source-line identity. The
catalog counts matching lines (including comments), minus one definition line;
it does not count assembler references or individual token occurrences.

Normal text uses one search regardless of constant count. Binary input, custom
RIPGREP_CONFIG_PATH options, and search errors retain the legacy per-name path
for compatibility. Discovery, value spelling, domain precedence, sorting, and
distinct value rows remain the refresh wrapper's policy. This helper never
reads a committed catalog or changes the inventory regeneration/drift gate.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys


def legacy_counts(asm: str, names: set[str]) -> dict[str, int]:
    counts = {}
    for name in sorted(names):
        result = subprocess.run(
            ["rg", "-n", rf"\b{name}\b", asm], stdout=subprocess.PIPE, check=False,
        )
        # Bash command substitution removes NULs and trailing newlines.
        matches = result.stdout.replace(b"\0", b"").rstrip(b"\n")
        counts[name] = matches.count(b"\n") + 1 if matches else 0
    return counts


def count_lines(asm: str, names: set[str]) -> dict[str, int]:
    if not names:
        return {}
    # User-supplied rg options can change matching and output policy. Likewise,
    # binary-file notices are per-pattern results, not ordinary matching lines.
    if os.environ.get("RIPGREP_CONFIG_PATH"):
        return legacy_counts(asm, names)
    result = subprocess.run(
        ["rg", "--json", r"\b[A-Za-z_][A-Za-z0-9_]*\b", asm],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    if result.returncode not in (0, 1):
        return legacy_counts(asm, names)
    counts = dict.fromkeys(names, 0)
    for line in result.stdout.split(b"\n"):
        if not line:
            continue
        event = json.loads(line)
        data = event["data"]
        if event["type"] == "end" and data.get("binary_offset") is not None:
            return legacy_counts(asm, names)
        if event["type"] != "match":
            continue
        matched = {item["match"]["text"] for item in data["submatches"]}
        for name in matched & names:
            counts[name] += 1
    return counts


def main() -> int:
    if len(sys.argv) != 3:
        print("usage: constant_usage_counts.py <asm> <sorted-name-value-tsv>", file=sys.stderr)
        return 64
    try:
        rows = [line.partition(b"\t") for line in Path(sys.argv[2]).read_bytes().split(b"\n") if line]
        names = {name.decode("ascii") for name, _, _ in rows}
        counts = count_lines(sys.argv[1], names)
        for name, _, value in rows:
            uses = max(0, counts[name.decode("ascii")] - 1)
            sys.stdout.buffer.write(name + b"\t" + str(uses).encode("ascii") + b"\t" + value + b"\n")
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"error: cannot count constant usage: {error}", file=sys.stderr)
        return 65
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
