#!/usr/bin/env python3
"""Advisory scan for data tables that a masked or fixed-count index bounds but
that have no `data_extent_assertions.csv` entry pinning their size.

The size guardrail (`data_extent_assertions_check.sh`) only *validates* listed
rows; nothing flags a bounded-index table that *should* be asserted and is not.
This scan closes that gap. It is advisory: it never fails the gate on its own
(the caller runs it with `|| true`), it only lists candidates for the operator
to disposition.

It consumes the `--data-consumers` cache that `project-pass-prep` already
generates (`inventory/pass/data_consumers.json`) rather than re-assembling, per
the wrapper-first evidence rule; if that cache is absent it skips.

Signal:
  1. The cache reports the table is read with an indexed absolute addressing
     mode (`absolute_x` / `absolute_y`).
  2. The reading routine's body bounds that index with either a bitmask
     `AND #(size-1)` (size a power of two) or a fixed count `CPX/CPY #size`.
  3. The table is not already in `data_extent_assertions.csv`.

A hit means: a future edit to the table's length would silently let the index
run past it, and parity alone would not catch a boundary shift that preserves
total ROM size. See agent_playbook/QUALITY_REVIEW.md and PASS_WORKFLOW.md.
"""
import csv
import json
import os
import re
import sys
from pathlib import Path

POW2 = {2, 4, 8, 16, 32, 64, 128, 256}


def routine_bodies(asm_file):
    """Map each global label -> its source text (label line to next global label)."""
    lines = Path(asm_file).read_text(encoding="utf-8").splitlines()
    heads = [(i, m.group(1)) for i, l in enumerate(lines)
             if (m := re.match(r"^([A-Za-z_][A-Za-z0-9_]*):", l))]
    bodies = {}
    for k, (i, name) in enumerate(heads):
        end = heads[k + 1][0] if k + 1 < len(heads) else len(lines)
        bodies.setdefault(name, "\n".join(l.split(";")[0] for l in lines[i:end]))
    return bodies


def bound_proof(body, size):
    """Return a short description if the routine bounds an index to `size`."""
    if size in POW2:
        for m in re.finditer(r"\bAND #\$([0-9A-Fa-f]{1,2})\b", body):
            if int(m.group(1), 16) == size - 1:
                return f"AND #${size - 1:02X}"
    for m in re.finditer(r"\bCP[XY] #\$([0-9A-Fa-f]{1,2})\b", body):
        if int(m.group(1), 16) == size:
            return f"{m.group(0).split()[0]} #${size:02X}"
    return None


def main():
    if len(sys.argv) != 4:
        sys.stderr.write(
            "usage: data_extent_missing_scan.py "
            "<data_consumers_json> <asm_file> <assertions_csv>\n")
        raise SystemExit(64)
    dc_json, asm_file, assertions_csv = sys.argv[1], sys.argv[2], sys.argv[3]

    if not os.path.isfile(dc_json):
        print("data_extent_missing_scan_total=0")
        print("OK: no data-consumers cache; run project-pass-prep to enable the scan")
        return
    if not os.path.isfile(asm_file):
        sys.stderr.write(f"error: asm file not found: {asm_file}\n")
        raise SystemExit(65)

    consumers = json.loads(Path(dc_json).read_text(encoding="utf-8"))

    asserted = set()
    if os.path.isfile(assertions_csv):
        with open(assertions_csv, encoding="utf-8") as f:
            for row in csv.DictReader(f):
                if (row.get("label") or "").strip():
                    asserted.add(row["label"].strip())

    bodies = routine_bodies(asm_file)
    hits = []
    for e in consumers:
        label = e["label"]
        size = int(e.get("declared_size", 0))
        if label in asserted or size < 2 or size > 256:
            continue
        indexed = [s for s in e.get("read_sites", [])
                   if s.get("addressing_mode") in ("absolute_x", "absolute_y")]
        if not indexed:
            continue
        for site in indexed:
            proof = bound_proof(bodies.get(site.get("routine", ""), ""), size)
            if proof:
                hits.append((label, size, site["routine"], proof))
                break

    if not hits:
        print("data_extent_missing_scan_total=0")
        print("OK: no unasserted bounded-index tables found")
        return
    print(f"data_extent_missing_scan_total={len(hits)}")
    print("ADVISORY: bounded-index data tables missing a data_extent_assertions.csv entry:")
    for label, size, routine, proof in sorted(set(hits)):
        print(f"  {label}: size {size}, indexed in {routine} bounded by {proof}")
        print(f"    -> add row: {label},{size},<consumer indexes it with {proof}>")
    raise SystemExit(1)


if __name__ == "__main__":
    main()
