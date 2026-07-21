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
     mode (`absolute_x` / `absolute_y`), which fixes the index register.
  2. The reading routine's body bounds *that index register* with either a
     bitmask (`AND #(size-1)` immediately transferred to the index register via
     `TAX`/`TAY`, size a power of two) or a matching fixed-count compare
     (`CPX #size` for an X-indexed read, `CPY #size` for a Y-indexed read).
  3. The table is not already in `data_extent_assertions.csv`.

A hit means: a future edit to the table's length would silently let the index
run past it, and parity alone would not catch a boundary shift that preserves
total ROM size. See agent_playbook/QUALITY_REVIEW.md and PASS_WORKFLOW.md.

Known limitations (advisory, not proof):
  - Symbolic masks/counts (`AND #MASK3`, `CPX #ACTOR_SLOT_COUNT`) are not
    matched, so a clean scan is NOT proof that every bounded table is asserted;
    coverage shrinks as a corridor symbolizes its literals.
  - Only the direct `AND #imm / TA{reg} / LDA Table,{reg}` idiom is recognized;
    a masked value that reaches the index register indirectly (via a store and
    reload) is not proven and is left unflagged rather than mis-flagged.
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


def bound_proof(body, size, reg):
    """Return a short description if the routine bounds the `reg` index to `size`.

    The bound must connect to the index register used by the read (`reg` is
    "X" or "Y"): a mask must be transferred to it (`AND #(size-1)` then
    `TA{reg}` within a couple of instructions), and a fixed-count compare must
    use it (`CP{reg} #size`). This tie is what keeps an unrelated in-routine
    mask from falsely bounding a coincidentally-sized table.
    """
    lines = [l.strip() for l in body.splitlines() if l.strip()]
    if size in POW2:
        transfer = f"TA{reg}"
        for i, line in enumerate(lines):
            m = re.fullmatch(r"AND #\$([0-9A-Fa-f]{1,2})", line)
            if m and int(m.group(1), 16) == size - 1:
                # masked value must reach the index register right away
                if any(lines[j] == transfer for j in range(i + 1, min(i + 3, len(lines)))):
                    return f"AND #${size - 1:02X} -> {transfer}"
    for line in lines:
        m = re.fullmatch(rf"CP{reg} #\$([0-9A-Fa-f]{{1,2}})", line)
        if m and int(m.group(1), 16) == size:
            return f"CP{reg} #${size:02X}"
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
            reg = "X" if site["addressing_mode"] == "absolute_x" else "Y"
            proof = bound_proof(bodies.get(site.get("routine", ""), ""), size, reg)
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
    print("note: raw-mask idiom only; symbolic masks/counts are not detected, so a"
          " clean scan is not proof that every bounded table is asserted.")
    raise SystemExit(1)


if __name__ == "__main__":
    main()
