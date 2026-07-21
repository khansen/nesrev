#!/usr/bin/env python3
"""Advisory scan for fixed-size indexed tables missing a data_extent_assertions.csv entry.

`data_extent_assertions_check.sh` only *validates* listed rows; nothing flags a
bounded-index table that *should* be asserted and is not. This scan closes that
gap. It is advisory: it never fails the gate on its own (the caller runs it with
`|| true`), it only lists candidates for the operator to disposition.

All the dataflow — resolving the index bound through a masking or compare idiom,
tying it to the read's index register, resolving symbolic mask/count constants,
and scoping to the read site's own routine — is done by xasm. This scan is a
pure join of two artifacts that `project-pass-prep` already generates (no
assembly here):

  - index_patterns.json : per read site, `index_upper_bound` + `index_bound_kind`
                          (mask|compare) when xasm can prove a bound.
  - data_consumers.json : `declared_size` per data label.

A table is flagged when a read site carries a proven bound, that bound equals the
table's declared size, and the project has no assertion row for it. See
agent_playbook/QUALITY_REVIEW.md and PASS_WORKFLOW.md; the xasm side is specified
in xorcyst/XASM_INDEX_BOUND_ANALYSIS_SPEC.md.
"""
import csv
import json
import os
import sys
from pathlib import Path


def load_json(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def main():
    if len(sys.argv) != 4:
        sys.stderr.write(
            "usage: data_extent_missing_scan.py "
            "<index_patterns_json> <data_consumers_json> <assertions_csv>\n")
        raise SystemExit(64)
    index_patterns_path, data_consumers_path, assertions_csv = sys.argv[1:4]

    if not os.path.isfile(index_patterns_path) or not os.path.isfile(data_consumers_path):
        print("data_extent_missing_scan_total=0")
        print("OK: analysis cache absent; run project-pass-prep to enable the scan")
        return

    sizes = {e["label"]: int(e["declared_size"]) for e in load_json(data_consumers_path)}

    asserted = set()
    if os.path.isfile(assertions_csv):
        with open(assertions_csv, encoding="utf-8") as f:
            for row in csv.DictReader(f):
                label = (row.get("label") or "").strip()
                if label:
                    asserted.add(label)

    hits = {}
    for rec in load_json(index_patterns_path):
        if rec.get("access_kind") != "read":
            continue
        kind = rec.get("index_bound_kind")
        if kind not in ("mask", "compare"):
            continue
        label = rec.get("table_label")
        bound = rec.get("index_upper_bound")
        if label is None or label in asserted or label not in sizes:
            continue
        if bound != sizes[label]:
            continue
        # First proof per table wins; a table needs only one assertion.
        hits.setdefault(label, (sizes[label], rec.get("routine"), kind, bound))

    if not hits:
        print("data_extent_missing_scan_total=0")
        print("OK: no unasserted bounded-index tables found")
        return

    print(f"data_extent_missing_scan_total={len(hits)}")
    print("ADVISORY: bounded-index data tables missing a data_extent_assertions.csv entry:")
    for label in sorted(hits):
        size, routine, kind, bound = hits[label]
        print(f"  {label}: size {size}, indexed in {routine} with a {kind} bound of {bound}")
        print(f"    -> add row: {label},{size},<{routine} indexes it with a {kind} bound of {bound}>")
    raise SystemExit(1)


if __name__ == "__main__":
    main()
