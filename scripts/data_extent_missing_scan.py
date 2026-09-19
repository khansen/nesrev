#!/usr/bin/env python3
"""Advisory scan for fixed-size indexed tables missing a data_extent_assertions.csv entry.

`data_extent_assertions_check.sh` only *validates* listed rows; nothing flags a
bounded-index table that *should* be asserted and is not. This scan closes that
gap. Findings are advisory (exit 0); invalid evidence is an error (exit 65).

All the dataflow — resolving the index bound through a masking or compare idiom,
tying it to the read's index register, resolving symbolic mask/count constants,
and scoping to the read site's own routine — is done by xasm. This scan is a
pure join of two artifacts (no assembly here):

  - index_patterns.json : per read site, `index_upper_bound` + `index_bound_kind`
                          (mask|compare) when xasm can prove a bound.
  - data_consumers.json : `declared_size` per data label.

Project wrappers supply a validated invocation-local bundle and --asm to bind
it to the source. The positional artifact paths are used only by the legacy
offline interface without a bundle; absent offline evidence is NOT CHECKED.

A table is flagged when a read site carries a proven bound, that bound equals the
table's declared size, and the project has no assertion row for it. See
agent_playbook/QUALITY_REVIEW.md and PASS_WORKFLOW.md; the xasm side is specified
in xorcyst/XASM_INDEX_BOUND_ANALYSIS_SPEC.md.
"""
import csv
import os
import sys

from analysis_bundle import check_schema, read_json, require, supplied


def asserted_labels(path):
    if not os.path.isfile(path):
        return set()
    with open(path, encoding="utf-8", newline="") as stream:
        reader = csv.DictReader(stream)
        require(reader.fieldnames == ["label", "expected_size", "reason"],
                "invalid data extent assertions header")
        labels = set()
        for row in reader:
            require(None not in row and all(value is not None for value in row.values()),
                    f"invalid assertions row at line {reader.line_num}")
            label = row["label"].strip()
            require(bool(label), f"empty assertion label at line {reader.line_num}")
            labels.add(label)
        return labels


def main():
    args = sys.argv[1:]
    source = None
    if len(args) == 5 and args[0] == "--asm":
        source, args = args[1], args[2:]
    if len(args) != 3 or args[0].startswith("--"):
        sys.stderr.write(
            "usage: data_extent_missing_scan.py "
            "[--asm <asm_file>] <index_patterns_json> <data_consumers_json> <assertions_csv>\n")
        raise SystemExit(64)
    index_patterns_path, data_consumers_path, assertions_csv = args
    if "NESREV_ANALYSIS_BUNDLE" in os.environ:
        require(source is not None, "--asm is required with a supplied analysis bundle")
    bundle = supplied(source)
    if bundle is not None:
        bundle.require_policy(assertions_csv)
        patterns = bundle.load("index_patterns")
        consumers = bundle.load("data_consumers")
    else:
        require(source is None, "--asm requires an invocation-local analysis bundle; refusing cached fallback")
        if not os.path.isfile(index_patterns_path) or not os.path.isfile(data_consumers_path):
            print("NOT CHECKED: extent scan requires both index-pattern and data-consumer artifacts")
            return
        patterns = read_json(index_patterns_path)
        consumers = read_json(data_consumers_path)
        check_schema("index_patterns", patterns)
        check_schema("data_consumers", consumers)

    sizes = {entry["label"]: entry["declared_size"] for entry in consumers}
    asserted = asserted_labels(assertions_csv)

    hits = {}
    for rec in patterns:
        if rec.get("access_kind") != "read":
            continue
        kind = rec.get("index_bound_kind")
        if kind not in ("mask", "compare"):
            continue
        label = rec.get("table_label")
        bound = rec.get("index_upper_bound")
        require(type(bound) is int and bound >= 0, "invalid index_upper_bound for bounded read")
        if label is None or label in asserted or label not in sizes:
            continue
        if bound != sizes[label]:
            continue
        # First proof per table wins; a table needs only one assertion.
        hits.setdefault(label, (sizes[label], rec.get("routine"), kind, bound))

    if bundle is not None:
        bundle.validate()

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


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(f"REFUSED: data extent scan: {exc}", file=sys.stderr)
        raise SystemExit(65)
