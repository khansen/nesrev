#!/usr/bin/env python3
"""Preserve xasm compare-v1 prefix semantics over successfully assembled facts."""

import json
import sys

from analysis_bundle import Bundle, BundleError, read_bytes


def compare(bundle, reference):
    output = bundle.data["outputs"]["binary"]["path"]
    actual, expected = read_bytes(output), read_bytes(reference)
    length = min(len(actual), len(expected))
    match = actual[:length] == expected[:length]
    bundle.validate()
    return {"version": "1", "reference_file": str(reference), "assembled_file": output,
            "compared_length": length, "match": match, "mismatches": []}


def main():
    if len(sys.argv) != 3:
        print("usage: analysis_prefix_compare.py <bundle> <reference_prg>", file=sys.stderr)
        return 64
    result = compare(Bundle(sys.argv[1]), sys.argv[2])
    if not result["match"]:
        # The owning wrapper obtains actual mismatch records from xasm; never
        # publish an empty mismatch list as if it were a complete diagnostic.
        return 5
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BundleError, OSError, ValueError, KeyError, TypeError) as exc:
        print(f"error: prefix comparison refused: {exc}", file=sys.stderr)
        raise SystemExit(65)
