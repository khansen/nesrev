#!/usr/bin/env python3
"""Raw-address KPI lexical policy over validated emitted instruction uses."""

import argparse
import re
import sys

from analysis_bundle import BundleError, read_bytes, require, supplied


LOW_LITERAL = re.compile(r"\$(?:[0-9A-F]{1,2}|0[0-9A-F]{2,3})")
ROM_LITERAL = re.compile(r"\$[C-F][0-9A-F]{3}")
STORE_MNEMONICS = {"STA", "STX", "STY"}
METRICS = ("strict_active_raw_lowaddr", "strict_active_raw_absrom")
LIMITS = ("MAX_ACTIVE_RAW_LOWADDR", "MAX_ACTIVE_RAW_ABSROM")


def category(record):
    tree = record["expression"]
    if record["immediate"] or tree is None or tree["kind"] != "integer":
        return None
    spelling = tree["source"]["text"]
    if LOW_LITERAL.fullmatch(spelling):
        return METRICS[0]
    if ROM_LITERAL.fullmatch(spelling) and record["mnemonic"] not in STORE_MNEMONICS:
        return METRICS[1]
    return None


def counts(bundle):
    result = dict.fromkeys(METRICS, 0)
    for record in bundle.load("instructions")["records"]:
        metric = category(record)
        if metric is not None:
            result[metric] += 1
    bundle.validate()
    return result


def report(bundle, measured, path=None):
    limits = {}
    if path:
        bundle.require_policy(path)
        for line in read_bytes(path).decode("utf-8").splitlines():
            key, separator, value = line.partition("=")
            key = key.strip()
            if separator and key in LIMITS and key not in limits:
                require(re.fullmatch(r"[0-9]+", value.strip()) is not None,
                        f"{key} must be a nonnegative integer")
                limits[key] = int(value.strip())
        if len(limits) != len(LIMITS):
            print(f"error: KPI config must define {' and '.join(LIMITS)}: {path}", file=sys.stderr)
            return 67
    bundle.validate()
    for metric in METRICS:
        print(f"[raw-kpi] {metric}={measured[metric]}")
    if path:
        for status, metric, key in zip((68, 69), METRICS, LIMITS):
            if measured[metric] > limits[key]:
                print(f"FAIL: {metric} ({measured[metric]}) exceeds KPI max ({limits[key]})", file=sys.stderr)
                return status
        print("OK: raw-address KPI gate passed")
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source")
    parser.add_argument("policy", nargs="?")
    args = parser.parse_args(argv)
    bundle = supplied(args.source)
    require(bundle is not None, "instruction bundle required; invoke the shell wrapper for fresh standalone analysis")
    return report(bundle, counts(bundle), args.policy)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BundleError, OSError, ValueError, KeyError, TypeError, RecursionError) as exc:
        print(f"error: raw-address analysis refused: {exc}", file=sys.stderr)
        raise SystemExit(65)
