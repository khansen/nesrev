#!/usr/bin/env python3
"""Branch-literal CSV v2 and KPI policy over validated xasm instruction records."""

import argparse
import csv
import io
import json
import os
from pathlib import Path
import sys
import tempfile

from analysis_bundle import BundleError, absolute, read_bytes, require, supplied


FIELDS = ["line", "enclosing_label", "mnemonic", "operand", "source", "schema_version",
          "source_file", "source_column", "source_end_line", "source_end_column",
          "use_file", "use_line", "use_column", "use_end_line", "use_end_column",
          "origin_id", "output_offset", "segment_id", "cpu_address", "expression"]


def qualifies(record):
    if record["immediate"] or record["index_register"] is not None:
        return False
    if record["addressing_mode"] not in {"relative", "absolute", "zeropage"}:
        return False
    tree = record["expression"]
    return (tree is not None and tree["kind"] == "operator" and tree["operator"] in {"+", "-"}
            and tree["children"][0]["kind"] == "current_pc"
            and tree["children"][1]["kind"] == "integer")


def portable(value, root):
    if isinstance(value, dict):
        return {key: os.path.relpath(absolute(child), root) if key == "file" else portable(child, root)
                for key, child in value.items()}
    if isinstance(value, list):
        return [portable(child, root) for child in value]
    return value


def rows(bundle):
    document = bundle.load("instructions")
    context = bundle.data["context"]
    root = os.getcwd() if context.get("project") else os.path.dirname(context["source"])
    result = []
    for record in document["records"]:
        if not qualifies(record):
            continue
        source = record["source"]
        location, use = portable(source["span"], root), portable(record["use"], root)
        result.append(dict(zip(FIELDS, [location["line"], record["lexical_owner"] or "(none)",
            record["mnemonic"], record["operand_source"]["text"], source["text"], "2",
            location["file"], location["column"], location["end_line"], location["end_column"],
            use["file"], use["line"], use["column"], use["end_line"], use["end_column"],
            record["origin_id"], record["output_offset"], record["segment_id"], record["cpu_address"],
            json.dumps(portable(record["expression"], root), ensure_ascii=False, separators=(",", ":"))])))
    bundle.validate()
    return result


def csv_bytes(records):
    stream = io.StringIO(newline="")
    writer = csv.DictWriter(stream, fieldnames=FIELDS, lineterminator="\n")
    writer.writeheader()
    writer.writerows(records)
    return stream.getvalue().encode("utf-8")


def write_csv(path, data, bundle):
    # Revalidate after staging and before replacement; refusal preserves the old ledger.
    with tempfile.NamedTemporaryFile(dir=Path(path).parent, delete=False) as stream:
        temporary = stream.name
        try:
            stream.write(data)
            stream.close()
            bundle.validate()
            os.replace(temporary, path)
        finally:
            if os.path.exists(temporary):
                os.unlink(temporary)


def report_kpi(bundle, records, path):
    maximum = None
    if path:
        bundle.require_policy(path)
        for line in read_bytes(path).decode("utf-8").splitlines():
            key, separator, value = line.partition("=")
            if separator and key.strip() == "MAX_ACTIVE_BRANCH_LITERALS":
                require(value.strip().isdigit(), "MAX_ACTIVE_BRANCH_LITERALS must be a nonnegative integer")
                maximum = int(value)
                break
        if maximum is None:
            print(f"error: KPI config must define MAX_ACTIVE_BRANCH_LITERALS: {path}", file=sys.stderr)
            return 67
    bundle.validate()
    count = len(records)
    print(f"[branch-kpi] strict_active_branch_literals={count}")
    if maximum is not None:
        if count > maximum:
            print(f"FAIL: strict_active_branch_literals ({count}) exceeds KPI max ({maximum})", file=sys.stderr)
            return 68
        print("OK: branch-literal KPI gate passed")
    return 0


def check_csv(bundle, records, path):
    require(path is not None, "sites registry path required")
    if not Path(path).is_file():
        print(f"error: branch-literal check input not found: {path}", file=sys.stderr)
        return 66
    current = read_bytes(path)
    bundle.validate()
    if current != csv_bytes(records):
        print(f"FAIL: branch-literal site registry is stale: {path}", file=sys.stderr)
        print("hint: run make project-inventory PROJECT=<slug>", file=sys.stderr)
        return 67
    print("OK: branch-literal site registry synchronized")
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("kpi", "sites", "check", "verify", "inventory"))
    parser.add_argument("source")
    parser.add_argument("path", nargs="?")
    parser.add_argument("--registry")
    args = parser.parse_args(argv)
    if args.mode == "verify":
        require(args.path and args.registry, "verification requires KPI policy and registry paths")
        if not Path(args.path).is_file():
            print(f"error: branch-literal kpi input not found: {args.path}", file=sys.stderr)
            return 66
    else:
        require(args.registry is None, "--registry is only valid for verification")
    if args.mode == "inventory":
        require(args.path, "inventory destination required")
    bundle = supplied(args.source)
    require(bundle is not None, "instruction bundle required; invoke the shell wrapper for fresh standalone analysis")
    records = rows(bundle)
    if args.mode in {"kpi", "verify", "inventory"}:
        status = report_kpi(bundle, records, None if args.mode == "inventory" else args.path)
        if status:
            return status
    if args.mode in {"sites", "inventory"}:
        data = csv_bytes(records)
        if args.path:
            write_csv(args.path, data, bundle)
        else:
            bundle.validate()
            sys.stdout.buffer.write(data)
    elif args.mode in {"check", "verify"}:
        return check_csv(bundle, records, args.registry if args.mode == "verify" else args.path)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BundleError, OSError, ValueError, KeyError, TypeError, RecursionError) as exc:
        print(f"error: branch-literal analysis refused: {exc}", file=sys.stderr)
        raise SystemExit(65)
