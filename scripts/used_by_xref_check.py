#!/usr/bin/env python3
"""Validate mechanically checkable `; Used by:` declaration comments.

This is intentionally narrow: it checks comments that name concrete asm
symbols as consumers, and it skips broad prose-only ownership descriptions.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile
from collections import defaultdict
from pathlib import Path

from data_directive_xref import ContractError, load_xref


USAGE = (
    "usage: used_by_xref_check.py [--strict] [--generate-xref] "
    "<asm_file> [xref_json]"
)
GLOBAL_DEF_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*):")
EQU_DEF_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s+\.EQU\b", re.IGNORECASE)
USED_BY_RE = re.compile(r";\s*Used by:\s*(.+)", re.IGNORECASE)
CONSUMER_SYMBOL_RE = re.compile(r"^[A-Z_][A-Za-z0-9_]*$")
CONNECTOR_RE = re.compile(r"\b(via|through)\b", re.IGNORECASE)
UNRESOLVED_LABEL_RE = re.compile(r"^L[0-9A-Fa-f]{4,5}$")
POINTER_TABLE_NAME_RE = re.compile(
    r"(PtrTable|PointerTable|PtrTbl|PtrList|PointerList|Pointers|Ptrs)", re.IGNORECASE
)
SKIP_PHRASES = (
    "no known",
    "no active",
    "no indexed",
    "retained as data",
    "unreferenced",
)
UNRESOLVED_INDIRECT_PREFIXES = (
    "the ",
    "exact ",
    "bank-local ",
)


def fail_usage() -> int:
    print(USAGE, file=sys.stderr)
    return 64


def sentence_prefix(text: str) -> str:
    return text.split(".", 1)[0].strip()


def split_symbols(text: str) -> list[str]:
    normalized = re.sub(r"\band\b", ",", text, flags=re.IGNORECASE)
    out: list[str] = []
    seen: set[str] = set()
    for part in normalized.split(","):
        candidate = part.strip()
        if CONSUMER_SYMBOL_RE.fullmatch(candidate) and candidate not in seen:
            out.append(candidate)
            seen.add(candidate)
    return out


def collect_used_by_annotations(asm_path: Path) -> list[dict[str, object]]:
    annotations: list[dict[str, object]] = []
    pending: list[tuple[int, str]] = []
    for lineno, raw in enumerate(asm_path.read_text(encoding="utf-8").splitlines(), start=1):
        stripped = raw.strip()
        used_by = USED_BY_RE.search(raw)
        if stripped.startswith(";"):
            if used_by:
                pending.append((lineno, used_by.group(1).strip()))
            continue

        label_match = GLOBAL_DEF_RE.match(raw) or EQU_DEF_RE.match(raw)
        if label_match:
            target = label_match.group(1)
            for comment_line, text in pending:
                annotations.append({
                    "target": target,
                    "line": comment_line,
                    "text": text,
                })
            pending = []
            continue

        if stripped:
            pending = []
    return annotations


def load_fresh_xref(asm_path: Path, xref_path: Path) -> dict[str, object]:
    if not xref_path.exists() or not xref_path.is_file():
        raise ContractError(f"xref file not found: {xref_path}")
    if xref_path.stat().st_mtime < asm_path.stat().st_mtime:
        raise ContractError(
            f"xref file is older than asm: {xref_path}; regenerate the shared xref"
        )
    return load_xref(xref_path)


def run_xasm_xref(asm_path: Path) -> dict[str, object]:
    with tempfile.TemporaryDirectory(prefix="used_by_xref.") as tmp:
        tmp_path = Path(tmp)
        out_path = tmp_path / "out.o"
        xref_path = tmp_path / "xref.json"
        cmd = [
            os.environ.get("XASM_BIN", "xasm"),
            "--pure-binary",
            "-o",
            str(out_path),
            f"--xref={xref_path}",
            "--xref-format=json",
            "--xref-include-owner=true",
            "--xref-data=true",
            str(asm_path),
        ]
        try:
            proc = subprocess.run(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                check=False,
            )
        except FileNotFoundError:
            print("error: xasm not found while running Used by xref check", file=sys.stderr)
            sys.exit(66)
        if proc.returncode != 0:
            print("FAIL: xasm xref generation failed for Used by check", file=sys.stderr)
            if proc.stdout:
                print(proc.stdout, file=sys.stderr, end="" if proc.stdout.endswith("\n") else "\n")
            if proc.stderr:
                print(proc.stderr, file=sys.stderr, end="" if proc.stderr.endswith("\n") else "\n")
            sys.exit(proc.returncode)
        return load_xref(xref_path)


def add_owner(owner_map: dict[str, set[str]], symbol: object, owner: object) -> None:
    if not isinstance(symbol, str) or not isinstance(owner, str) or not owner:
        return
    owner_map[symbol].add(owner)


def records(xref: dict[str, object], section: str) -> list[object]:
    value = xref.get(section)
    if not isinstance(value, list):
        raise ContractError(f"xref version 2 is missing {section}")
    return value


def build_reference_owners(xref: dict[str, object]) -> tuple[set[str], dict[str, set[str]]]:
    symbols = {
        item.get("name")
        for item in records(xref, "symbols")
        if isinstance(item, dict) and isinstance(item.get("name"), str)
    }
    owners: dict[str, set[str]] = defaultdict(set)
    for item in records(xref, "references"):
        if not isinstance(item, dict):
            continue
        add_owner(owners, item.get("symbol"), item.get("owner_routine"))
    for section in ("data_reads", "data_writes"):
        for item in records(xref, section):
            if not isinstance(item, dict):
                continue
            add_owner(owners, item.get("symbol"), item.get("owner_routine"))
            add_owner(owners, item.get("symbol"), item.get("routine"))
    return {s for s in symbols if isinstance(s, str)}, owners


def add_reference(
    refs: dict[str, set[str]], owner: object, symbol: object
) -> None:
    if not isinstance(owner, str) or not owner:
        return
    if not isinstance(symbol, str) or not symbol or owner == symbol:
        return
    refs[owner].add(symbol)


def build_xref_references(xref: dict[str, object]) -> dict[str, set[str]]:
    refs: dict[str, set[str]] = defaultdict(set)
    for item in records(xref, "references"):
        if not isinstance(item, dict):
            continue
        add_reference(refs, item.get("owner_routine"), item.get("symbol"))
    for index, item in enumerate(records(xref, "data_directive_references")):
        if not isinstance(item, dict):
            raise ContractError(f"data_directive_references[{index}] must be object")
        referenced_symbols = item.get("referenced_symbols")
        if not isinstance(referenced_symbols, list) or not all(
            isinstance(symbol, str) for symbol in referenced_symbols
        ):
            raise ContractError(
                f"data_directive_references[{index}].referenced_symbols must be list[str]"
            )
        for symbol in referenced_symbols:
            add_reference(refs, item.get("owner_symbol"), symbol)
    return refs


def reaches_through_symbolic_pointer_table(
    consumer: str,
    target: str,
    xref_refs: dict[str, set[str]],
) -> bool:
    """Return true for Consumer -> named pointer table -> Target xref edges.

    Ordinary reference owners prove the first edge. Data-directive owner_symbol
    provenance proves the second without assigning the table operand to a
    preceding routine or treating an arbitrary two-hop reference as executable.
    """

    consumer_refs = xref_refs.get(consumer, set())
    for table in consumer_refs:
        if not POINTER_TABLE_NAME_RE.search(table):
            continue
        if target in xref_refs.get(table, set()):
            return True
    return False


def first_symbol(text: str) -> str | None:
    match = re.search(r"\b([A-Za-z_][A-Za-z0-9_]*)\b", text)
    if not match:
        return None
    return match.group(1)


def is_unresolved_label(symbol: str) -> bool:
    return bool(UNRESOLVED_LABEL_RE.fullmatch(symbol))


def check_annotation(
    annotation: dict[str, object],
    symbols: set[str],
    owners: dict[str, set[str]],
    xref_refs: dict[str, set[str]],
    *,
    strict: bool,
) -> tuple[list[str], list[str], bool]:
    target = str(annotation["target"])
    line = int(annotation["line"])
    text = str(annotation["text"])
    sentence = sentence_prefix(text)
    lower_sentence = sentence.lower()
    if not sentence or any(phrase in lower_sentence for phrase in SKIP_PHRASES):
        return [], [], False

    connector = CONNECTOR_RE.search(sentence)
    producer_for_target: str | None = None
    if connector:
        lhs = sentence[: connector.start()].strip()
        rhs = sentence[connector.end() :].strip()
        consumers = split_symbols(lhs)
        if not consumers:
            if "prg banking" in rhs.lower():
                return [f"{line}: Used by comment for {target} names PRG banking but no concrete consumer symbol"], [], False
            return [], [], False
        producer = first_symbol(rhs)
        if producer and is_unresolved_label(producer):
            return [
                f"{line}: Used by comment for {target} cites unresolved producer label {producer}"
            ], [], False
        if not producer or producer not in symbols:
            if rhs.lower().startswith(UNRESOLVED_INDIRECT_PREFIXES):
                return [], [], False
            if "prg banking" in rhs.lower():
                return [f"{line}: Used by comment for {target} names PRG banking instead of a concrete producer symbol"], [], False
            return [], [], False
        producer_for_target = producer
        checked_symbol = producer
        context = f"{target} via {producer}"
    else:
        consumers = split_symbols(sentence)
        if not consumers:
            return [], [], False
        checked_symbol = target
        context = target

    failures: list[str] = []
    advisories: list[str] = []
    if producer_for_target:
        producer_refs = xref_refs.get(producer_for_target, set())
        if target not in producer_refs:
            rendered_refs = ", ".join(sorted(producer_refs)) or "none"
            # A through/via dispatcher commonly reaches the target indirectly --
            # a ZP pointer or other runtime dispatch the static xref cannot
            # follow -- so a missing proven edge is unverifiable, not necessarily
            # wrong. Advisory by default; hard only under --strict.
            msg = (
                f"{line}: Used by comment for {target} says through {producer_for_target}, "
                f"but {producer_for_target} does not reference {target}; "
                f"xref references are: {rendered_refs}"
            )
            (failures if strict else advisories).append(msg)
    actual_owners = owners.get(checked_symbol, set())
    for consumer in consumers:
        if is_unresolved_label(consumer):
            failures.append(
                f"{line}: Used by comment for {target} cites unresolved consumer label {consumer}"
            )
        elif consumer not in symbols:
            failures.append(
                f"{line}: Used by comment for {target} names unknown consumer symbol {consumer}"
            )
        else:
            pointer_table_edge = (
                producer_for_target is None
                and reaches_through_symbolic_pointer_table(consumer, target, xref_refs)
            )
            if consumer in actual_owners or pointer_table_edge:
                continue
            rendered_owners = ", ".join(sorted(actual_owners)) or "none"
            msg = (
                f"{line}: Used by comment for {context} names {consumer}, "
                f"but xref owners are: {rendered_owners}"
            )
            if strict:
                failures.append(msg)
            else:
                advisories.append(msg)
    return failures, advisories, True


def main(argv: list[str]) -> int:
    strict = False
    generate_xref = False
    args: list[str] = []
    for arg in argv[1:]:
        if arg == "--strict":
            strict = True
        elif arg == "--generate-xref":
            generate_xref = True
        elif arg.startswith("-"):
            return fail_usage()
        else:
            args.append(arg)
    if (generate_xref and len(args) != 1) or (not generate_xref and len(args) != 2):
        return fail_usage()
    asm_path = Path(args[0])
    if not asm_path.exists():
        print(f"error: asm file not found: {asm_path}", file=sys.stderr)
        return 1
    xref_path = Path(args[1]) if len(args) == 2 else None

    annotations = collect_used_by_annotations(asm_path)
    try:
        if generate_xref:
            xref = run_xasm_xref(asm_path)
        else:
            assert xref_path is not None
            xref = load_fresh_xref(asm_path, xref_path)
        symbols, owners = build_reference_owners(xref)
        xref_refs = build_xref_references(xref)
    except ContractError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 65

    failures: list[str] = []
    advisories: list[str] = []
    checked = 0
    for annotation in annotations:
        new_failures, new_advisories, was_checked = check_annotation(
            annotation,
            symbols,
            owners,
            xref_refs,
            strict=strict,
        )
        failures.extend(new_failures)
        advisories.extend(new_advisories)
        if was_checked:
            checked += 1

    if failures:
        print("FAIL: Used by xref annotations are stale or uncheckable:", file=sys.stderr)
        for failure in failures[:120]:
            print(f"{asm_path}:{failure}", file=sys.stderr)
        if len(failures) > 120:
            print(f"... {len(failures) - 120} more failures omitted", file=sys.stderr)
        return 2

    if strict:
        print(f"OK: Used by xref annotations are synchronized ({checked} strict claims checked)")
    else:
        if advisories:
            print("ADVISORY: Used by xref (unverifiable indirect dispatch or owner mismatch):", file=sys.stderr)
            for advisory in advisories[:40]:
                print(f"{asm_path}:{advisory}", file=sys.stderr)
            if len(advisories) > 40:
                print(f"... {len(advisories) - 40} more advisories omitted", file=sys.stderr)
        print(
            "OK: Used by hard-error scan passed "
            f"({checked} symbol-shaped claims parsed; strict owner matching is opt-in)"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
