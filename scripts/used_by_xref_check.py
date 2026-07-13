#!/usr/bin/env python3
"""Validate mechanically checkable `; Used by:` declaration comments.

This is intentionally narrow: it checks comments that name concrete asm
symbols as consumers, and it skips broad prose-only ownership descriptions.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
import tempfile
from collections import defaultdict
from pathlib import Path


USAGE = "usage: used_by_xref_check.py [--strict] <asm_file> [xref_json]"
GLOBAL_DEF_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*):")
EQU_DEF_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s+\.EQU\b", re.IGNORECASE)
USED_BY_RE = re.compile(r";\s*Used by:\s*(.+)", re.IGNORECASE)
SYMBOL_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
CONSUMER_SYMBOL_RE = re.compile(r"^[A-Z_][A-Za-z0-9_]*$")
CONNECTOR_RE = re.compile(r"\b(via|through)\b", re.IGNORECASE)
SYMBOL_TOKEN_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_]*\b")
UNRESOLVED_LABEL_RE = re.compile(r"^L[0-9A-Fa-f]{4,5}$")
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


def strip_comment(text: str) -> str:
    return text.split(";", 1)[0]


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


def load_cached_xref(asm_path: Path, xref_path: Path | None) -> dict[str, object] | None:
    if xref_path is None or not xref_path.exists() or not xref_path.is_file():
        return None
    if xref_path.stat().st_mtime < asm_path.stat().st_mtime:
        return None
    return json.loads(xref_path.read_text(encoding="utf-8"))


def run_xasm_xref(asm_path: Path) -> dict[str, object]:
    with tempfile.TemporaryDirectory(prefix="used_by_xref.") as tmp:
        tmp_path = Path(tmp)
        out_path = tmp_path / "out.o"
        xref_path = tmp_path / "xref.json"
        cmd = [
            "xasm",
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
        return json.loads(xref_path.read_text(encoding="utf-8"))


def add_owner(owner_map: dict[str, set[str]], symbol: object, owner: object) -> None:
    if not isinstance(symbol, str) or not isinstance(owner, str) or not owner:
        return
    owner_map[symbol].add(owner)


def build_reference_owners(xref: dict[str, object]) -> tuple[set[str], dict[str, set[str]]]:
    symbols = {
        item.get("name")
        for item in xref.get("symbols", [])
        if isinstance(item, dict) and isinstance(item.get("name"), str)
    }
    owners: dict[str, set[str]] = defaultdict(set)
    for item in xref.get("references", []):
        if not isinstance(item, dict):
            continue
        add_owner(owners, item.get("symbol"), item.get("owner_routine"))
    for section in ("data_reads", "data_writes"):
        for item in xref.get(section, []):
            if not isinstance(item, dict):
                continue
            add_owner(owners, item.get("symbol"), item.get("owner_routine"))
            add_owner(owners, item.get("symbol"), item.get("routine"))
    return {s for s in symbols if isinstance(s, str)}, owners


def build_source_references(asm_path: Path, symbols: set[str]) -> dict[str, set[str]]:
    refs: dict[str, set[str]] = defaultdict(set)
    owner = ""
    for raw in asm_path.read_text(encoding="utf-8").splitlines():
        code = strip_comment(raw)
        label_match = GLOBAL_DEF_RE.match(code)
        equ_match = EQU_DEF_RE.match(code)
        if label_match:
            owner = label_match.group(1)
            code = code[label_match.end() :]
        elif equ_match:
            owner = equ_match.group(1)
            code = code[equ_match.end() :]
        elif not code.strip():
            continue
        if not owner:
            continue
        for match in SYMBOL_TOKEN_RE.finditer(code):
            symbol = match.group(0)
            if symbol in symbols and symbol != owner:
                refs[owner].add(symbol)
    return refs


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
    source_refs: dict[str, set[str]],
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
        producer_refs = source_refs.get(producer_for_target, set())
        if target not in producer_refs:
            rendered_refs = ", ".join(sorted(producer_refs)) or "none"
            # A through/via dispatcher commonly reaches the target indirectly --
            # a jump table, pointer table, or ZP pointer the static xref cannot
            # follow -- so a missing *direct* reference is unverifiable, not
            # necessarily wrong. Advisory by default; hard only under --strict.
            msg = (
                f"{line}: Used by comment for {target} says through {producer_for_target}, "
                f"but {producer_for_target} does not reference {target}; "
                f"source references are: {rendered_refs}"
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
        elif consumer not in actual_owners:
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
    args = argv[1:]
    if args and args[0] == "--strict":
        strict = True
        args = args[1:]
    if len(args) not in (1, 2):
        return fail_usage()
    asm_path = Path(args[0])
    if not asm_path.exists():
        print(f"error: asm file not found: {asm_path}", file=sys.stderr)
        return 1
    xref_path = Path(args[1]) if len(args) == 2 else None

    annotations = collect_used_by_annotations(asm_path)
    xref = load_cached_xref(asm_path, xref_path) or run_xasm_xref(asm_path)
    symbols, owners = build_reference_owners(xref)
    source_refs = build_source_references(asm_path, symbols)

    failures: list[str] = []
    advisories: list[str] = []
    checked = 0
    for annotation in annotations:
        new_failures, new_advisories, was_checked = check_annotation(
            annotation,
            symbols,
            owners,
            source_refs,
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
