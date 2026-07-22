#!/usr/bin/env python3
"""Validate per-label data blob format dispositions.

This inventory closes the gap between "a data label has a comment" and "the
bytes under that label have been structurally reviewed." It is intentionally a
human disposition ledger: the checker can surface opaque-span candidates from
data_coverage.json, but the row evidence records the consumer proof, pointer
search result, extent/boundary proof, and whether the bytes were reflowed. A
row label may be exact or a glob pattern for repeated same-format spans.
"""

from __future__ import annotations

import argparse
import csv
import fnmatch
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


FIELDS = [
    "label",
    "disposition",
    "format",
    "artifact",
    "consumer_evidence",
    "pointer_evidence",
    "extent_evidence",
    "reflow_status",
    "notes",
]

VALID_DISPOSITIONS = {
    "not_yet_reviewed",
    "queued_static_pass",
    "decoded_format",
    "record_table",
    "pointer_table",
    "packed_stream",
    "bitmap_chr_graphics",
    "padding_or_fill",
    "known_unreferenced",
    "runtime_gated",
}

MATURITY_BLOCKING_DISPOSITIONS = {
    "not_yet_reviewed",
    "queued_static_pass",
}

STRUCTURAL_DISPOSITIONS = {
    "decoded_format",
    "record_table",
    "pointer_table",
    "packed_stream",
    "bitmap_chr_graphics",
}

VALID_REFLOW_STATUSES = {
    "not_reflowed",
    "reflowed",
    "split_and_reflowed",
    "not_applicable",
    "blocked_unknown_format",
}

MATURITY_BLOCKING_REFLOW_STATUSES = {
    "not_reflowed",
    "blocked_unknown_format",
}

LABEL_PATTERN_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_*\?\[\]!\-]*$")
OPAQUE_NAME_RE = re.compile(r"(blob|payload|bytes|image|stream|block)", re.IGNORECASE)


@dataclass(frozen=True)
class Candidate:
    label: str
    size: int
    reasons: tuple[str, ...]


def error(message: str) -> None:
    print(f"data_blob_dispositions_check: {message}", file=sys.stderr)


def info(message: str) -> None:
    print(f"data_blob_dispositions_check: {message}")


def parse_int(value: Any) -> int | None:
    if isinstance(value, int):
        return value
    if not isinstance(value, str):
        return None
    value = value.strip()
    if not value:
        return None
    try:
        return int(value, 0)
    except ValueError:
        return None


def artifact_paths(raw: str) -> list[str]:
    return [part.strip() for part in raw.split(";") if part.strip()]


def artifact_file_part(raw: str) -> str:
    return raw.split("#", 1)[0].strip()


def validate_artifact(path: Path, doc_root: Path, row_num: int, artifact: str) -> bool:
    ok = True
    for part in artifact_paths(artifact):
        file_part = artifact_file_part(part)
        if not file_part:
            error(f"{path}:{row_num}: artifact '{part}' has no file path")
            ok = False
            continue
        candidate = (doc_root / file_part).resolve()
        if not candidate.exists():
            error(f"{path}:{row_num}: artifact does not exist relative to DOC_ROOT: {file_part}")
            ok = False
    return ok


def read_rows(path: Path) -> tuple[list[dict[str, str]], bool]:
    try:
        with path.open("r", encoding="utf-8", newline="") as handle:
            reader = csv.DictReader(handle)
            if reader.fieldnames != FIELDS:
                error(
                    f"{path}: invalid header {reader.fieldnames!r}; "
                    f"expected {','.join(FIELDS)}"
                )
                return [], False
            return list(reader), True
    except OSError as exc:
        error(f"{path}: {exc}")
        return [], False


def iter_dict_records(value: Any) -> Iterable[dict[str, Any]]:
    if isinstance(value, list):
        for item in value:
            if isinstance(item, dict):
                yield item
        return
    if isinstance(value, dict):
        for preferred in ("data_labels", "labels", "records", "spans"):
            nested = value.get(preferred)
            if isinstance(nested, list):
                yield from iter_dict_records(nested)
                return
        for nested in value.values():
            if isinstance(nested, list):
                for item in nested:
                    if isinstance(item, dict):
                        yield item


def read_coverage_records(path: Path | None) -> tuple[list[dict[str, Any]], bool]:
    if path is None:
        return [], False
    if not path.exists():
        return [], False
    try:
        return list(iter_dict_records(json.loads(path.read_text(encoding="utf-8")))), True
    except (OSError, json.JSONDecodeError) as exc:
        error(f"{path}: failed to read data coverage JSON: {exc}")
        return [], False


def declared_size(record: dict[str, Any]) -> int | None:
    for key in ("declared_size", "size", "byte_count"):
        parsed = parse_int(record.get(key))
        if parsed is not None:
            return parsed
    start = parse_int(record.get("declared_start"))
    end = parse_int(record.get("declared_end_exclusive"))
    if start is not None and end is not None and end >= start:
        return end - start
    return None


def candidate_label(record: dict[str, Any]) -> str | None:
    for key in ("label", "name", "symbol", "data_label"):
        value = record.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return None


def find_candidates(records: list[dict[str, Any]], min_size: int) -> list[Candidate]:
    candidates: list[Candidate] = []
    for record in records:
        label = candidate_label(record)
        size = declared_size(record)
        if label is None or size is None or size < min_size:
            continue
        if label.endswith("End"):
            continue

        uncovered_size = parse_int(record.get("uncovered_size")) or 0
        access_count = parse_int(record.get("access_count")) or 0
        reasons: list[str] = []
        if OPAQUE_NAME_RE.search(label):
            reasons.append("opaque-name")
        if uncovered_size >= min_size:
            reasons.append("undercovered-span")
        if access_count == 0 and size >= min_size:
            reasons.append("unreferenced-span")
        if record.get("has_indexed_accesses_without_exact_coverage") is True:
            reasons.append("indexed-without-exact-coverage")

        if reasons:
            candidates.append(Candidate(label=label, size=size, reasons=tuple(sorted(set(reasons)))))
    return sorted(candidates, key=lambda item: item.label)


def validate_rows(path: Path, doc_root: Path, rows: list[dict[str, str]], mode: str) -> tuple[bool, list[str]]:
    ok = True
    seen: set[str] = set()
    label_patterns: list[str] = []

    for idx, row in enumerate(rows, start=2):
        if None in row:
            error(f"{path}:{idx}: too many CSV columns; quote note or evidence text that contains commas")
            ok = False

        label = (row.get("label") or "").strip()
        disposition = (row.get("disposition") or "").strip()
        format_name = (row.get("format") or "").strip()
        artifact = (row.get("artifact") or "").strip()
        consumer_evidence = (row.get("consumer_evidence") or "").strip()
        pointer_evidence = (row.get("pointer_evidence") or "").strip()
        extent_evidence = (row.get("extent_evidence") or "").strip()
        reflow_status = (row.get("reflow_status") or "").strip()

        if not label:
            error(f"{path}:{idx}: label is required")
            ok = False
        elif not LABEL_PATTERN_RE.match(label):
            error(f"{path}:{idx}: label must be an asm global label or glob pattern: {label}")
            ok = False
        elif label in seen:
            error(f"{path}:{idx}: duplicate label: {label}")
            ok = False
        else:
            seen.add(label)
            label_patterns.append(label)

        if disposition not in VALID_DISPOSITIONS:
            error(
                f"{path}:{idx}: invalid disposition '{disposition}'; "
                f"expected one of {', '.join(sorted(VALID_DISPOSITIONS))}"
            )
            ok = False

        if disposition not in MATURITY_BLOCKING_DISPOSITIONS:
            if not consumer_evidence:
                error(f"{path}:{idx}: consumer_evidence is required for disposition '{disposition}'")
                ok = False
            if not pointer_evidence:
                error(f"{path}:{idx}: pointer_evidence is required for disposition '{disposition}'")
                ok = False
            if not extent_evidence:
                error(f"{path}:{idx}: extent_evidence is required for disposition '{disposition}'")
                ok = False

        if disposition in STRUCTURAL_DISPOSITIONS:
            if not format_name:
                error(f"{path}:{idx}: structural disposition '{disposition}' requires a format")
                ok = False
            if not artifact:
                error(f"{path}:{idx}: structural disposition '{disposition}' requires an artifact")
                ok = False
        if artifact and not validate_artifact(path, doc_root, idx, artifact):
            ok = False

        if not reflow_status:
            error(f"{path}:{idx}: reflow_status is required")
            ok = False
        elif reflow_status not in VALID_REFLOW_STATUSES:
            error(
                f"{path}:{idx}: invalid reflow_status '{reflow_status}'; "
                f"expected one of {', '.join(sorted(VALID_REFLOW_STATUSES))}"
            )
            ok = False

        if mode == "maturity":
            if disposition in MATURITY_BLOCKING_DISPOSITIONS:
                error(f"{path}:{idx}: maturity cannot leave label '{label}' as {disposition}")
                ok = False
            if (
                disposition in STRUCTURAL_DISPOSITIONS
                and reflow_status in MATURITY_BLOCKING_REFLOW_STATUSES
            ):
                error(
                    f"{path}:{idx}: maturity requires proven structure for '{label}' "
                    "to be reflowed, split_and_reflowed, or not_applicable"
                )
                ok = False

    return ok, label_patterns


def validate(
    path: Path,
    doc_root: Path,
    data_coverage: Path | None,
    min_size: int,
    mode: str,
    required: bool,
) -> int:
    if not path.exists():
        if required:
            error(f"required data-blob disposition inventory missing: {path}")
            return 1
        return 0

    rows, ok = read_rows(path)
    if not ok:
        return 1

    rows_ok, dispositioned_patterns = validate_rows(path, doc_root, rows, mode)
    ok = ok and rows_ok

    records, coverage_available = read_coverage_records(data_coverage)
    candidates = find_candidates(records, min_size) if coverage_available else []
    if coverage_available:
        info(
            f"candidate_spans={len(candidates)} disposition_rows={len(rows)} "
            f"min_size={min_size}"
        )
    elif mode == "maturity" and required:
        error("maturity requires data coverage candidates; run project-pass-prep before closeout")
        ok = False

    missing = [
        candidate
        for candidate in candidates
        if not any(fnmatch.fnmatchcase(candidate.label, pattern) for pattern in dispositioned_patterns)
    ]
    if missing:
        summary = ", ".join(
            f"{item.label}({item.size}:{'/'.join(item.reasons)})" for item in missing[:20]
        )
        if len(missing) > 20:
            summary += f", ... +{len(missing) - 20} more"
        message = f"{path}: {len(missing)} candidate data spans lack blob dispositions: {summary}"
        if mode == "maturity":
            error(message)
            ok = False
        else:
            print(f"warn: {message}", file=sys.stderr)

    return 0 if ok else 1


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inventory", type=Path)
    parser.add_argument("--doc-root", type=Path, required=True)
    parser.add_argument("--data-coverage", type=Path)
    parser.add_argument("--min-size", type=int, default=12)
    parser.add_argument("--mode", choices=["process", "maturity"], default="process")
    parser.add_argument("--required", action="store_true")
    args = parser.parse_args(argv)

    return validate(
        path=args.inventory,
        doc_root=args.doc_root,
        data_coverage=args.data_coverage,
        min_size=args.min_size,
        mode=args.mode,
        required=args.required,
    )


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
