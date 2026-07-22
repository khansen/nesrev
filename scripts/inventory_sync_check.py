#!/usr/bin/env python3
"""Validate generated inventory snapshots and raw-RAM owner references.

`refresh_inventory.sh` owns a handful of generated files under
`docs/reverse_engineering/inventory/`. This check regenerates those files into a
temporary directory and compares the tracked copies without mutating the
project. It also catches a separate ledger-drift class: `raw_ram_review.csv`
owner columns that still name routines that no longer exist after a rename.
"""
from __future__ import annotations

import csv
import difflib
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path


GENERATED_INVENTORY_FILES = (
    "constants_catalog.csv",
    "pointer_targets.csv",
    "embedded_pointer_targets.csv",
    "branch_literal_sites.csv",
    "unknowns.md",
)
RAW_RAM_OWNER_FIELDS = ("top_readers", "top_writers")
GLOBAL_LABEL_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*|L[0-9A-F]{4,5}):\s*(?:;.*)?$")
LOCAL_LABEL_RE = re.compile(r"^(@@[A-Za-z_][A-Za-z0-9_]*|@):\s*(?:;.*)?$")


def load_label_index(asm_file: Path) -> tuple[set[str], dict[str, set[str]]]:
    labels: set[str] = set()
    locals_by_global: dict[str, set[str]] = {}
    current_global: str | None = None
    for raw in asm_file.read_text(encoding="utf-8").splitlines():
        text = raw.strip()
        match = GLOBAL_LABEL_RE.match(text)
        if match:
            current_global = match.group(1)
            labels.add(current_global)
            continue
        local_match = LOCAL_LABEL_RE.match(text)
        if local_match and current_global:
            locals_by_global.setdefault(current_global, set()).add(local_match.group(1))
    return labels, locals_by_global


def owner_name_from_count_item(item: str) -> str | None:
    item = item.strip()
    if not item:
        return None
    owner_text, sep, count_text = item.rpartition(":")
    if not sep or not count_text.strip().isdigit():
        return None
    owner_text = owner_text.strip()
    if "::" in owner_text:
        owner_text = owner_text.split("::", 1)[0].strip()
    return owner_text or None


def raw_ram_owner_error(owner: str, labels: set[str], locals_by_global: dict[str, set[str]]) -> str | None:
    if owner in labels:
        return None
    if owner == "@":
        return None
    if owner.startswith("@@"):
        return (
            f"names unscoped local owner symbol {owner!r}; "
            "write local owners as Global@@local"
        )
    if "@@" in owner:
        global_owner, local_owner = owner.split("@@", 1)
        scoped_local = f"@@{local_owner}" if local_owner else ""
        if not global_owner or global_owner not in labels:
            return f"names unknown owner symbol {owner!r}"
        if not scoped_local or scoped_local not in locals_by_global.get(global_owner, set()):
            return f"names unknown scoped local owner symbol {owner!r}"
        return None
    return f"names unknown owner symbol {owner!r}"


def validate_raw_ram_owners(raw_ram_review: Path, asm_file: Path) -> list[str]:
    if not raw_ram_review.exists():
        return []

    labels, locals_by_global = load_label_index(asm_file)
    errors: list[str] = []
    with raw_ram_review.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        missing = [field for field in RAW_RAM_OWNER_FIELDS if field not in (reader.fieldnames or [])]
        if missing:
            errors.append(f"{raw_ram_review}: missing owner column(s): {', '.join(missing)}")
            return errors
        for row_index, row in enumerate(reader, start=2):
            if None in row:
                errors.append(f"{raw_ram_review}:{row_index}: row has too many columns")
                continue
            if (row.get("active") or "").strip().lower() != "yes":
                continue
            for field in RAW_RAM_OWNER_FIELDS:
                for item in (row.get(field) or "").split(","):
                    owner = owner_name_from_count_item(item)
                    if owner:
                        owner_error = raw_ram_owner_error(owner, labels, locals_by_global)
                    else:
                        owner_error = None
                    if owner_error:
                        addr = (row.get("addr_hex") or "<unknown address>").strip() or "<unknown address>"
                        errors.append(
                            f"{raw_ram_review}:{row_index}: {addr} {field} {owner_error}"
                        )
    return errors


def first_diff(actual: Path, expected: Path) -> str:
    actual_lines = actual.read_text(encoding="utf-8").splitlines(keepends=True)
    expected_lines = expected.read_text(encoding="utf-8").splitlines(keepends=True)
    diff = difflib.unified_diff(
        expected_lines,
        actual_lines,
        fromfile=f"expected/{expected.name}",
        tofile=str(actual),
        n=3,
    )
    return "".join(list(diff)[:80]).rstrip()


def validate_generated_inventory(
    project_slug: str,
    doc_root: Path,
    refresh_script: Path,
) -> list[str]:
    inv_dir = doc_root / "inventory"
    existing = [inv_dir / name for name in GENERATED_INVENTORY_FILES if (inv_dir / name).exists()]
    if not existing:
        return []

    errors: list[str] = []
    with tempfile.TemporaryDirectory(prefix="nesrev_inventory_sync_") as tmpdir:
        env = os.environ.copy()
        env["NESREV_INVENTORY_OUT_DIR"] = tmpdir
        result = subprocess.run(
            [str(refresh_script), project_slug],
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            check=False,
        )
        if result.returncode != 0:
            errors.append(
                f"error: could not regenerate inventory for sync check "
                f"(exit {result.returncode}); run {refresh_script} {project_slug}"
            )
            if result.stderr.strip():
                errors.append(result.stderr.strip())
            return errors

        generated_dir = Path(tmpdir)
        for actual in existing:
            expected = generated_dir / actual.name
            if not expected.exists():
                errors.append(f"error: generated inventory check did not produce {actual.name}")
                continue
            if actual.read_bytes() == expected.read_bytes():
                continue
            errors.append(
                f"error: generated inventory is out of sync: {actual}; "
                f"run {refresh_script} {project_slug}"
            )
            diff = first_diff(actual, expected)
            if diff:
                errors.append(diff)
    return errors


def main() -> int:
    if len(sys.argv) != 5:
        print(
            "usage: inventory_sync_check.py <project_slug> <asm_file> <doc_root> <refresh_script>",
            file=sys.stderr,
        )
        return 64

    project_slug = sys.argv[1]
    asm_file = Path(sys.argv[2])
    doc_root = Path(sys.argv[3])
    refresh_script = Path(sys.argv[4])

    errors: list[str] = []
    errors.extend(validate_generated_inventory(project_slug, doc_root, refresh_script))
    errors.extend(validate_raw_ram_owners(doc_root / "inventory" / "raw_ram_review.csv", asm_file))

    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1

    print("OK: project inventory ledgers are synchronized")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
