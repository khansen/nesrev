#!/usr/bin/env python3
"""Validate the project data-format disposition inventory.

The inventory is a reviewer worklist, not an inference engine. New projects
start with one row per common NES data family and must disposition each row
before maturity: documented, absent/not applicable, or runtime-gated with the
evidence needed to close it.
"""

from __future__ import annotations

import argparse
import csv
import re
import sys
from pathlib import Path


FIELDS = ["family", "disposition", "artifact", "evidence"]

VALID_DISPOSITIONS = {
    "not_yet_reviewed",
    "queued_static_pass",
    "documented",
    "absent_not_applicable",
    "runtime_gated",
}

MATURITY_BLOCKING_DISPOSITIONS = {
    "not_yet_reviewed",
    "queued_static_pass",
}

CANONICAL_FAMILIES = [
    "levels_rooms_maps",
    "objects_actors_enemies_hazards",
    "items_pickups_powerups",
    "projectiles_collision",
    "behavior_state_movement_animation",
    "metasprites_sprite_animation",
    "graphics_tiles_chr_nametables",
    "ppu_packet_update_streams",
    "audio_music_jingles",
    "audio_sfx_cues",
    "password_save_progression",
]

FAMILY_RE = re.compile(r"^[a-z0-9_]+$")


def error(message: str) -> None:
    print(f"data_format_targets_check: {message}", file=sys.stderr)


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


def validate(path: Path, doc_root: Path, mode: str, required: bool) -> int:
    if not path.exists():
        if required:
            error(f"required data-format target inventory missing: {path}")
            return 1
        return 0

    rows, ok = read_rows(path)
    if not ok:
        return 1
    if not rows:
        error(f"{path}: inventory has no target rows")
        return 1

    seen: set[str] = set()
    families: set[str] = set()
    for idx, row in enumerate(rows, start=2):
        if None in row:
            error(f"{path}:{idx}: too many CSV columns; quote evidence text that contains commas")
            ok = False
        family = (row.get("family") or "").strip()
        disposition = (row.get("disposition") or "").strip()
        artifact = (row.get("artifact") or "").strip()
        evidence = (row.get("evidence") or "").strip()

        if not family:
            error(f"{path}:{idx}: family is required")
            ok = False
        elif not FAMILY_RE.match(family):
            error(f"{path}:{idx}: family must match [a-z0-9_]+: {family}")
            ok = False
        elif family in seen:
            error(f"{path}:{idx}: duplicate family: {family}")
            ok = False
        else:
            seen.add(family)
            families.add(family)

        if disposition not in VALID_DISPOSITIONS:
            error(
                f"{path}:{idx}: invalid disposition '{disposition}'; "
                f"expected one of {', '.join(sorted(VALID_DISPOSITIONS))}"
            )
            ok = False
        if not evidence:
            error(f"{path}:{idx}: evidence is required")
            ok = False

        if disposition == "documented" and not artifact:
            error(f"{path}:{idx}: documented rows require an artifact")
            ok = False
        if disposition == "absent_not_applicable" and artifact:
            error(f"{path}:{idx}: absent_not_applicable rows must leave artifact empty")
            ok = False
        if artifact and not validate_artifact(path, doc_root, idx, artifact):
            ok = False

        if mode == "maturity" and disposition in MATURITY_BLOCKING_DISPOSITIONS:
            error(
                f"{path}:{idx}: maturity cannot leave family '{family}' "
                f"as {disposition}"
            )
            ok = False

    if required:
        missing = sorted(set(CANONICAL_FAMILIES) - families)
        if missing:
            error(f"{path}: missing canonical target families: {', '.join(missing)}")
            ok = False

    return 0 if ok else 1


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inventory", type=Path)
    parser.add_argument("--doc-root", type=Path, required=True)
    parser.add_argument("--mode", choices=["process", "maturity"], default="process")
    parser.add_argument("--required", action="store_true")
    args = parser.parse_args(argv)

    return validate(
        path=args.inventory,
        doc_root=args.doc_root,
        mode=args.mode,
        required=args.required,
    )


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
