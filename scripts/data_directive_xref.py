#!/usr/bin/env python3
"""Shared validation and classification for xasm JSON xref version 2."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any


TARGET_TYPES = {
    "code": (
        "code_pointer",
        "high confidence",
        "auto-classified from target label leading instruction",
    ),
    "data": (
        "data_pointer",
        "high confidence",
        "auto-classified from target label leading data directive",
    ),
    "equate": (
        "data_pointer",
        "high confidence",
        "auto-classified from target label leading data directive",
    ),
}


class ContractError(ValueError):
    pass


def load_xref(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise ContractError(f"xref file not found: {path}") from exc
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise ContractError(f"could not read xref JSON {path}: {exc}") from exc

    if not isinstance(payload, dict):
        raise ContractError(f"xref root must be an object: {path}")
    version = payload.get("version")
    if version != "2":
        raise ContractError(
            f"xref schema version 2 required, got {version!r}; "
            "use the lockstep xasm data-directive-reference build"
        )
    records = payload.get("data_directive_references")
    if not isinstance(records, list):
        raise ContractError("xref version 2 is missing data_directive_references")
    return payload


def require(record: dict[str, Any], field: str, expected: type, index: int) -> Any:
    value = record.get(field)
    if not isinstance(value, expected) or (expected is int and isinstance(value, bool)):
        raise ContractError(
            f"data_directive_references[{index}].{field} must be "
            f"{expected.__name__}"
        )
    return value


def pointer_metadata(
    record: dict[str, Any], index: int, unknown_note: str
) -> tuple[str, str, str]:
    kind = record.get("target_kind", "unknown")
    if kind == "unknown":
        return "unknown_pointer", "inferred", unknown_note
    try:
        return TARGET_TYPES[kind]
    except (KeyError, TypeError) as exc:
        raise ContractError(
            f"data_directive_references[{index}].target_kind has unsupported value "
            f"{kind!r}"
        ) from exc
