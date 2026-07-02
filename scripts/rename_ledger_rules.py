#!/usr/bin/env python3
"""Shared validation rules for reverse-engineering rename ledgers."""

from __future__ import annotations

import re


def valid_old_name_shape(name: str) -> bool:
    """Return true when a renames.csv old_name is an accepted source key."""

    if re.fullmatch(r"raw_\$[0-9A-Fa-f]{1,4}", name or ""):
        return True
    if re.fullmatch(r"raw_[a-z0-9]+(?:_[a-z0-9]+)+", name or ""):
        return True
    if re.fullmatch(r"@@[A-Za-z][A-Za-z0-9_]*", name or ""):
        return True
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name or "") and re.search(r"[A-Z]", name or ""):
        return True
    return False
