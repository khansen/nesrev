#!/usr/bin/env python3
"""Structural checker for SEMANTIC_CLAIMS.md.

This validates that semantic claims are *reviewable* and connected to real
symbols/docs. It deliberately does NOT try to prove the claims — evidence
quality remains a reviewer judgment. See the model and scope at
agent_playbook/QUALITY_REVIEW.md#semantic-claims.

Modes:
  --mode advisory   everything is a warning; exit 0 (legacy-safe default)
  --mode strict     missing file and structural errors fail (exit 2); a sparse
                    ledger with zero claims is allowed (pass-time validation)
  --mode maturity   strict, and additionally require at least one real claim
                    (gold-closeout gate for opted-in projects)

Usage:
  project_semantic_claims_check.py <asm_file> <semantic_claims_file> [--mode advisory|strict|maturity]
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

REQUIRED_FIELDS = [
    "Subject",
    "Kind",
    "Subsystem",
    "Claim",
    "Confidence",
    "Evidence",
    "Caveats",
    "Canonical docs",
]
ALLOWED_KIND = {
    "RAM/ZP field",
    "scoped overlay",
    "state machine",
    "state value",
    "data format",
    "pointer table",
    "routine contract",
    "subsystem",
    "other",
}
ALLOWED_CONFIDENCE = {"high", "medium", "inferred", "mechanical"}
EXTERNAL_SUBJECT = "External/reference-only"

FENCE_RE = re.compile(r"^\s*```")
CLAIM_HEADING_RE = re.compile(r"^##\s+Claim:\s*(\S.*?)\s*$")
H2_RE = re.compile(r"^##\s+")
LABEL_RE = re.compile(
    r"^(Subject|Kind|Subsystem|Claim|Confidence|Evidence|Caveats|Canonical docs):\s?(.*)$"
)
LIST_ITEM_RE = re.compile(r"^\s*-\s+(.*)$")
IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
LXXXX_RE = re.compile(r"^L[0-9A-F]{4,5}$")
PLACEHOLDER_RE = re.compile(r"^(State|Mode|Field|Page|Group|Arm)\d{1,4}$|^Addr[0-9A-Fa-f]{4}$")
BARE_RAW_RE = re.compile(r"^\$[0-9A-Fa-f]{1,4}$")
MD_LINK_RE = re.compile(r"\[[^\]]*\]\(([^)]+)\)")
NONE_VALUES = {"", "none", "-", "n/a", "na"}


def build_asm_symbols(asm_path: Path) -> set[str]:
    symbols: set[str] = set()
    if not asm_path.exists():
        return symbols
    for raw in asm_path.read_text(encoding="utf-8").splitlines():
        m = re.match(r"^(@{0,2}[A-Za-z_][A-Za-z0-9_]*):", raw)
        if m:
            symbols.add(m.group(1).lstrip("@"))
            symbols.add(m.group(1))
            continue
        m = re.match(r"^([A-Za-z_][A-Za-z0-9_]*)\s+\.EQU\b", raw, re.IGNORECASE)
        if m:
            symbols.add(m.group(1))
    return symbols


def strip_fenced(lines: list[str]) -> list[str]:
    out = []
    in_fence = False
    for line in lines:
        if FENCE_RE.match(line):
            in_fence = not in_fence
            continue
        if not in_fence:
            out.append(line)
    return out


def parse_claims(lines: list[str]):
    """Yield (slug, heading_line_no, block_lines) for each `## Claim:` block."""
    claims = []
    current = None
    for idx, line in enumerate(lines, start=1):
        m = CLAIM_HEADING_RE.match(line)
        if m:
            if current:
                claims.append(current)
            current = (m.group(1), idx, [])
            continue
        if H2_RE.match(line):
            # a non-claim h2 closes the current claim block
            if current:
                claims.append(current)
                current = None
            continue
        if current:
            current[2].append(line)
    if current:
        claims.append(current)
    return claims


def parse_fields(block_lines: list[str]):
    fields: dict[str, dict] = {}
    current = None
    for line in block_lines:
        m = LABEL_RE.match(line)
        if m:
            current = m.group(1)
            fields[current] = {"inline": m.group(2).strip(), "items": []}
            continue
        li = LIST_ITEM_RE.match(line)
        if li and current:
            fields[current]["items"].append(li.group(1).strip())
    return fields


def field_has_value(field: dict) -> bool:
    return bool(field.get("inline", "").strip()) or any(
        item.strip() for item in field.get("items", [])
    )


def caveat_is_substantive(field: dict) -> bool:
    values = [v for v in [field.get("inline", "")] + field.get("items", []) if v]
    for v in values:
        if v.strip().lower().rstrip(".") not in NONE_VALUES:
            return True
    return False


def validate(asm_path: Path, claims_path: Path, require_claims: bool = False) -> list[str]:
    errors: list[str] = []
    symbols = build_asm_symbols(asm_path)
    text = claims_path.read_text(encoding="utf-8")
    lines = strip_fenced(text.splitlines())
    claims = parse_claims(lines)

    if require_claims and not claims:
        errors.append(
            f"{claims_path}: no claims recorded; gold-closeout maturity requires "
            "at least one '## Claim:' (a sparse ledger is only allowed pass-time)"
        )

    seen_slugs: dict[str, int] = {}
    for slug, heading_no, block in claims:
        where = f"{claims_path}: claim '{slug}'"
        if slug in seen_slugs:
            errors.append(f"{where}: duplicate claim heading (also at line {seen_slugs[slug]})")
        seen_slugs[slug] = heading_no

        fields = parse_fields(block)
        missing = [
            f for f in REQUIRED_FIELDS
            if f not in fields or not field_has_value(fields[f])
        ]
        if missing:
            errors.append(f"{where}: missing required field(s): {', '.join(missing)}")

        kind = fields.get("Kind", {}).get("inline", "")
        if "Kind" in fields and kind not in ALLOWED_KIND:
            errors.append(f"{where}: invalid Kind {kind!r}")

        confidence = fields.get("Confidence", {}).get("inline", "")
        if "Confidence" in fields and confidence not in ALLOWED_CONFIDENCE:
            errors.append(f"{where}: invalid Confidence {confidence!r}")

        subject = fields.get("Subject", {}).get("inline", "")
        if "Subject" in fields:
            errors.extend(
                validate_subject(where, subject, confidence, fields, symbols)
            )

        if "Canonical docs" in fields:
            errors.extend(validate_canonical_docs(where, fields["Canonical docs"], claims_path))

    return errors


def validate_subject(where, subject, confidence, fields, symbols) -> list[str]:
    out = []
    if subject == EXTERNAL_SUBJECT:
        return out
    mechanical_exempt = confidence == "mechanical" and caveat_is_substantive(
        fields.get("Caveats", {})
    )
    if LXXXX_RE.match(subject):
        out.append(f"{where}: Subject is a raw LXXXX/LXXXXX label ({subject}); resolve it first")
        return out
    if PLACEHOLDER_RE.match(subject) or BARE_RAW_RE.match(subject):
        if not mechanical_exempt:
            out.append(
                f"{where}: placeholder/raw Subject {subject!r} requires "
                "Confidence: mechanical with a caveat explaining the exclusion"
            )
        return out
    if IDENT_RE.match(subject):
        if symbols and subject not in symbols:
            out.append(
                f"{where}: Subject {subject!r} not found in project ASM "
                "(use 'Subject: External/reference-only' if intentional)"
            )
    return out


def validate_canonical_docs(where, field: dict, claims_path: Path) -> list[str]:
    out = []
    base = claims_path.parent
    for item in field.get("items", []):
        targets = MD_LINK_RE.findall(item)
        if not targets:
            # bare token form: only treat as a local path if it ends in .md
            token = item.strip()
            if token.endswith(".md") and "/" not in token and " " not in token:
                targets = [token]
        for target in targets:
            target = target.split("#", 1)[0]
            if not target.endswith(".md"):
                continue
            if target.startswith(("http://", "https://")):
                continue
            if not (base / target).exists():
                out.append(f"{where}: Canonical docs link does not resolve: {target}")
    return out


def main() -> int:
    args = []
    mode = "advisory"
    invalid_args = False
    i = 1
    while i < len(sys.argv):
        arg = sys.argv[i]
        if arg == "--mode":
            if i + 1 >= len(sys.argv):
                invalid_args = True
                break
            mode = sys.argv[i + 1]
            i += 2
        elif arg.startswith("--mode="):
            mode = arg.split("=", 1)[1]
            i += 1
        elif arg.startswith("--"):
            invalid_args = True
            break
        else:
            args.append(arg)
            i += 1

    if invalid_args or len(args) != 2 or mode not in {"advisory", "strict", "maturity"}:
        print(
            "usage: project_semantic_claims_check.py <asm_file> "
            "<semantic_claims_file> [--mode advisory|strict|maturity]",
            file=sys.stderr,
        )
        return 64

    asm_path, claims_path = Path(args[0]), Path(args[1])
    fail_on_errors = mode in {"strict", "maturity"}

    if not claims_path.exists():
        msg = (
            f"SEMANTIC_CLAIMS.md not found: {claims_path}. New/opted-in projects "
            "must scaffold it; it may stay sparse until gold closeout."
        )
        if fail_on_errors:
            print(f"FAIL: {msg}", file=sys.stderr)
            return 2
        print(f"warn: {msg} (advisory; legacy project not opted in)")
        return 0

    errors = validate(asm_path, claims_path, require_claims=(mode == "maturity"))

    if not errors:
        print(f"OK: semantic-claims structure valid ({claims_path})")
        return 0

    if fail_on_errors:
        for e in errors:
            print(f"FAIL: {e}", file=sys.stderr)
        return 2
    for e in errors:
        print(f"warn: {e}")
    print("warn: semantic-claims issues are advisory for this project")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
