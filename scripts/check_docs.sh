#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 4 || $# -gt 5 ]]; then
  echo "usage: $0 <asm_file> <doc_root> <systems_doc> <warn_baseline_file> [recovery_status]" >&2
  echo "(invoke via 'make project-docs-check PROJECT=<slug>' rather than directly)" >&2
  exit 64
fi

ASM_FILE="$1"
DOC_ROOT="$2"
SYSTEMS_DOC="$3"
WARN_BASELINE_FILE="$4"
RECOVERY_STATUS="${5:-legacy}"
TMPDIR_CHECK_DOCS="$(mktemp -d)"
trap 'rm -rf "${TMPDIR_CHECK_DOCS}"' EXIT

if ! command -v rg >/dev/null 2>&1; then
  echo "error: rg not found in PATH" >&2
  exit 1
fi

if [[ ! -f "${ASM_FILE}" ]]; then
  echo "error: asm file not found: ${ASM_FILE}" >&2
  exit 1
fi

if [[ ! -f "${SYSTEMS_DOC}" ]]; then
  echo "error: systems doc not found: ${SYSTEMS_DOC}" >&2
  exit 1
fi

if [[ ! -d "${DOC_ROOT}" ]]; then
  echo "error: docs root not found: ${DOC_ROOT}" >&2
  exit 1
fi

if [[ ! -f "${WARN_BASELINE_FILE}" ]]; then
  echo "error: warning baseline file not found: ${WARN_BASELINE_FILE}" >&2
  exit 1
fi

if [[ ! -f "${DOC_ROOT}/QUICK_REFERENCE.md" ]]; then
  echo "error: quick reference doc not found: ${DOC_ROOT}/QUICK_REFERENCE.md" >&2
  exit 1
fi

RENAMES_FILE="${DOC_ROOT}/inventory/renames.csv"
RAW_RAM_REVIEW_FILE="${DOC_ROOT}/inventory/raw_ram_review.csv"

if [[ ! -f "${RENAMES_FILE}" ]]; then
  echo "error: renames ledger not found: ${RENAMES_FILE}" >&2
  exit 1
fi

DOC_FILES=("${SYSTEMS_DOC}" "${DOC_ROOT}"/*.md)
ASM_BASENAME="$(basename "${ASM_FILE}")"
ASM_BASENAME_RE="$(
  printf '%s\n' "${ASM_BASENAME}" | sed -E 's/[][(){}.^$*+?|\\]/\\&/g'
)"
LINE_REF_RE="${ASM_BASENAME_RE}:[0-9]+"

echo "[1/8] Checking renames.csv structure"
python3 - "${RENAMES_FILE}" <<'PY'
import csv
import sys
from pathlib import Path

path = Path(sys.argv[1])
expected = ["old_name", "new_name", "reason", "confidence", "pass_id"]

with path.open("r", encoding="utf-8", newline="") as f:
    reader = csv.DictReader(f)
    if reader.fieldnames != expected:
        print("FAIL: renames.csv header mismatch", file=sys.stderr)
        print(f"expected: {expected}", file=sys.stderr)
        print(f"actual:   {reader.fieldnames}", file=sys.stderr)
        sys.exit(2)
    for idx, row in enumerate(reader, start=2):
        if None in row:
            print(f"FAIL: renames.csv row {idx} has too many columns", file=sys.stderr)
            print(row, file=sys.stderr)
            sys.exit(2)
        missing = [key for key in expected if row.get(key, "").strip() == ""]
        if missing:
            print(f"FAIL: renames.csv row {idx} has empty required fields: {', '.join(missing)}", file=sys.stderr)
            print(row, file=sys.stderr)
            sys.exit(2)
        try:
            int(row["pass_id"])
        except ValueError:
            print(f"FAIL: renames.csv row {idx} has non-integer pass_id: {row['pass_id']!r}", file=sys.stderr)
            print(row, file=sys.stderr)
            sys.exit(2)
print("OK: renames.csv structure is valid")
PY

echo "[2/8] Checking raw_ram_review.csv structure (if present)"
if [[ -f "${RAW_RAM_REVIEW_FILE}" ]]; then
  python3 - "${RAW_RAM_REVIEW_FILE}" <<'PY'
import csv
import sys
from pathlib import Path

path = Path(sys.argv[1])
expected = [
    "addr_hex",
    "status",
    "proposed_symbol",
    "notes",
    "last_pass_reviewed",
    "active",
    "operand_count",
    "distinct_owner_count",
    "read_count",
    "write_count",
    "top_readers",
    "top_writers",
]
allowed_status = {"candidate", "unreviewed", "deferred", "revisit", "not_semantic_yet", "symbolized"}
allowed_active = {"yes", "no", ""}

with path.open("r", encoding="utf-8", newline="") as f:
    reader = csv.DictReader(f)
    if reader.fieldnames != expected:
        print("FAIL: raw_ram_review.csv header mismatch", file=sys.stderr)
        print(f"expected: {expected}", file=sys.stderr)
        print(f"actual:   {reader.fieldnames}", file=sys.stderr)
        sys.exit(2)
    for idx, row in enumerate(reader, start=2):
        if None in row:
            print(f"FAIL: raw_ram_review.csv row {idx} has too many columns", file=sys.stderr)
            print(row, file=sys.stderr)
            sys.exit(2)
        if (row.get("status") or "").strip() not in allowed_status:
            print(f"FAIL: raw_ram_review.csv row {idx} has invalid status: {row.get('status')!r}", file=sys.stderr)
            print(row, file=sys.stderr)
            sys.exit(2)
        if (row.get("active") or "").strip() not in allowed_active:
            print(f"FAIL: raw_ram_review.csv row {idx} has invalid active value: {row.get('active')!r}", file=sys.stderr)
            print(row, file=sys.stderr)
            sys.exit(2)
        pass_value = (row.get("last_pass_reviewed") or "").strip()
        if pass_value:
            try:
                int(pass_value)
            except ValueError:
                print(f"FAIL: raw_ram_review.csv row {idx} has non-integer last_pass_reviewed: {pass_value!r}", file=sys.stderr)
                print(row, file=sys.stderr)
                sys.exit(2)
print("OK: raw_ram_review.csv structure is valid")
PY
else
  echo "OK: raw_ram_review.csv not present for this project"
fi

echo "[3/8] Checking for stale line-based asm references"
if rg -n "${LINE_REF_RE}" "${DOC_FILES[@]}" >"${TMPDIR_CHECK_DOCS}/line_refs.out"; then
  echo "FAIL: stale line-number references found:" >&2
  cat "${TMPDIR_CHECK_DOCS}/line_refs.out" >&2
  exit 2
else
  echo "OK: no ${ASM_BASENAME}:<line> references in docs"
fi

echo "[4/8] Checking systems-doc maturity hygiene"
systems_fail=0
if rg -n 'L[0-9A-F]{4}' "${SYSTEMS_DOC}" >"${TMPDIR_CHECK_DOCS}/systems_lxxxx.out"; then
  echo "FAIL: systems doc contains unresolved LXXXX labels:" >&2
  cat "${TMPDIR_CHECK_DOCS}/systems_lxxxx.out" >&2
  systems_fail=1
fi
if rg -n -i '\b(future pass|next pass|queued for (a )?(future|later)|most likely|to be revisited|candidate for a future)\b' \
  "${SYSTEMS_DOC}" >"${TMPDIR_CHECK_DOCS}/systems_planning.out"; then
  echo "FAIL: systems doc contains provisional/future-pass planning:" >&2
  cat "${TMPDIR_CHECK_DOCS}/systems_planning.out" >&2
  systems_fail=1
fi
if [[ ${systems_fail} -ne 0 ]]; then
  echo "Move provisional findings to WORKING_NOTES.md or process artifacts." >&2
  exit 2
fi
echo "OK: systems doc contains no unresolved labels or future-pass planning"

echo "[5/8] Checking for scaffold placeholder support docs"
python3 - "${DOC_ROOT}" "${RECOVERY_STATUS}" "${WARN_BASELINE_FILE}" <<'PY'
import sys
from pathlib import Path

doc_root = Path(sys.argv[1])
recovery_status = sys.argv[2]
warn_baseline = Path(sys.argv[3])

placeholder_patterns = {
    "ONBOARDING.md": [
        "Status: scaffolded; update this snapshot with ROM/header details during intake.",
        "Status: intake baseline captured; replace with project-specific snapshot during first pass.",
        "Status: scaffolded; intake gates have not completed.",
        "Recovery controls: pending discovery before intake.",
    ],
    "PARITY_GAPS.md": [
        "Record the current parity/documentation state and the highest-value remaining\nwork for this project.",
        "Fresh scaffold: update this file after `make project-intake PROJECT=<slug>`.",
        "Record current parity state, warning baseline state, and the highest-value remaining work.",
        "Procedure documentation is still at starter state.",
        "Data declaration documentation is still at starter state.",
    ],
    "ACTOR_ENUMS.md": [
        "Document actor states/actions/kinds with confidence notes.",
    ],
}

# The stale pass-0 note is part of the new scaffold lifecycle. Existing
# projects predate that contract and remain valid until explicitly upgraded.
if recovery_status != "legacy":
    placeholder_patterns["PROGRESS_SCORECARD.md"] = [
        "Initial intake; run `project-inventory` and KPI scripts to seed values.",
    ]

failures = []
for name, patterns in placeholder_patterns.items():
    path = doc_root / name
    if not path.exists():
        continue
    text = path.read_text(encoding="utf-8")
    for pattern in patterns:
        if pattern in text:
            failures.append(f"{path}: contains scaffold/stale placeholder text: {pattern!r}")
            break

for lineno, raw in enumerate(warn_baseline.read_text(encoding="utf-8").splitlines(), start=1):
    line = raw.strip()
    if not line or line.startswith("#"):
        continue
    if "REVIEW REQUIRED" in line:
        failures.append(
            f"{warn_baseline}:{lineno}: warning baseline still has auto-seed rationale"
        )

if failures:
    print("FAIL: placeholder support docs detected:", file=sys.stderr)
    for line in failures:
        print(line, file=sys.stderr)
    sys.exit(2)

print("OK: no scaffold placeholder support docs detected")
PY

echo "[6/8] Checking local .md references resolve"
python3 - "${DOC_ROOT}" <<'PY'
import re
import sys
from pathlib import Path

doc_root = Path(sys.argv[1])

# Bare same-directory .md filenames (no slash). Three syntactic forms.
BACKTICK_RE = re.compile(r"`([A-Z][A-Za-z0-9_]*\.md)`")
MDLINK_RE   = re.compile(r"\[[^\]]*\]\(([A-Z][A-Za-z0-9_]*\.md)(?:#[^)]*)?\)")
LISTITEM_RE = re.compile(r"^-\s+([A-Z][A-Za-z0-9_]*\.md)\s*$")

# Files that live outside DOC_ROOT (other tree locations).
EXTERNAL = {"AGENTS.md", "TERMINOLOGY_CROSSWALK.md", "MANUAL_TERMS.md"}
# Sources to skip entirely (intentionally historical / append-only).
SKIP_SOURCES = {"PROGRESS_SCORECARD.md"}

missing = []
for md in sorted(doc_root.glob("*.md")):
    if md.name in SKIP_SOURCES:
        continue
    text = md.read_text(encoding="utf-8")
    refs = set()
    for line in text.splitlines():
        m = LISTITEM_RE.match(line)
        if m:
            refs.add(m.group(1))
    for m in BACKTICK_RE.finditer(text):
        refs.add(m.group(1))
    for m in MDLINK_RE.finditer(text):
        refs.add(m.group(1))
    for ref in sorted(refs):
        if ref in EXTERNAL:
            continue
        if not (doc_root / ref).exists():
            missing.append(f"{md}: refers to missing {ref}")

if missing:
    print("FAIL: docs reference missing local .md files:", file=sys.stderr)
    for line in missing:
        print(line, file=sys.stderr)
    sys.exit(2)

print("OK: local .md references resolve")
PY

echo "[7/8] Building asm symbol index (labels + .EQU + local @@labels)"
{
  rg -o "^[A-Za-z_][A-Za-z0-9_]*:" "${ASM_FILE}" | sed 's/:$//' || true
  rg -o "^@@[A-Za-z_][A-Za-z0-9_]*:" "${ASM_FILE}" | sed 's/:$//' || true
  rg -o "^[A-Za-z_][A-Za-z0-9_]*[[:space:]]+\\.EQU\\b" "${ASM_FILE}" | sed 's/[[:space:]].*$//' || true
} | sort -u >"${TMPDIR_CHECK_DOCS}/asm_symbols.txt"

echo "[8/8] Validating backticked symbol references in docs"
{ rg --no-filename -o '`@@?[A-Za-z_][A-Za-z0-9_]*`|`[A-Za-z_][A-Za-z0-9_]*`' "${DOC_FILES[@]}" || true; } \
  | tr -d '`' \
  | awk '
    /^AudioMacroDescNN$/ { next }
    /^UNK_$/ { next }
    /^@@/ { print; next }
    /_/ && /[A-Z]/ { print; next }
    /^[A-Z]/ && length($0) >= 5 { print; next }
  ' \
  | sort -u >"${TMPDIR_CHECK_DOCS}/doc_symbols.txt"

comm -23 "${TMPDIR_CHECK_DOCS}/doc_symbols.txt" "${TMPDIR_CHECK_DOCS}/asm_symbols.txt" >"${TMPDIR_CHECK_DOCS}/missing_symbols.txt"

if [[ -s "${TMPDIR_CHECK_DOCS}/missing_symbols.txt" ]]; then
  echo "FAIL: docs reference unknown symbols:" >&2
  sed -n '1,120p' "${TMPDIR_CHECK_DOCS}/missing_symbols.txt" >&2
  exit 3
fi

echo "OK: docs symbol references resolve in ${ASM_FILE}"

echo "Doc consistency checks passed"
