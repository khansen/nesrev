#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 || $# -gt 2 ]]; then
  echo "usage: $0 <project_slug> [text|json]" >&2
  exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=scripts/project_common.sh
source "${SCRIPT_DIR}/project_common.sh"

load_project_conf "$1"
OUTPUT_FORMAT="${2:-text}"

python3 - "${ASM_FILE}" "${OUTPUT_FORMAT}" <<'PY'
import json
import re
import sys
from pathlib import Path

asm_file = Path(sys.argv[1])
out_format = sys.argv[2]

EQU_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s+\.EQU\s+(\$[0-9A-Fa-f]{2,4})\b")
COMMENT_ADDR_RE = re.compile(r"\$[0-9A-Fa-f]{2,4}\b")
EQU_LINE_RE = re.compile(r"^\s*[A-Za-z_][A-Za-z0-9_]*\s+\.EQU\b")

# Restrict to address/storage-like symbol families. This avoids false positives
# from value/bitmask constants such as PAD_BTN_A or PPUCTRL_NMI_ENABLE.
def is_address_symbol(name: str) -> bool:
    if name.startswith(("ZP_", "RAM_", "IO_RAW_")):
        return True
    return name in {
        "PPUCTRL", "PPUMASK", "PPUSTATUS", "OAMADDR", "OAMDATA",
        "PPUSCROLL", "PPUADDR", "PPUDATA", "OAMDMA", "APUSTATUS",
        "JOY1", "JOY2",
    }

def looks_like_address_reference(comment: str, match: re.Match[str]) -> bool:
    addr = match.group(0)
    lowered = comment.lower()
    start, end = match.span()

    # Explicit byte values and value ranges are common in format comments. Keep
    # this audit scoped to storage/address prose, not semantic value literals.
    value_words = (
        "token", "state", "states", "tile", "tiles", "timer value",
        "threshold", "sentinel", "terminator", "palette", "attr", "branch",
        "position", "minimum",
        "sweep", "byte ",
        "bytes ", "value", "values", "offset", "offsets", "ofs ",
        "field", "fields",
        "index", "indices", "duration", "volume", "control", "coordinate",
        "pixel", "start at", "down to", "limit", "capped", "scaled",
        "signed range",
        "off-screen", "wraparound", "bitmask",
        "bitmasks", "mask bits", "range 0-", "positions range",
    )
    if any(word in lowered for word in value_words):
        return False

    # Four-digit literals are almost always actual addresses or hardware regs.
    if len(addr) == 5:
        return True

    # Two-digit literals are noisy. Only keep direct addressing forms or obvious
    # storage-like prose.
    tail = comment[end:end + 2]
    head = comment[max(0, start - 1):start]
    if tail == ".." or comment[max(0, start - 2):start] == "..":
        return False
    direct_operand = (
        tail.startswith((",X", ",Y")) or
        (head == "[" or comment[max(0, start - 2):start] in {"[$", "($"}) or
        re.search(r"(?:from|to|into|at|in|reads?|writes?|stores?|loads?|copies?|copy)\s+\$[0-9A-Fa-f]{2}\b", comment[:end], re.IGNORECASE)
    )
    if not direct_operand and head not in {"-", "/"} and tail[:1] not in {"-", "/"}:
        return False

    return any(word in lowered for word in (
        "range", "block", "window", "array", "arrays", "triplet",
        "runtime", "shadow", "latch", "ptr", "pointer", "bounds",
        "slot", "slots", "copied", "copy", "save", "restore",
        "from", "into", "back to", "at ",
    ))


addr_to_symbols = {}
lines = asm_file.read_text(encoding="utf-8").splitlines()

for raw in lines:
    m = EQU_RE.match(raw)
    if not m:
        continue
    name = m.group(1)
    if not is_address_symbol(name):
        continue
    addr = m.group(2).upper()
    addr_to_symbols.setdefault(addr, []).append(name)

findings = []
for lineno, raw in enumerate(lines, start=1):
    if ";" not in raw:
        continue
    if EQU_LINE_RE.match(raw):
        continue
    comment = raw.split(";", 1)[1]
    seen = set()
    for match in COMMENT_ADDR_RE.finditer(comment):
        if not looks_like_address_reference(comment, match):
            continue
        addr = match.group(0).upper()
        if addr in seen:
            continue
        seen.add(addr)
        symbols = addr_to_symbols.get(addr)
        if not symbols:
            continue
        findings.append({
            "file": str(asm_file),
            "line": lineno,
            "address": addr,
            "symbols": symbols,
            "text": raw.rstrip(),
        })

payload = {
    "file": str(asm_file),
    "finding_count": len(findings),
    "findings": findings,
}

if out_format == "json":
    print(json.dumps(payload, indent=2))
else:
    if not findings:
        print(f"OK: no stale raw-address comments found in {asm_file}")
    else:
        print(f"stale raw-address comment candidates: {len(findings)}")
        for item in findings:
            symbols = ", ".join(item["symbols"])
            print(f"{item['file']}:{item['line']}: {item['address']} -> {symbols}")
            print(f"  {item['text']}")

if findings:
    sys.exit(69)
PY
