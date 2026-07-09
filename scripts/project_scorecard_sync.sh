#!/usr/bin/env bash
set -euo pipefail

usage() {
  echo "usage: $0 <project_slug> [pass_id] [--dry-run]" >&2
}

if [[ $# -lt 1 || $# -gt 3 ]]; then
  usage
  exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=scripts/project_common.sh
source "${SCRIPT_DIR}/project_common.sh"

PROJECT_SLUG="$1"
shift

PASS_ID=""
DRY_RUN=""

if (( $# > 0 )); then
  if [[ "$1" == "--dry-run" ]]; then
    DRY_RUN="--dry-run"
    shift
  else
    PASS_ID="$1"
    shift
  fi
fi

if (( $# > 0 )); then
  if [[ "$1" == "--dry-run" && -z "${DRY_RUN}" ]]; then
    DRY_RUN="--dry-run"
    shift
  else
    usage
    exit 64
  fi
fi

if (( $# != 0 )); then
  usage
  exit 64
fi

load_project_conf "${PROJECT_SLUG}"

python3 - "${PROGRESS_SCORECARD_FILE}" "${ASM_FILE}" "${PASS_ID}" "${SCRIPT_DIR}" "${CONST_KPI_FILE}" "${DRY_RUN}" <<'PY'
import re
import subprocess
import sys
from pathlib import Path

scorecard_file = Path(sys.argv[1])
asm_file = Path(sys.argv[2])
pass_id_arg = sys.argv[3]
script_dir = Path(sys.argv[4])
const_kpi_file = Path(sys.argv[5])
dry_run = sys.argv[6] == "--dry-run"

for label, path in (
    ("scorecard", scorecard_file),
    ("asm", asm_file),
    ("constant KPI config", const_kpi_file),
):
    if not path.is_file():
        raise SystemExit(f"error: {label} file not found: {path}")

def parse_last_pass_id(path: Path):
    last = None
    for raw in path.read_text(encoding="utf-8").splitlines():
        stripped = raw.strip()
        if not (stripped.startswith("|") and stripped.endswith("|")):
            continue
        cells = [c.strip() for c in stripped.strip("|").split("|")]
        if not cells or cells[0] in {"pass_id", "---"}:
            continue
        if cells[0].isdigit():
            pass_id = int(cells[0])
            if last is None or pass_id > last:
                last = pass_id
    return last

pass_id = int(pass_id_arg) if pass_id_arg else parse_last_pass_id(scorecard_file)
if pass_id is None:
    raise SystemExit("error: no scorecard pass rows found")

asm_text = asm_file.read_text(encoding="utf-8")

labels_defs = len(re.findall(r"^L[0-9A-F]{4,5}:", asm_text, re.M))
labels_occ = len(re.findall(r"\bL[0-9A-F]{4,5}\b|^L[0-9A-F]{4,5}:", asm_text, re.M))

raw_rom_calls = len(re.findall(r"^\s+(?:JSR|JMP)\s+\$[0-9A-F]{4}\b", asm_text, re.M))
raw_indirect_re = re.compile(
    r"\[\$[0-9A-F]{1,4}(?:,[XY])?\](?:,[XY])?",
    re.I,
)
raw_indirect_operands = len(raw_indirect_re.findall(asm_text))

const_proc = subprocess.run(
    ["bash", str(script_dir / "constant_kpi.sh"), str(asm_file), str(const_kpi_file)],
    capture_output=True,
    text=True,
)
if const_proc.returncode != 0:
    detail = (const_proc.stderr or const_proc.stdout).strip()
    suffix = f": {detail}" if detail else ""
    raise SystemExit(f"error: constant KPI calculation failed{suffix}")
hardcoded_counter_sites = ""
for raw in const_proc.stdout.splitlines():
    if "strict_active_magic_immediates=" in raw:
        hardcoded_counter_sites = raw.split("=", 1)[1].strip()
        break

supported = {
    "labels_remaining": f"{labels_defs} / {labels_occ}",
    "raw_rom_calls_remaining": str(raw_rom_calls),
    "raw_indirect_operands_remaining": str(raw_indirect_operands),
}
if hardcoded_counter_sites != "":
    supported["hardcoded_counter_sites_remaining"] = hardcoded_counter_sites

# fill_when_empty: written only if the cell is currently blank. Scoped
# strictly to the intake baseline row (pass 0): records that the
# baseline has no automated pointer-immediate KPI yet, and that the
# intake wrapper's verify + docs_check gates passed (intake's caller is
# responsible for not invoking sync until those gates have actually
# succeeded). Generic post-pass sync calls must not infer outcomes, so
# this dict stays empty for any pass other than 0.
if pass_id == 0:
    fill_when_empty = {
        "raw_ptr_immediates_remaining": "not measured",
        # Intake runs verify with ALLOW_UNRESOLVED_LXXXX=1, so the gate
        # is intentionally relaxed. Record that explicitly rather than
        # implying a strict-green run.
        "verify": "pass (intake-relaxed)",
        "docs_check": "pass",
        "rework_items": "0",
        "notes": "Intake baseline captured; semantic naming not started.",
    }
else:
    fill_when_empty = {}

lines = scorecard_file.read_text(encoding="utf-8").splitlines()
changed = False

for idx, raw in enumerate(lines):
    stripped = raw.strip()
    if not (stripped.startswith("|") and stripped.endswith("|")):
        continue
    cells = [c.strip() for c in stripped.strip("|").split("|")]
    if not cells or cells[0] in {"pass_id", "---"}:
        continue
    if cells[0] != str(pass_id):
        continue

    # find header immediately above
    header = None
    for hidx in range(idx - 1, -1, -1):
        hraw = lines[hidx].strip()
        if not (hraw.startswith("|") and hraw.endswith("|")):
            continue
        hcells = [c.strip() for c in hraw.strip("|").split("|")]
        if hcells and hcells[0] == "pass_id":
            header = hcells
            break
    if header is None:
        raise SystemExit(f"error: header row not found for pass {pass_id}")
    if len(header) != len(cells):
        raise SystemExit(f"error: scorecard row/header column mismatch for pass {pass_id}")

    header_index = {name: i for i, name in enumerate(header)}
    for key, value in supported.items():
        if key in header_index:
            col = header_index[key]
            if cells[col] != value:
                cells[col] = value
                changed = True
    for key, value in fill_when_empty.items():
        if key in header_index:
            col = header_index[key]
            if cells[col] == "" and value != "":
                cells[col] = value
                changed = True
    lines[idx] = "| " + " | ".join(cells) + " |"
    break
else:
    raise SystemExit(f"error: pass row {pass_id} not found in scorecard")

if changed:
    if not dry_run:
        scorecard_file.write_text("\n".join(lines) + "\n", encoding="utf-8")
        print(f"scorecard synced: pass {pass_id}")
    else:
        print(f"scorecard would sync: pass {pass_id}")
else:
    print(f"scorecard already in sync: pass {pass_id}")
PY
