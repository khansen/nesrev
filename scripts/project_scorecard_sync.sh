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
if pass_id == 0:
    raise SystemExit("error: historical pass 0 is read-only; use make project-intake PROJECT=<slug> for a current snapshot")

sys.path.insert(0, str(script_dir))
from scorecard_metrics import measure
try:
    supported = measure(asm_file, const_kpi_file, script_dir)
except (OSError, ValueError) as exc:
    raise SystemExit(f"error: {exc}") from exc

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
