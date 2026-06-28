#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 || $# -gt 3 ]]; then
  echo "usage: $0 <project_slug> [pass_id] [strict|relaxed]" >&2
  exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=scripts/project_common.sh
source "${SCRIPT_DIR}/project_common.sh"

SLUG="$1"
load_project_conf "${SLUG}"

PASS_ID_ARG="${2:-}"
VERIFY_MODE="${3:-${VERIFY_MODE:-strict}}"
if [[ -z "${VERIFY_MODE}" ]]; then
  VERIFY_MODE="strict"
fi
if [[ "${VERIFY_MODE}" != "strict" && "${VERIFY_MODE}" != "relaxed" ]]; then
  echo "error: verify mode must be strict or relaxed" >&2
  exit 2
fi

RUN_SCRIPT_DIR="${PROJECT_PASS_FINISH_SCRIPT_DIR:-${SCRIPT_DIR}}"

PASS_ID="$(python3 - "${PROGRESS_SCORECARD_FILE}" "${DOC_ROOT}/inventory/pass/current_pass_plan.json" "${PASS_ID_ARG}" <<'PY'
import json
import os
import re
import sys
from pathlib import Path

scorecard_path = Path(sys.argv[1])
plan_path = Path(sys.argv[2])
pass_id_arg = sys.argv[3].strip()
focus_env = os.environ.get("FOCUS", "").strip()
notes_env = os.environ.get("NOTES", "").strip()

HEADER = [
    "pass_id",
    "focus",
    "labels_remaining",
    "raw_rom_calls_remaining",
    "raw_ptr_immediates_remaining",
    "raw_indirect_operands_remaining",
    "hardcoded_counter_sites_remaining",
    "warnings_baseline_delta",
    "verify",
    "docs_check",
    "rework_items",
    "notes",
]
SEPARATOR = ["---", "---", "---:", "---:", "---:", "---:", "---:", "---", "---", "---", "---:", "---"]
HEADER_REQUIRED = {"pass_id", "notes", "verify", "docs_check", "rework_items"}


def cell(text):
    text = re.sub(r"\s+", " ", (text or "").strip())
    return text.replace("|", "/")


def table_line(cells):
    return "| " + " | ".join(cells) + " |"


def markdown_cells(raw):
    stripped = raw.strip()
    if not (stripped.startswith("|") and stripped.endswith("|")):
        return None
    return [c.strip() for c in stripped.strip("|").split("|")]


def is_separator_row(cells):
    return bool(cells) and all(re.fullmatch(r":?-{3,}:?", cell or "") for cell in cells)


def is_scorecard_header(cells):
    return HEADER_REQUIRED.issubset(set(cells))


def parse_scorecard_table(lines):
    header = None
    header_index = None
    rows = []
    for idx, raw in enumerate(lines):
        cells = markdown_cells(raw)
        if cells is None:
            continue
        if is_scorecard_header(cells):
            header = cells
            header_index = {name: col for col, name in enumerate(header)}
            continue
        if header is None or header_index is None:
            continue
        if is_separator_row(cells):
            continue
        pass_col = header_index["pass_id"]
        if len(cells) != len(header):
            continue
        if cells[pass_col].isdigit():
            rows.append((idx, cells, header, header_index))
    return header, rows


def row_for_header(header, pass_id, focus, notes):
    defaults = {
        "pass_id": str(pass_id),
        "focus": focus,
        "labels_remaining": "0 / 0",
        "raw_rom_calls_remaining": "0",
        "raw_ptr_immediates_remaining": "not measured",
        "raw_indirect_operands_remaining": "0",
        "hardcoded_counter_sites_remaining": "0",
        "warnings_baseline_delta": "0",
        "verify": "pending",
        "docs_check": "pending",
        "rework_items": "0",
        "notes": notes,
    }
    return [defaults.get(name, "") for name in header]


def load_plan():
    if not plan_path.exists():
        return {}
    try:
        return json.loads(plan_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {}


def plan_pass_id(plan):
    value = plan.get("intended_pass_id")
    if isinstance(value, int):
        return value
    if isinstance(value, str) and value.isdigit():
        return int(value)
    return None


def objective_focus(plan):
    objective = plan.get("corridor_objective") or {}
    selected = cell(objective.get("selected_corridor", ""))
    if selected:
        return selected
    cluster = cell(plan.get("selected_cluster", ""))
    if cluster:
        return cluster
    anchor = cell(plan.get("anchor_target", ""))
    if anchor:
        return f"{anchor} corridor"
    return ""


def objective_notes(plan, focus):
    objective = plan.get("corridor_objective") or {}
    why_now = cell(objective.get("why_now", ""))
    boundaries = cell(objective.get("expected_boundaries", ""))
    if why_now or boundaries:
        pieces = [f"Closed {focus}."]
        if why_now:
            pieces.append(f"Why now: {why_now}.")
        if boundaries:
            pieces.append(f"Boundary: {boundaries}.")
        return " ".join(pieces)
    return f"Closed {focus}; synchronized scorecard and closeout gates."


if not scorecard_path.exists():
    raise SystemExit(f"scorecard not found: {scorecard_path}")

lines = scorecard_path.read_text(encoding="utf-8").splitlines()
header, rows = parse_scorecard_table(lines)
plan = load_plan()

if pass_id_arg:
    if not pass_id_arg.isdigit():
        raise SystemExit(f"pass_id must be numeric: {pass_id_arg}")
    pass_id = int(pass_id_arg)
else:
    pass_id = plan_pass_id(plan)
    if pass_id is None:
        pass_id = (
            max((int(row[1][row[3]["pass_id"]]) for row in rows), default=-1) + 1
        )

for _, row, _, row_header_index in rows:
    if int(row[row_header_index["pass_id"]]) == pass_id:
        print(pass_id)
        raise SystemExit(0)

focus = cell(focus_env) or objective_focus(plan) or f"Pass {pass_id} corridor"
notes = cell(notes_env) or objective_notes(plan, focus)

if not lines:
    header = HEADER
    lines = [table_line(header), table_line(SEPARATOR)]
    insert_at = len(lines)
elif rows:
    insert_idx, _, header, _ = max(rows, key=lambda row: row[0])
    insert_at = insert_idx + 1
else:
    insert_at = len(lines)
    if header is None:
        header = HEADER
        lines.extend([table_line(header), table_line(SEPARATOR)])
        insert_at = len(lines)

lines.insert(insert_at, table_line(row_for_header(header, pass_id, focus, notes)))
scorecard_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
print(f"project-pass-finish: added scorecard row for pass {pass_id}", file=sys.stderr)
print(pass_id)
PY
)"

bash "${RUN_SCRIPT_DIR}/project_pass_closeout.sh" "${SLUG}" "${PASS_ID}"
bash "${RUN_SCRIPT_DIR}/project_docs_check.sh" "${SLUG}"
bash "${RUN_SCRIPT_DIR}/project_process_check.sh" "${SLUG}"

if [[ "${VERIFY_MODE}" == "relaxed" ]]; then
  ALLOW_UNRESOLVED_LXXXX=1 bash "${RUN_SCRIPT_DIR}/project_verify.sh" "${SLUG}"
else
  bash "${RUN_SCRIPT_DIR}/project_verify.sh" "${SLUG}"
fi

python3 - "${PROGRESS_SCORECARD_FILE}" "${PASS_ID}" "${VERIFY_MODE}" <<'PY'
import sys
from pathlib import Path

scorecard_path = Path(sys.argv[1])
pass_id = sys.argv[2]
verify_mode = sys.argv[3]
verify_text = "pass (LXXXX allowed)" if verify_mode == "relaxed" else "pass"
HEADER_REQUIRED = {"pass_id", "notes", "verify", "docs_check", "rework_items"}


def is_scorecard_header(cells):
    return HEADER_REQUIRED.issubset(set(cells))

lines = scorecard_path.read_text(encoding="utf-8").splitlines()
changed = False
header = None
for idx, raw in enumerate(lines):
    stripped = raw.strip()
    if not (stripped.startswith("|") and stripped.endswith("|")):
        continue
    cells = [c.strip() for c in stripped.strip("|").split("|")]
    if not cells:
        continue
    if is_scorecard_header(cells):
        header = cells
        continue
    if header is None:
        continue
    if cells[0] == "---":
        continue
    if len(cells) != len(header):
        raise SystemExit(f"scorecard row/header column mismatch while marking pass {pass_id}")
    header_index = {name: i for i, name in enumerate(header)}
    required = ["pass_id", "verify", "docs_check", "rework_items"]
    missing = [name for name in required if name not in header_index]
    if missing:
        raise SystemExit(f"scorecard header missing required column(s): {', '.join(missing)}")
    if cells[header_index["pass_id"]] != pass_id:
        continue
    cells[header_index["verify"]] = verify_text
    cells[header_index["docs_check"]] = "pass"
    rework_col = header_index["rework_items"]
    if not cells[rework_col] or cells[rework_col].lower() in {"pending", "n/a"}:
        cells[rework_col] = "0"
    lines[idx] = "| " + " | ".join(cells) + " |"
    changed = True
    break

if not changed:
    raise SystemExit(f"scorecard row not found for pass {pass_id}")

scorecard_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
print(f"project-pass-finish: marked pass {pass_id} verify='{verify_text}', docs_check='pass'")
PY

bash "${RUN_SCRIPT_DIR}/project_docs_check.sh" "${SLUG}"

echo "project-pass-finish: completed pass ${PASS_ID} with ${VERIFY_MODE} verification"
