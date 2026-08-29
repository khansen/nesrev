#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 || $# -gt 3 ]]; then
  echo "usage: $0 <project_slug> [pass_id] [strict|relaxed]" >&2
  exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
if [[ -n "${PROJECT_PASS_CLOSEOUT_REPO_ROOT:-}" ]]; then
  REPO_ROOT_INPUT="${PROJECT_PASS_CLOSEOUT_REPO_ROOT}"
else
  REPO_ROOT_INPUT="$(git rev-parse --show-toplevel 2>/dev/null || true)"
fi
if [[ -z "${REPO_ROOT_INPUT}" ]]; then
  echo "error: could not determine project repository root; run from the project checkout or set PROJECT_PASS_CLOSEOUT_REPO_ROOT" >&2
  exit 2
fi
if ! REPO_ROOT="$(git -C "${REPO_ROOT_INPUT}" rev-parse --show-toplevel 2>/dev/null)"; then
  echo "error: PROJECT_PASS_CLOSEOUT_REPO_ROOT is not inside a git worktree: ${REPO_ROOT_INPUT}" >&2
  exit 2
fi
cd "${REPO_ROOT}"

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

RUN_SCRIPT_DIR="${PROJECT_PASS_CLOSEOUT_SCRIPT_DIR:-${SCRIPT_DIR}}"

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
    if "|" in text:
        raise SystemExit(
            "error: raw '|' is not allowed in a scorecard cell "
            f"(got {text!r}); the scorecard is a Markdown-table ledger, so a pipe "
            "breaks the row. Use a pipe-free prose form, e.g. 'codeentries bank 1 $A64C'."
        )
    return text


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
        "rework_items": "pending",
        "notes": notes,
    }
    return [defaults.get(name, "") for name in header]


def load_plan():
    if not plan_path.exists():
        return {}, "missing"
    try:
        return json.loads(plan_path.read_text(encoding="utf-8")), "loaded"
    except json.JSONDecodeError:
        return {}, "invalid"


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


def is_pending_gate(value):
    text = (value or "").strip().lower()
    return text in {"", "pending", "n/a", "not run"}


def row_is_closed(row, header_index):
    verify = row[header_index["verify"]]
    docs_check = row[header_index["docs_check"]]
    return not is_pending_gate(verify) and not is_pending_gate(docs_check)


if not scorecard_path.exists():
    raise SystemExit(f"scorecard not found: {scorecard_path}")

lines = scorecard_path.read_text(encoding="utf-8").splitlines()
header, rows = parse_scorecard_table(lines)
plan, plan_status = load_plan()

if pass_id_arg:
    if not pass_id_arg.isdigit():
        raise SystemExit(f"pass_id must be numeric: {pass_id_arg}")
    pass_id = int(pass_id_arg)
else:
    if plan_status == "missing":
        raise SystemExit(
            f"error: {plan_path} missing; run make project-next-pass PROJECT=<slug> "
            "and make project-pass-start PROJECT=<slug> before closeout, or pass "
            "PASS=<id> explicitly when intentionally rechecking an existing pass."
        )
    if plan_status == "invalid":
        raise SystemExit(
            f"error: {plan_path} could not be parsed; rerun project-pass-start "
            "before closeout, or pass PASS=<id> explicitly when intentionally "
            "rechecking an existing pass."
        )
    pass_id = plan_pass_id(plan)
    if pass_id is None:
        raise SystemExit(
            f"error: {plan_path} has no intended_pass_id; rerun "
            "project-pass-start before closeout, or pass PASS=<id> explicitly "
            "when intentionally rechecking an existing pass."
        )

for _, row, _, row_header_index in rows:
    if int(row[row_header_index["pass_id"]]) == pass_id:
        if not pass_id_arg and row_is_closed(row, row_header_index):
            raise SystemExit(
                f"error: current pass plan resolves to pass {pass_id}, but that "
                "scorecard row is already closed. Run project-next-pass and "
                "project-pass-start for the new pass, or pass "
                f"PASS={pass_id} explicitly to recheck the existing pass."
            )
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
print(f"project-pass-closeout: added scorecard row for pass {pass_id}", file=sys.stderr)
print(pass_id)
PY
)"

python3 - \
  "${PROGRESS_SCORECARD_FILE}" \
  "${DOC_ROOT}/inventory/pass/current_pass_plan.json" \
  "${WARN_BASELINE_FILE}" \
  "${PASS_ID}" <<'PY'
import json
import sys
from pathlib import Path

scorecard_path = Path(sys.argv[1])
plan_path = Path(sys.argv[2])
warning_baseline_path = Path(sys.argv[3])
pass_id = sys.argv[4]


def warning_count(path):
    if not path.exists():
        return 0
    return sum(
        1
        for raw in path.read_text(encoding="utf-8").splitlines()
        if raw.strip() and not raw.strip().startswith("#")
    )


try:
    plan = json.loads(plan_path.read_text(encoding="utf-8"))
except (OSError, ValueError):
    plan = {}

plan_pass_id = plan.get("intended_pass_id")
start_count = plan.get("warning_baseline_count_at_start")
if str(plan_pass_id) != pass_id or not isinstance(start_count, int):
    print(
        "project-pass-closeout: warning baseline start count unavailable for "
        f"pass {pass_id}; preserving the existing warnings_baseline_delta cell",
        file=sys.stderr,
    )
    raise SystemExit(0)

delta = warning_count(warning_baseline_path) - start_count
lines = scorecard_path.read_text(encoding="utf-8").splitlines()
header = None
changed = False
for idx, raw in enumerate(lines):
    stripped = raw.strip()
    if not (stripped.startswith("|") and stripped.endswith("|")):
        continue
    cells = [cell.strip() for cell in stripped.strip("|").split("|")]
    if {"pass_id", "warnings_baseline_delta"}.issubset(set(cells)):
        header = cells
        continue
    if header is None or len(cells) != len(header):
        continue
    columns = {name: col for col, name in enumerate(header)}
    if cells[columns["pass_id"]] != pass_id:
        continue
    cells[columns["warnings_baseline_delta"]] = str(delta)
    lines[idx] = "| " + " | ".join(cells) + " |"
    changed = True
    break

if not changed:
    raise SystemExit(f"scorecard row not found while recording warning delta for pass {pass_id}")

scorecard_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
print(
    "project-pass-closeout: recorded "
    f"warnings_baseline_delta={delta} for pass {pass_id} "
    f"({start_count} -> {start_count + delta})"
)
PY

if [[ -n "${REWORK_ITEMS:-}" ]]; then
  python3 - "${PROGRESS_SCORECARD_FILE}" "${PASS_ID}" "${REWORK_ITEMS}" <<'PY'
import re
import sys
from pathlib import Path

scorecard_path = Path(sys.argv[1])
pass_id = sys.argv[2]
rework_input = re.sub(r"\s+", " ", sys.argv[3].strip())
HEADER_REQUIRED = {"pass_id", "notes", "verify", "docs_check", "rework_items"}


if "|" in rework_input:
    raise SystemExit(
        "error: raw '|' is not allowed in REWORK_ITEMS; the scorecard is a "
        "Markdown-table ledger, so a pipe breaks the row."
    )


def is_scorecard_header(cells):
    return HEADER_REQUIRED.issubset(set(cells))


lines = scorecard_path.read_text(encoding="utf-8").splitlines()
header = None
changed = False
for idx, raw in enumerate(lines):
    stripped = raw.strip()
    if not (stripped.startswith("|") and stripped.endswith("|")):
        continue
    cells = [c.strip() for c in stripped.strip("|").split("|")]
    if is_scorecard_header(cells):
        header = cells
        continue
    if header is None:
        continue
    if len(cells) != len(header):
        continue
    header_index = {name: i for i, name in enumerate(header)}
    if cells[header_index["pass_id"]] != pass_id:
        continue
    cells[header_index["rework_items"]] = rework_input
    lines[idx] = "| " + " | ".join(cells) + " |"
    changed = True
    break

if not changed:
    raise SystemExit(f"scorecard row not found for pass {pass_id}")

scorecard_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
print(
    f"project-pass-closeout: recorded rework_items='{rework_input}' for pass "
    f"{pass_id} before process preflight",
    file=sys.stderr,
)
PY
fi

TMPDIR_PASS_CLOSEOUT="$(mktemp -d)"
trap 'rm -rf "${TMPDIR_PASS_CLOSEOUT}"' EXIT
export NESREV_XREF_FILE="${TMPDIR_PASS_CLOSEOUT}/xref_with_data.json"

if [[ "${VERIFY_MODE}" == "relaxed" ]]; then
  PROJECT_VERIFY_REFRESH_INVENTORY=1 \
  PROJECT_VERIFY_REFRESH_SCRIPT="${RUN_SCRIPT_DIR}/refresh_inventory.sh" \
  ALLOW_UNRESOLVED_LXXXX=1 \
    bash "${RUN_SCRIPT_DIR}/project_verify.sh" "${SLUG}"
else
  PROJECT_VERIFY_REFRESH_INVENTORY=1 \
  PROJECT_VERIFY_REFRESH_SCRIPT="${RUN_SCRIPT_DIR}/refresh_inventory.sh" \
    bash "${RUN_SCRIPT_DIR}/project_verify.sh" "${SLUG}"
fi

bash "${RUN_SCRIPT_DIR}/project_pass_residue_check.sh" "${SLUG}" "${PASS_ID}"
bash "${RUN_SCRIPT_DIR}/project_docs_check.sh" "${SLUG}"
DATA_BLOB_RENAMED_PASS="${PASS_ID}" \
  bash "${RUN_SCRIPT_DIR}/project_process_check.sh" "${SLUG}"

python3 - "${PROGRESS_SCORECARD_FILE}" "${PASS_ID}" "${VERIFY_MODE}" "${REWORK_ITEMS:-}" <<'PY'
import sys
from pathlib import Path

scorecard_path = Path(sys.argv[1])
pass_id = sys.argv[2]
verify_mode = sys.argv[3]
rework_input = (sys.argv[4] if len(sys.argv) > 4 else "").strip()
verify_text = "pass (LXXXX allowed)" if verify_mode == "relaxed" else "pass"
HEADER_REQUIRED = {"pass_id", "notes", "verify", "docs_check", "rework_items"}


def is_scorecard_header(cells):
    return HEADER_REQUIRED.issubset(set(cells))

lines = scorecard_path.read_text(encoding="utf-8").splitlines()
changed = False
rework_pending = False
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
    if rework_input:
        cells[rework_col] = rework_input
    elif not cells[rework_col]:
        cells[rework_col] = "pending"
    if cells[rework_col].lower() == "pending":
        rework_pending = True
    lines[idx] = "| " + " | ".join(cells) + " |"
    changed = True
    break

if not changed:
    raise SystemExit(f"scorecard row not found for pass {pass_id}")

scorecard_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
print(f"project-pass-closeout: marked pass {pass_id} verify='{verify_text}', docs_check='pass'")
if rework_pending:
    print(
        f"project-pass-closeout: rework_items is 'pending' for pass {pass_id}; "
        "pass REWORK_ITEMS=<count> to record the late fixes caused by missed "
        "required sweeps (0 is a valid answer, but it must be the operator's)"
    )
PY

# Capture this pass's deferrals while the operator's own wording is at hand.
# A deferral with no recorded revisit condition is how a placeholder fossilises.
if [[ "${PROOF_DEBT_REQUIRED}" == "1" ]]; then
  # DEFERRALS is the contract; NOTES prose is the fallback for when the
  # operator did not state the gaps directly.
  python3 "${RUN_SCRIPT_DIR}/deferral_capture.py" \
    "${DOC_ROOT}/inventory/deferrals.csv" \
    --pass-id "${PASS_ID}" \
    --corridor "${FOCUS:-}" \
    --explicit "${DEFERRALS:-}" \
    --notes "${NOTES:-}"
fi

PROJECT_NEXT_PASS_AUTO_PREP=0 \
PROJECT_NEXT_PASS_WRITE_RAW_RAM_REVIEW=1 \
PROJECT_NEXT_PASS_RAW_RAM_REFRESH_ONLY=1 \
  bash "${RUN_SCRIPT_DIR}/project_next_pass.sh" "${SLUG}" json >/dev/null
bash "${RUN_SCRIPT_DIR}/project_docs_check.sh" "${SLUG}"
DATA_BLOB_RENAMED_PASS="${PASS_ID}" \
  bash "${RUN_SCRIPT_DIR}/project_process_check.sh" "${SLUG}"

echo "project-pass-closeout: completed pass ${PASS_ID} with ${VERIFY_MODE} verification"
