#!/usr/bin/env bash
set -euo pipefail

# Advisory, read-only project maturity dashboard. It summarizes hard maturity
# blockers, soft review inventory, recent pass yield, and the current generated
# candidate evidence (top actionable corridors plus deferred/mixed clusters kept
# as context) in one screen so strategy decisions do not require manually
# synthesizing the scorecard, unknowns.md, KPI scripts, and pass cache.
#
# It reuses the canonical KPI scripts rather than re-deriving counts, and never
# fails on the metrics: it is a summary, not a gate.

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <project_slug>" >&2
  exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=scripts/project_common.sh
source "${SCRIPT_DIR}/project_common.sh"

load_project_conf "$1"

raw_report="$(bash "${SCRIPT_DIR}/raw_address_kpi.sh" "${ASM_FILE}" "${RAW_KPI_FILE}" 2>/dev/null || true)"
data_report="$(bash "${SCRIPT_DIR}/data_label_doc_kpi.sh" "${ASM_FILE}" "${DATA_LABEL_DOC_KPI_FILE}" 2>/dev/null || true)"
const_report="$(bash "${SCRIPT_DIR}/constant_kpi.sh" "${ASM_FILE}" "${CONST_KPI_FILE}" 2>/dev/null || true)"
inferred_report="$(bash "${SCRIPT_DIR}/inferred_kpi.sh" "${ASM_FILE}" "${INFERRED_KPI_FILE}" 2>/dev/null || true)"
comment_report="$(bash "${SCRIPT_DIR}/comment_quality_kpi.sh" "${ASM_FILE}" "${COMMENT_KPI_FILE}" 2>/dev/null || true)"
proc_report="$(bash "${SCRIPT_DIR}/procedure_doc_kpi.sh" "${ASM_FILE}" "${PROC_DOC_KPI_FILE}" 2>/dev/null || true)"
global_report="$(bash "${SCRIPT_DIR}/global_code_label_doc_kpi.sh" "${ASM_FILE}" "${GLOBAL_CODE_LABEL_DOC_KPI_FILE}" 2>/dev/null || true)"
branch_report="$(bash "${SCRIPT_DIR}/branch_literal_kpi.sh" "${ASM_FILE}" "${BRANCH_KPI_FILE}" 2>/dev/null || true)"

pass_dir="${DOC_ROOT}/inventory/pass"

python3 - \
  "$1" \
  "${PROGRESS_SCORECARD_FILE}" \
  "${pass_dir}/next_pass.json" \
  "${DOC_ROOT}/inventory/raw_ram_review.csv" \
  "${ASM_FILE}" \
  "${raw_report}" \
  "${data_report}" \
  "${const_report}" \
  "${inferred_report}" \
  "${comment_report}" \
  "${proc_report}" \
  "${global_report}" \
  "${branch_report}" <<'PY'
import json
import re
import sys
from pathlib import Path

(
    slug,
    scorecard_path,
    next_pass_path,
    raw_ram_review_path,
    asm_path,
    raw_report,
    data_report,
    const_report,
    inferred_report,
    comment_report,
    proc_report,
    global_report,
    branch_report,
) = sys.argv[1:]

RECENT_ROWS = 5
TOP_CANDIDATES = 5


def kpi(report, key, default="unknown"):
    # KPI scripts emit either a bare "key=value" line or a "[prefix] key=value"
    # line; match the key as a start-or-whitespace-delimited token so a longer
    # key (e.g. ..._undocumented) never matches a shorter suffix (..._documented).
    m = re.search(rf"(?:^|\s){re.escape(key)}=(\S+)", report)
    return m.group(1) if m else default


def read_text(path):
    p = Path(path)
    if not p.exists():
        return ""
    try:
        return p.read_text(encoding="utf-8")
    except OSError:
        return ""


def load_json(path):
    text = read_text(path)
    if not text:
        return None
    try:
        return json.loads(text)
    except ValueError:
        return None


def count_raw_indirect(asm_text):
    raw_indirect_re = re.compile(
        r"\[\$[0-9A-F]{1,4}(?:,[XY])?\](?:,[XY])?",
        re.I,
    )
    return len(raw_indirect_re.findall(asm_text))


def parse_scorecard(path):
    header = None
    rows = []
    for raw in read_text(path).splitlines():
        line = raw.strip()
        if not (line.startswith("|") and line.endswith("|")):
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        if not cells:
            continue
        if cells[0] == "pass_id":
            header = cells
            continue
        if cells[0] in {"---"} or not cells[0].isdigit():
            continue
        rows.append(cells)
    return header, rows


print(f"Maturity summary: {slug}")
print("Advisory dashboard — candidate evidence, not a gate; the operator selects the corridor objective.")
print()

print("Hard blockers (must reach 0 for maturity):")
print(f"- raw low-address operands: {kpi(raw_report, 'strict_active_raw_lowaddr')}")
print(f"- raw absolute-ROM operands: {kpi(raw_report, 'strict_active_raw_absrom')}")
print(f"- noncompliant data labels: {kpi(data_report, 'strict_data_labels_noncompliant')}")
print()

print("Soft review inventory (judgment calls, not zero-target KPIs):")
print(f"- raw indirect operands: {count_raw_indirect(read_text(asm_path))}")
print(f"- magic immediates: {kpi(const_report, 'strict_active_magic_immediates')}")
print(f"- branch literals: {kpi(branch_report, 'strict_active_branch_literals')}")
print(f"- inferred annotations: {kpi(inferred_report, 'strict_inferred_annotations')}")
print(f"- placeholder comments: {kpi(comment_report, 'strict_placeholder_comments')}")
print(
    "- undocumented callable procedures: "
    f"{kpi(proc_report, 'strict_callable_procedures_undocumented')}"
    f" / {kpi(proc_report, 'strict_callable_procedures_total')}"
    " (review inventory, not a zero target)"
)
print(
    "- undocumented global code labels: "
    f"{kpi(global_report, 'strict_global_code_labels_undocumented')}"
    f" / {kpi(global_report, 'strict_global_code_labels_total')}"
    " (review inventory, not a zero target)"
)
print()

header, rows = parse_scorecard(scorecard_path)
print(f"Recent pass yield (last {RECENT_ROWS} rows):")
if header and rows:
    def cell(row, name):
        if name in header:
            idx = header.index(name)
            if idx < len(row):
                return row[idx]
        return "-"
    # Scorecards may be oldest-first or newest-first; sort by numeric pass_id
    # descending so the highest (most recent) passes are always reported.
    recent = sorted(rows, key=lambda r: int(r[0]), reverse=True)[:RECENT_ROWS]
    for row in recent:
        movement = (
            f"labels {cell(row, 'labels_remaining')}, "
            f"raw_indirect {cell(row, 'raw_indirect_operands_remaining')}, "
            f"warn_delta {cell(row, 'warnings_baseline_delta')}, "
            f"rework {cell(row, 'rework_items')}"
        )
        print(f"- pass {row[0]} {cell(row, 'focus')}: {movement}")
else:
    print("- no scorecard rows found")
print()

next_pass = load_json(next_pass_path)
clusters = (next_pass or {}).get("cluster_candidates") or []
actionable = [c for c in clusters if not c.get("mixed_anchor")]
mixed = [c for c in clusters if c.get("mixed_anchor")]
alternatives = (next_pass or {}).get("alternative_candidates") or []

print("Top actionable candidate corridors (from generated evidence; advisory):")
if next_pass is None:
    print("- no next_pass.json; run make project-next-pass PROJECT=<slug> first")
elif actionable:
    for c in actionable[:TOP_CANDIDATES]:
        print(f"- {c.get('anchor')} ({c.get('kind')}) — {c.get('why')}")
else:
    print("- no focused actionable corridors in current evidence")
if alternatives:
    print("  data-label/format alternatives (weigh vs. another small raw-RAM pass):")
    for alt in alternatives:
        print(f"  - {alt.get('label')} ({alt.get('kind')}) — {alt.get('why')}")
print()

print("Deferred / mixed clusters (context, not direct pass targets):")
shown = False
for c in mixed:
    shown = True
    print(f"- {c.get('anchor')} [mixed-anchor evidence] — {c.get('why')}")
deferred_rows = []
review_text = read_text(raw_ram_review_path)
if review_text:
    import csv
    import io
    reader = csv.DictReader(io.StringIO(review_text))
    for r in reader:
        if (r.get("status") or "").strip() in {"deferred", "not_semantic_yet"} and (r.get("active") or "").strip() != "no":
            deferred_rows.append(r.get("addr_hex"))
if deferred_rows:
    shown = True
    print(f"- deferred raw-RAM bytes ({len(deferred_rows)}): {', '.join(deferred_rows[:12])}")
if not shown:
    print("- none recorded")
print()

print(
    "Reminder: callable/global-label counts are review inventories, not zero-target "
    "KPIs. This summary is candidate evidence; the operator selects the corridor objective."
)
PY
