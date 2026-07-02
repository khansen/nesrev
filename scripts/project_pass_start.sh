#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 || $# -gt 3 ]]; then
  echo "usage: $0 <project_slug> [pass_id] [target_symbol_or_override]" >&2
  exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=scripts/project_common.sh
source "${SCRIPT_DIR}/project_common.sh"

load_project_conf "$1"

PASS_ID="${2:-}"
TARGET_SYMBOL="${3:-}"

pass_dir="${DOC_ROOT}/inventory/pass"
next_pass_json="${pass_dir}/next_pass.json"

if [[ ! -f "${next_pass_json}" ]]; then
  echo "error: ${next_pass_json} missing; run make project-pass-prep PROJECT=$1 && make project-next-pass PROJECT=$1 first" >&2
  exit 2
fi

python3 - "${1}" "${PASS_ID}" "${TARGET_SYMBOL}" "${next_pass_json}" "${PROGRESS_SCORECARD_FILE}" "${pass_dir}" "${pass_dir}/xref_with_data.json" <<'PY'
import json
import os
import re
import sys
from pathlib import Path

slug, pass_id_arg, target_arg, next_pass_path, scorecard_path, pass_dir, xref_path = sys.argv[1:]

# Operator-selected corridor objective fields (env-supplied, all optional).
# Persisted into the current pass plan so the most important review artifact
# does not live only in chat. Mirrors the mandatory fields documented at
# agent_playbook/PASS_WORKFLOW.md#corridor-objective.
OBJECTIVE_FIELDS = [
    ("selected_corridor", "CORRIDOR", "Selected corridor"),
    ("why_now", "WHY_NOW", "Why now"),
    ("expected_boundaries", "BOUNDARIES", "Expected boundaries"),
    ("generated_evidence", "EVIDENCE", "Generated evidence"),
    ("explicitly_out_of_scope", "OUT_OF_SCOPE", "Explicitly out of scope"),
]
corridor_objective = {
    key: (os.environ.get(env_var) or "").strip()
    for key, env_var, _ in OBJECTIVE_FIELDS
}
missing_objective_fields = [
    env_var for key, env_var, _ in OBJECTIVE_FIELDS if not corridor_objective[key]
]
next_pass = json.loads(Path(next_pass_path).read_text(encoding="utf-8"))
scorecard_text = Path(scorecard_path).read_text(encoding="utf-8") if Path(scorecard_path).exists() else ""
xref = json.loads(Path(xref_path).read_text(encoding="utf-8")) if Path(xref_path).exists() else {}

last_pass_id = None
for raw in scorecard_text.splitlines():
    line = raw.strip()
    if not (line.startswith("|") and line.endswith("|")):
        continue
    cells = [c.strip() for c in line.strip("|").split("|")]
    if cells and cells[0].isdigit():
        pass_id = int(cells[0])
        if last_pass_id is None or pass_id > last_pass_id:
            last_pass_id = pass_id

pass_id = int(pass_id_arg) if pass_id_arg else ((last_pass_id + 1) if last_pass_id is not None else None)

cluster_candidates = next_pass.get("cluster_candidates") or []
target = None
anchor_source = "cluster_candidate" if cluster_candidates else "manual_override"

def find_symbol_definition(symbol_name):
    for sym in xref.get("symbols", []):
        if sym.get("name") != symbol_name:
            continue
        definition = sym.get("definition") or {}
        if not definition:
            continue
        return {
            "file": definition.get("file"),
            "line": definition.get("line"),
            "cpu_address": definition.get("cpu_address"),
        }
    return None

if target_arg == "notes_plan":
    target = {
        "cluster": "notes_plan",
        "anchor": "notes_plan",
        "kind": "notes_plan",
        "summary": "Anchor this pass to the durable corridor plan captured in WORKING_NOTES.md.",
        "definition": None,
        "recommended_open_range": None,
        "scope_barriers": [],
        "localize_candidates": [],
        "members": [],
    }
    anchor_source = "notes_plan"
elif target_arg:
    for row in cluster_candidates:
        aliases = {
            row.get("cluster"),
            row.get("anchor"),
            row.get("symbol"),
        }
        for member in row.get("members") or []:
            aliases.add(member.get("symbol"))
            aliases.add(member.get("addr_hex"))
            aliases.add(member.get("label"))
        if target_arg in aliases:
            target = row
            anchor_source = "cluster_candidate"
            break
    if target is None:
        target = {
            "cluster": f"{target_arg} corridor",
            "anchor": target_arg,
            "kind": "manual_override",
            "definition": find_symbol_definition(target_arg),
            "recommended_open_range": None,
            "scope_barriers": [],
            "localize_candidates": [],
            "members": [],
        }
        anchor_source = "manual_override"
elif cluster_candidates:
    target = cluster_candidates[0]
    anchor_source = "cluster_candidate"

definition = (target or {}).get("definition") or {}
open_range = (target or {}).get("recommended_open_range") or {}

plan = {
    "project": slug,
    "started_from_next_pass": str(Path(next_pass_path)),
    "intended_pass_id": pass_id,
    "selection_strategy": next_pass.get("selection_strategy"),
    "recommended_pass": next_pass.get("recommended_pass"),
    "operator_guidance": next_pass.get("operator_guidance") or {},
    "operator_signals": next_pass.get("operator_signals") or [],
    "selected_cluster": (target or {}).get("cluster"),
    "anchor_target": (target or {}).get("anchor") or (target or {}).get("symbol"),
    "anchor_source": anchor_source,
    "anchor_kind": (target or {}).get("kind"),
    "anchor_definition": definition or None,
    "recommended_open_range": open_range or None,
    "follow_up": next_pass.get("follow_up"),
    "corridor_objective": corridor_objective,
    "cluster_members": (target or {}).get("members") or [],
    "scope_barriers": (target or {}).get("scope_barriers") or [],
    "localize_candidates": (target or {}).get("localize_candidates") or [],
}

if not target_arg and cluster_candidates and anchor_source == "cluster_candidate":
    print(
        "warning: no TARGET given; using the first generated evidence bucket "
        f"({plan['anchor_target']}) as a mechanical fallback. project-next-pass "
        "output is candidate evidence, not a pass decision. Select an explicit "
        "corridor objective and pass "
        "TARGET=<corridor_anchor> (see agent_playbook/PASS_WORKFLOW.md#corridor-objective).",
        file=sys.stderr,
    )

if missing_objective_fields:
    print(
        "warning: corridor objective incomplete; missing "
        f"{', '.join(missing_objective_fields)}. Pass CORRIDOR=, WHY_NOW=, "
        "BOUNDARIES=, EVIDENCE=, OUT_OF_SCOPE= to project-pass-start to persist "
        "the full review objective (see "
        "agent_playbook/PASS_WORKFLOW.md#corridor-objective).",
        file=sys.stderr,
    )

# Advisory (never fails): warn when the operator selects a tiny 1-2-site
# corridor from generated evidence while a larger actionable corridor is still
# available, unless the objective text explains a final-tail cleanup or a
# strategic unblock. Only assessed for generated candidates, where sizes are known.
TINY_CORRIDOR_MAX = 2
LARGER_CORRIDOR_MIN = 4
EXEMPT_OBJECTIVE_RE = re.compile(
    r"final[\s-]*tail|tail[\s-]*cleanup|final[\s-]*cleanup|strateg|unblock",
    re.IGNORECASE,
)

def cluster_size(c):
    if not isinstance(c, dict):
        return 0
    if c.get("actionable_operand_count") is not None:
        return c["actionable_operand_count"]
    sizes = [m.get("site_count") or 0 for m in (c.get("members") or [])]
    return max(sizes) if sizes else 0

if anchor_source == "cluster_candidate" and target is not None:
    selected_size = cluster_size(target)
    selected_anchor = (target or {}).get("anchor")
    # Only focused/actionable corridors count as a "larger corridor to prefer";
    # mixed-anchor evidence containers are context, not pass targets (Batch 4).
    larger = [
        c for c in cluster_candidates
        if c.get("anchor") != selected_anchor
        and not c.get("mixed_anchor")
        and c.get("anchor_role") != "mixed_anchor_evidence"
        and cluster_size(c) >= LARGER_CORRIDOR_MIN
    ]
    objective_text = " ".join(corridor_objective.get(k, "") for k in corridor_objective)
    if selected_size and selected_size <= TINY_CORRIDOR_MAX and larger and not EXEMPT_OBJECTIVE_RE.search(objective_text):
        biggest = max(larger, key=cluster_size)
        print(
            f"warning: selected corridor {selected_anchor} is a tiny "
            f"{selected_size}-site objective while larger actionable corridors remain "
            f"(e.g. {biggest.get('anchor')} with {cluster_size(biggest)} sites). "
            "Prefer the larger corridor, or note final-tail cleanup / a strategic "
            "unblock in WHY_NOW (see agent_playbook/PASS_WORKFLOW.md#low-yield-checkpoint).",
            file=sys.stderr,
        )

pass_dir_path = Path(pass_dir)
json_path = pass_dir_path / "current_pass_plan.json"
md_path = pass_dir_path / "current_pass_plan.md"
json_path.write_text(json.dumps(plan, indent=2) + "\n", encoding="utf-8")

lines = []
lines.append(f"# Current Pass Plan — {slug}")
lines.append("")
lines.append(
    "Generated corridor-selection briefing. Record completed work in the "
    "scorecard and authored ledgers; this cache is replaced by the next pass start."
)
lines.append("")
if pass_id is not None:
    lines.append(f"- Intended pass id: `{pass_id}`")
if plan.get("selection_strategy"):
    lines.append(f"- Selection strategy: `{plan['selection_strategy']}`")
if plan["recommended_pass"]:
    lines.append(f"- Generated evidence bucket: `{plan['recommended_pass'].get('type', 'unknown')}`")
    if plan["recommended_pass"].get("summary"):
        lines.append(f"- Bucket summary: {plan['recommended_pass']['summary']}")
    if plan["recommended_pass"].get("operator_action"):
        lines.append(f"- Operator action: {plan['recommended_pass']['operator_action']}")
if plan["operator_signals"]:
    lines.append("- Work-based operator signals:")
    for signal in plan["operator_signals"][:6]:
        source = signal.get("source") or "unknown"
        text = signal.get("text") or ""
        lines.append(f"  - {text} ({source})")
if plan.get("selected_cluster"):
    lines.append(f"- Selected corridor: `{plan['selected_cluster']}`")
if plan["anchor_target"]:
    lines.append(f"- Corridor anchor: `{plan['anchor_target']}`")
if plan.get("anchor_source"):
    lines.append(f"- Anchor source: `{plan['anchor_source']}`")
if definition.get("file") and definition.get("line"):
    lines.append(f"- Definition: `{definition['file']}:{definition['line']}`")
if open_range.get("start_line") and open_range.get("end_line") and definition.get("file"):
    lines.append(f"- Recommended open range: `{definition['file']}:{open_range['start_line']}-{open_range['end_line']}`")
if plan.get("follow_up"):
    lines.append(f"- Follow-up: {plan['follow_up']}")
if plan.get("cluster_members"):
    lines.append("- Corridor members:")
    for item in plan["cluster_members"][:8]:
        label = item.get("symbol") or item.get("addr_hex") or item.get("label") or "unknown"
        extras = []
        if item.get("site_count") is not None:
            extras.append(f"sites {item['site_count']}")
        if item.get("review_status"):
            extras.append(f"status {item['review_status']}")
        if item.get("kind"):
            extras.append(item["kind"])
        lines.append(f"  - `{label}`" + (f" ({'; '.join(extras)})" if extras else ""))
lines.append("")
lines.append("## Corridor Objective")
if missing_objective_fields:
    lines.append(
        "Operator-selected objective is incomplete; pass CORRIDOR=, WHY_NOW=, "
        "BOUNDARIES=, EVIDENCE=, OUT_OF_SCOPE= to project-pass-start to record it."
    )
for key, _env_var, label in OBJECTIVE_FIELDS:
    value = corridor_objective[key]
    lines.append(f"- {label}: {value if value else '(not recorded)'}")

if plan["scope_barriers"]:
    lines.append("")
    lines.append("## Scope Barriers")
    for item in plan["scope_barriers"][:8]:
        lines.append(f"- `{item.get('symbol')}` line {item.get('line')} ({item.get('reason')})")
lines.append("")
lines.append("## Localization Review")
if plan["localize_candidates"]:
    for item in plan["localize_candidates"][:8]:
        state = "safe" if item.get("safe_localize") else "keep non-local"
        lines.append(f"- `{item.get('symbol')}`: {state} — {item.get('reason')}")
else:
    lines.append("- No generated localization candidates.")
lines.append("")
md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

print(json.dumps({
    "project": slug,
    "current_pass_plan_json": str(json_path),
    "current_pass_plan_md": str(md_path),
    "intended_pass_id": pass_id,
    "anchor_target": plan["anchor_target"],
    "anchor_source": plan["anchor_source"],
    "corridor_objective_recorded": not missing_objective_fields,
}, indent=2))
PY
