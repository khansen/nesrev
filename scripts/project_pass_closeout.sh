#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 || $# -gt 2 ]]; then
  echo "usage: $0 <project_slug> [pass_id]" >&2
  exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=scripts/project_common.sh
source "${SCRIPT_DIR}/project_common.sh"

load_project_conf "$1"
PASS_ID="${2:-}"

bash "${SCRIPT_DIR}/project_scorecard_sync.sh" "$1" "${PASS_ID}"

python3 - "${DOC_ROOT}" "${PASS_ID}" "${PROGRESS_SCORECARD_FILE}" "${RENAMES_FILE}" "${ASM_FILE}" "${SCRIPT_DIR}" <<'PY'
import csv
import json
import re
import subprocess
import sys
from pathlib import Path

doc_root = Path(sys.argv[1])
pass_id_arg = sys.argv[2]
scorecard_file = Path(sys.argv[3])
renames_file = Path(sys.argv[4])
asm_file = Path(sys.argv[5])
script_dir = Path(sys.argv[6])
sys.path.insert(0, str(script_dir))

from rename_ledger_rules import valid_old_name_shape

expected = ["old_name", "new_name", "reason", "confidence", "pass_id"]
SCOPED_OVERLAY_CONFIDENCE = {"scoped-overlay"}
RAW_RAM_REVIEW_FIELDS = [
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
MNEMONIC_RE = re.compile(r"^\s*([A-Za-z]{3}(?:\.[A-Za-z])?)\s+([^;]+?)(?:\s*;.*)?$")
RAW_LOWADDR_OPERAND_RE = re.compile(
    r"^(?:"
    r"\$([0-9A-F]{1,4})(?:,[XY])?"
    r"|\(\$([0-9A-F]{1,4})(?:,[XY])?\)(?:,Y)?"
    r"|\[\$([0-9A-F]{1,4})(?:,[XY])?\](?:,[XY])?"
    r")$",
    re.IGNORECASE,
)


def parse_last_pass_id(path: Path):
    last = None
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not (line.startswith("|") and line.endswith("|")):
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        if not cells or cells[0] in {"pass_id", "---"}:
            continue
        if cells[0].isdigit():
            pass_id = int(cells[0])
            if last is None or pass_id > last:
                last = pass_id
    return last


def parse_scorecard_rows(path: Path):
    rows = []
    header = None
    for lineno, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        line = raw.rstrip()
        stripped = line.strip()
        if not (stripped.startswith("|") and stripped.endswith("|")):
            continue
        cells = [c.strip() for c in stripped.strip("|").split("|")]
        if not cells:
            continue
        if cells[0] == "pass_id":
            header = cells
            continue
        if cells[0] == "---":
            continue
        if cells[0].isdigit():
            rows.append((lineno, cells))
    return header, rows

def load_json(path: Path):
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))

def raw_addr_from_symbol(symbol: str):
    m = re.fullmatch(r"raw_\$(?P<hex>[0-9A-Fa-f]{1,4})", symbol or "")
    if not m:
        return None
    return f"0x{int(m.group('hex'), 16):04x}"


def bare_raw_addr_old_name(symbol: str):
    m = re.fullmatch(r"(?:\$|0x)(?P<hex>[0-9A-Fa-f]{1,4})", symbol or "")
    if not m:
        return None
    addr = int(m.group("hex"), 16)
    if addr > 0x0FFF:
        return None
    return {
        "addr_hex": f"0x{addr:04x}",
        "required_old_name": f"raw_${addr:04X}",
    }


def is_scoped_overlay_rename(row):
    return (row.get("confidence") or "").strip().lower() in SCOPED_OVERLAY_CONFIDENCE


def raw_symbol_targets(rename_rows, *, include_scoped_overlays=False):
    targets = {}
    for row in rename_rows:
        if not include_scoped_overlays and is_scoped_overlay_rename(row):
            continue
        addr_hex = raw_addr_from_symbol((row.get("old_name") or "").strip())
        new_name = (row.get("new_name") or "").strip()
        if addr_hex is None or new_name == "":
            continue
        targets.setdefault(addr_hex, set()).add(new_name)
    return {
        addr_hex: sorted(symbols)
        for addr_hex, symbols in sorted(targets.items())
    }


def scoped_overlay_raw_symbols(rename_rows):
    overlays = []
    for row in rename_rows:
        if not is_scoped_overlay_rename(row):
            continue
        addr_hex = raw_addr_from_symbol((row.get("old_name") or "").strip())
        if addr_hex is None:
            continue
        overlays.append({
            "addr_hex": addr_hex,
            "old_name": (row.get("old_name") or "").strip(),
            "new_name": (row.get("new_name") or "").strip(),
            "reason": (row.get("reason") or "").strip(),
        })
    return overlays

def local_label_owner_index(asm_file: Path):
    owners = {}
    current_global = ""
    global_re = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*):")
    local_re = re.compile(r"^(@@[A-Za-z_][A-Za-z0-9_]*):")
    for raw in asm_file.read_text(encoding="utf-8").splitlines():
        stripped = raw.strip()
        m = global_re.match(stripped)
        if m:
            current_global = m.group(1)
            continue
        m = local_re.match(stripped)
        if m and current_global:
            owners.setdefault(m.group(1), set()).add(current_global)
    return {
        local_name: sorted(owner_set)
        for local_name, owner_set in owners.items()
    }


def rewrite_top_owner_field(text: str, replacements: dict[str, str]):
    if not text:
        return text
    changed = False
    order = []
    counts = {}
    passthrough = []
    for item in text.split(","):
        name, sep, count = item.partition(":")
        replacement = replacements.get(name, name)
        if replacement != name:
            changed = True
        if sep and count.isdigit():
            if replacement not in counts:
                order.append(replacement)
                counts[replacement] = 0
            counts[replacement] += int(count)
        else:
            passthrough.append(f"{replacement}{sep}{count}" if sep else replacement)
    if not changed:
        return text
    parts = [f"{name}:{counts[name]}" for name in order]
    parts.extend(passthrough)
    return ",".join(parts)


def rewrite_raw_ram_review_owner_symbols(doc_root: Path, asm_file: Path, rename_rows):
    review_path = doc_root / "inventory" / "raw_ram_review.csv"
    if not review_path.exists():
        return None

    local_owners = local_label_owner_index(asm_file)
    replacements = {}
    ambiguous_local_replacements = []
    for row in rename_rows:
        old_name = (row.get("old_name") or "").strip()
        new_name = (row.get("new_name") or "").strip()
        if not old_name or not new_name or raw_addr_from_symbol(old_name):
            continue
        if new_name.startswith("@@"):
            owners = local_owners.get(new_name, [])
            if len(owners) == 1:
                replacements[old_name] = owners[0]
            else:
                ambiguous_local_replacements.append({
                    "old_name": old_name,
                    "new_name": new_name,
                    "candidate_owners": owners,
                    "reason": "ambiguous local label owner" if owners else "local label not found",
                })
        else:
            replacements[old_name] = new_name

    if not replacements:
        return {
            "updated": False,
            "replacements": replacements,
            "ambiguous_local_replacements": ambiguous_local_replacements,
        }

    rows = []
    changed = False
    with review_path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        if reader.fieldnames != RAW_RAM_REVIEW_FIELDS:
            return None
        for row in reader:
            for field in ("top_readers", "top_writers"):
                updated = rewrite_top_owner_field(row.get(field, ""), replacements)
                if updated != row.get(field, ""):
                    row[field] = updated
                    changed = True
            rows.append({field: row.get(field, "") for field in RAW_RAM_REVIEW_FIELDS})

    if changed:
        with review_path.open("w", encoding="utf-8", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=RAW_RAM_REVIEW_FIELDS, lineterminator='\n')
            writer.writeheader()
            writer.writerows(rows)

    return {
        "updated": changed,
        "replacements": replacements,
        "ambiguous_local_replacements": ambiguous_local_replacements,
    }


def parse_active_raw_sites(path: Path):
    sites = []
    for lineno, text in enumerate(
        path.read_text(encoding="utf-8").splitlines(),
        start=1,
    ):
        m = MNEMONIC_RE.match(text)
        if not m:
            continue
        mnemonic = m.group(1)
        operand = m.group(2).strip().split()[0]
        if operand.startswith("#"):
            continue
        m2 = RAW_LOWADDR_OPERAND_RE.match(operand)
        if not m2:
            continue
        raw = next((group for group in m2.groups() if group), "")
        if not raw:
            continue
        addr = int(raw, 16)
        if addr <= 0x0FFF:
            sites.append({
                "addr_hex": f"0x{addr:04x}",
                "line": lineno,
                "mnemonic": mnemonic.upper(),
                "operand": operand,
                "text": text.strip(),
            })
    return sites


def find_raw_symbol_residue(asm_file: Path, rename_rows):
    targets = raw_symbol_targets(rename_rows)
    residue = []
    for site in parse_active_raw_sites(asm_file):
        symbols = targets.get(site["addr_hex"])
        if not symbols:
            continue
        residue.append({
            "addr_hex": site["addr_hex"],
            "new_symbols": symbols,
            "file": str(asm_file),
            "line": site["line"],
            "mnemonic": site["mnemonic"],
            "operand": site["operand"],
            "text": site["text"],
        })
    return residue


def update_raw_ram_review_on_closeout(
    doc_root: Path,
    pass_id: int,
    rename_rows,
):
    review_path = doc_root / "inventory" / "raw_ram_review.csv"
    if not review_path.exists():
        return None
    target_addrs = set(raw_symbol_targets(rename_rows))
    if not target_addrs:
        return None
    rows = []
    changed = False
    updated_addrs = []
    with review_path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            addr_hex = (row.get("addr_hex") or "").strip().lower()
            if addr_hex in target_addrs:
                row["last_pass_reviewed"] = str(pass_id)
                row["status"] = "symbolized"
                row["active"] = "no"
                changed = True
                updated_addrs.append(addr_hex)
            rows.append({field: row.get(field, "") for field in RAW_RAM_REVIEW_FIELDS})
    if changed:
        with review_path.open("w", encoding="utf-8", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=RAW_RAM_REVIEW_FIELDS, lineterminator='\n')
            writer.writeheader()
            writer.writerows(rows)
    return {
        "addr_hexes": sorted(target_addrs),
        "updated_addr_hexes": sorted(updated_addrs),
        "updated": changed,
    }


pass_id = int(pass_id_arg) if pass_id_arg else parse_last_pass_id(scorecard_file)
if pass_id is None:
    print(json.dumps({
        "pass_id": None,
        "old_symbols": [],
        "residue": [],
        "summary": "No pass rows found in scorecard.",
    }, indent=2))
    sys.exit(0)

# Persisted corridor objective from pass-start (see
# agent_playbook/PASS_WORKFLOW.md#corridor-objective). Surfaced so closeout can
# remind the operator to summarize the completed corridor against the recorded
# objective. Advisory only: this never fails the closeout.
OBJECTIVE_FIELDS = [
    "selected_corridor",
    "why_now",
    "expected_boundaries",
    "generated_evidence",
    "explicitly_out_of_scope",
]

def load_corridor_objective(doc_root: Path, pass_id: int):
    plan_path = doc_root / "inventory" / "pass" / "current_pass_plan.json"
    if not plan_path.exists():
        return None, None, "missing", []
    # The plan is a generated cache; a malformed or partially written file must
    # never crash closeout, because the corridor-objective check is advisory.
    try:
        plan = json.loads(plan_path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None, None, "invalid_plan", []
    objective = plan.get("corridor_objective") if isinstance(plan, dict) else None
    if not isinstance(objective, dict):
        return None, None, "missing", []
    plan_pass_id = plan.get("intended_pass_id")
    missing = [f for f in OBJECTIVE_FIELDS if not (objective.get(f) or "").strip()]
    if plan_pass_id is not None and plan_pass_id != pass_id:
        status = "stale_plan"
    elif missing:
        status = "incomplete"
    else:
        status = "complete"
    return objective, plan_pass_id, status, missing

corridor_objective, objective_plan_pass_id, objective_status, objective_missing_fields = (
    load_corridor_objective(doc_root, pass_id)
)

if objective_status == "missing":
    print(
        "warning: no persisted corridor objective found "
        "(current_pass_plan.json has no corridor_objective). The scorecard row "
        "must still summarize the completed corridor; record the objective at "
        "pass-start next time (agent_playbook/PASS_WORKFLOW.md#corridor-objective).",
        file=sys.stderr,
    )
elif objective_status == "invalid_plan":
    print(
        "warning: current_pass_plan.json could not be parsed; treating the "
        "corridor objective as unrecorded. The scorecard row must still "
        "summarize the completed corridor; re-run pass-start to regenerate a "
        "clean plan (agent_playbook/PASS_WORKFLOW.md#corridor-objective).",
        file=sys.stderr,
    )
elif objective_status == "stale_plan":
    print(
        f"warning: persisted corridor objective is for pass {objective_plan_pass_id}, "
        f"not closeout pass {pass_id}; treat it as stale and summarize the corridor "
        "that was actually completed.",
        file=sys.stderr,
    )
elif objective_status == "incomplete":
    print(
        "warning: corridor objective was incomplete at pass start; missing "
        f"{', '.join(objective_missing_fields)}. Summarize the completed corridor "
        "against the recorded objective and record full objectives next time.",
        file=sys.stderr,
    )

project_root = asm_file.parents[1]


def is_untracked_authored_project_path(path: Path, root: Path):
    try:
        rel = path.relative_to(root)
    except ValueError:
        return False
    parts = rel.parts
    if not parts:
        return False
    if parts[0] in {"asm", "config", "scripts"}:
        return True
    if parts[0] == "tools" and len(parts) > 1 and parts[1] == "trace":
        return True
    if (
        parts[0] == "docs"
        and len(parts) > 1
        and parts[1] in {"crosswalk", "reverse_engineering"}
    ):
        return True
    return rel.as_posix() == "project.conf"


def git_authored_diff_paths(root: Path):
    # `git diff` alone misses staged files, so a pass that's already been
    # `git add`ed would falsely report no changes. We still include untracked
    # canonical project files for new-file passes, but ignore local scratch,
    # helper mods, tmp traces, references, and other intentionally untracked
    # workspace material.
    proc = subprocess.run(
        ["git", "status", "--porcelain=v1", "-z", "--untracked-files=all", "--", str(root)],
        capture_output=True,
        text=True,
        check=True,
    )
    authored: list[str] = []
    seen: set[str] = set()
    repo_root = Path.cwd()
    root_abs = root if root.is_absolute() else repo_root / root
    # Porcelain `-z` emits each record as "XY <path>\0". For renames/copies
    # (status code starts with R or C), a second NUL-terminated record
    # carries the original path; consume it without emitting.
    records = iter(proc.stdout.split("\0"))
    for raw in records:
        if len(raw) < 4:
            continue
        status_code = raw[:2]
        entry = raw[3:]
        if status_code[0] in {"R", "C"}:
            # Drop the original-path record that follows.
            try:
                next(records)
            except StopIteration:
                pass
        path = Path(entry)
        if not entry or entry in seen:
            continue
        seen.add(entry)
        check_path = path if path.is_absolute() else repo_root / path
        if status_code == "??" and not is_untracked_authored_project_path(check_path, root_abs):
            continue
        if "docs/reverse_engineering/inventory/pass" in str(path):
            continue
        if path.name in {"intake_listing.json", "intake_xref.json", "raw_address_audit.json"}:
            continue
        if path.name == "unknowns.md":
            continue
        authored.append(str(path))
    return authored

scorecard_header, scorecard_rows = parse_scorecard_rows(scorecard_file)
if not scorecard_header:
    print(json.dumps({
        "pass_id": pass_id,
        "old_symbols": [],
        "residue": [],
        "summary": "Scorecard header row not found.",
    }, indent=2))
    sys.exit(2)

latest_rows = [(lineno, cells) for lineno, cells in scorecard_rows if int(cells[0]) == pass_id]
if len(latest_rows) != 1:
    print(json.dumps({
        "pass_id": pass_id,
        "old_symbols": [],
        "residue": [],
        "summary": "Scorecard pass row missing or duplicated.",
        "error": {
            "matching_rows": [lineno for lineno, _ in latest_rows],
        },
    }, indent=2))
    sys.exit(2)

scorecard_line, latest_scorecard_cells = latest_rows[0]
if len(latest_scorecard_cells) != len(scorecard_header):
    print(json.dumps({
        "pass_id": pass_id,
        "old_symbols": [],
        "residue": [],
        "summary": f"Scorecard row {scorecard_line} has wrong column count.",
        "error": {
            "expected_columns": len(scorecard_header),
            "actual_columns": len(latest_scorecard_cells),
            "row": latest_scorecard_cells,
        },
    }, indent=2))
    sys.exit(2)

labels_remaining = latest_scorecard_cells[2] if len(latest_scorecard_cells) > 2 else ""
if not re.fullmatch(r"\d+\s*/\s*\d+", labels_remaining):
    print(json.dumps({
        "pass_id": pass_id,
        "old_symbols": [],
        "residue": [],
        "summary": f"Scorecard row {scorecard_line} has invalid labels_remaining shape.",
        "error": {
            "labels_remaining": labels_remaining,
        },
    }, indent=2))
    sys.exit(2)

old_symbols = []
rename_rows_for_pass = []
invalid_raw_old_names = []
invalid_old_name_shapes = []
with renames_file.open("r", encoding="utf-8", newline="") as f:
    reader = csv.DictReader(f)
    if reader.fieldnames != expected:
        print(json.dumps({
            "pass_id": pass_id,
            "old_symbols": [],
            "residue": [],
            "summary": "renames.csv header mismatch",
            "error": {
                "expected_header": expected,
                "actual_header": reader.fieldnames,
            },
        }, indent=2))
        sys.exit(2)
    for idx, row in enumerate(reader, start=2):
        if None in row:
            print(json.dumps({
                "pass_id": pass_id,
                "old_symbols": [],
                "residue": [],
                "summary": f"renames.csv row {idx} has too many columns",
                "error": row,
            }, indent=2))
            sys.exit(2)
        missing = [key for key in expected if row.get(key, "").strip() == ""]
        if missing:
            print(json.dumps({
                "pass_id": pass_id,
                "old_symbols": [],
                "residue": [],
                "summary": f"renames.csv row {idx} has empty required fields",
                "error": {
                    "row": row,
                    "missing": missing,
                },
            }, indent=2))
            sys.exit(2)
        try:
            row_pass = int(row.get("pass_id", ""))
        except ValueError:
            print(json.dumps({
                "pass_id": pass_id,
                "old_symbols": [],
                "residue": [],
                "summary": f"renames.csv row {idx} has non-integer pass_id",
                "error": row,
            }, indent=2))
            sys.exit(2)
        if row_pass == pass_id:
            old_name = row.get("old_name", "").strip()
            bare_raw = bare_raw_addr_old_name(old_name)
            if bare_raw:
                invalid_raw_old_names.append({
                    "row": idx,
                    "old_name": old_name,
                    **bare_raw,
                })
            if not valid_old_name_shape(old_name):
                invalid_old_name_shapes.append({
                    "row": idx,
                    "old_name": old_name,
                    "expected": (
                        "asm symbol-style name, LXXXX label, @@local label, "
                        "raw_$NN/raw_$NNNN address key, or specific raw_* synthetic key"
                    ),
                })
            rename_rows_for_pass.append({
                key: (row.get(key) or "").strip()
                for key in expected
            })
            if old_name:
                old_symbols.append(old_name)

old_symbols = sorted(dict.fromkeys(old_symbols))
if invalid_raw_old_names:
    print(json.dumps({
        "pass_id": pass_id,
        "old_symbols": old_symbols,
        "residue": [],
        "summary": (
            "Raw RAM/ZP renames must use raw_$NNNN in renames.csv old_name; "
            "bare $NN/$NNNN rows are not reconciled with raw_ram_review.csv."
        ),
        "error": {
            "invalid_rows": invalid_raw_old_names,
        },
    }, indent=2))
    sys.exit(2)
if invalid_old_name_shapes:
    print(json.dumps({
        "pass_id": pass_id,
        "old_symbols": old_symbols,
        "residue": [],
        "summary": (
            "renames.csv old_name values must be symbol-shaped. "
            "Plain lowercase prose keys create false stale-symbol matches."
        ),
        "error": {
            "invalid_rows": invalid_old_name_shapes,
        },
    }, indent=2))
    sys.exit(2)
authored_diff_paths = git_authored_diff_paths(project_root)

if not authored_diff_paths:
    print(json.dumps({
        "pass_id": pass_id,
        "old_symbols": old_symbols,
        "residue": [],
        "summary": "No authored project-file changes detected for this pass.",
        "error": {
            "project_root": str(project_root),
        },
    }, indent=2))
    sys.exit(2)

latest_row_residue = []
for symbol in old_symbols:
    pattern = re.compile(rf"`{re.escape(symbol)}`|\b{re.escape(symbol)}\b")
    row_text = " | ".join(latest_scorecard_cells)
    if pattern.search(row_text):
        latest_row_residue.append({
            "symbol": symbol,
            "file": str(scorecard_file),
            "line": scorecard_line,
            "text": row_text,
        })

if latest_row_residue:
    print(json.dumps({
        "pass_id": pass_id,
        "old_symbols": old_symbols,
        "residue": latest_row_residue,
        "summary": "Latest scorecard row still mentions old symbols from this pass.",
    }, indent=2))
    sys.exit(4)

raw_ram_review_owner_update = rewrite_raw_ram_review_owner_symbols(
    doc_root,
    asm_file,
    rename_rows_for_pass,
)

doc_files = []
for path in doc_root.rglob("*"):
    if not path.is_file():
        continue
    rel = path.relative_to(doc_root)
    if "inventory/pass" in str(rel):
        continue
    if path.name == "renames.csv":
        continue
    if path.name in {"intake_listing.json", "intake_xref.json", "raw_address_audit.json"}:
        continue
    doc_files.append(path)

residue = []
for symbol in old_symbols:
    pattern = re.compile(rf"`{re.escape(symbol)}`|\b{re.escape(symbol)}\b")
    for path in doc_files:
        for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            if pattern.search(line):
                residue.append({
                    "symbol": symbol,
                    "file": str(path),
                    "line": lineno,
                    "text": line.strip(),
                })

payload = {
    "pass_id": pass_id,
    "old_symbols": old_symbols,
    "authored_diff_paths": authored_diff_paths,
    "residue": residue,
    "corridor_objective": corridor_objective,
    "corridor_objective_status": objective_status,
    "summary": (
        f"{len(residue)} stale old-symbol references found."
        if residue else
        "No stale old-symbol references found in authored docs."
    ),
}
if objective_missing_fields:
    payload["corridor_objective_missing_fields"] = objective_missing_fields
if raw_ram_review_owner_update and (
    raw_ram_review_owner_update.get("updated")
    or raw_ram_review_owner_update.get("ambiguous_local_replacements")
):
    payload["raw_ram_review_owner_update"] = raw_ram_review_owner_update
scoped_overlay_symbols = scoped_overlay_raw_symbols(rename_rows_for_pass)
if scoped_overlay_symbols:
    payload["scoped_overlay_raw_symbols"] = scoped_overlay_symbols

raw_symbol_residue = []
if not residue:
    raw_symbol_residue = find_raw_symbol_residue(asm_file, rename_rows_for_pass)
    if raw_symbol_residue:
        payload["raw_symbol_residue"] = raw_symbol_residue
        payload["summary"] = (
            "Residual raw operands remain for RAM/ZP addresses renamed in this pass."
        )

raw_ram_review_update = None
if not residue and not raw_symbol_residue:
    raw_ram_review_update = update_raw_ram_review_on_closeout(
        doc_root,
        pass_id,
        rename_rows_for_pass,
    )
    if raw_ram_review_update:
        payload["raw_ram_review_update"] = raw_ram_review_update

print(json.dumps(payload, indent=2))

if residue:
    sys.exit(4)
if raw_symbol_residue:
    sys.exit(5)
PY
