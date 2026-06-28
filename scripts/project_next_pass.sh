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
FORMAT="${2:-text}"

if [[ "${FORMAT}" != "text" && "${FORMAT}" != "json" ]]; then
  echo "error: format must be text or json" >&2
  exit 2
fi

if [[ "${PROJECT_NEXT_PASS_AUTO_PREP:-1}" != "0" ]]; then
  PASS_CACHE_DIR="${DOC_ROOT}/inventory/pass"
  PREP_SCRIPT="${PROJECT_NEXT_PASS_PREP_SCRIPT:-${SCRIPT_DIR}/project_pass_prep.sh}"
  NEEDS_PREP=0
  PASS_CACHE_INPUTS=(
    "baseline_status.json"
    "xref_summary_all.json"
    "xref_summary_generic.json"
    "xref_with_data.json"
    "data_consumers.json"
  )
  for cache_name in "${PASS_CACHE_INPUTS[@]}"; do
    cache_path="${PASS_CACHE_DIR}/${cache_name}"
    if [[ ! -e "${cache_path}" || ! -s "${cache_path}" || "${ASM_FILE}" -nt "${cache_path}" ]]; then
      NEEDS_PREP=1
      break
    fi
  done
  if [[ "${NEEDS_PREP}" == "1" ]]; then
    echo "project-next-pass: refreshing missing, partial, or stale pass cache via project-pass-prep" >&2
    bash "${PREP_SCRIPT}" "$1" >&2
  fi
fi

python3 - "$1" "${FORMAT}" "${ASM_FILE}" "${WARN_BASELINE_FILE}" "${PROGRESS_SCORECARD_FILE}" "${DOC_ROOT}/inventory/unknowns.md" "${DOC_ROOT}/inventory/pass" "${DOC_ROOT}/inventory/raw_ram_review.csv" <<'PY'
import csv
import json
import os
import re
import sys
from bisect import bisect_right
from pathlib import Path

slug, out_format, asm_file, warn_file, scorecard_file, unknowns_file, pass_dir, raw_ram_review_path = sys.argv[1:]
GENERIC_RE = re.compile(r"^L[0-9A-F]{4}$")
GLOBAL_LABEL_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*|L[0-9A-F]{4}):\s*$")
DATA_DIRECTIVE_RE = re.compile(r"^\s*\.(?:DB|DW|BYTE|WORD|DS|INCBIN)\b", re.IGNORECASE)
MNEMONIC_RE = re.compile(r"^\s*([A-Za-z]{3}(?:\.[A-Za-z])?)\s+([^;]+?)(?:\s*;.*)?$")
RAW_LOWADDR_OPERAND_RE = re.compile(
    r"^(?:"
    r"\$([0-9A-F]{1,4})(?:,[XY])?"
    r"|\(\$([0-9A-F]{1,4})(?:,[XY])?\)(?:,Y)?"
    r"|\[\$([0-9A-F]{1,4})(?:,[XY])?\](?:,[XY])?"
    r")$",
    re.IGNORECASE,
)

WRITE_ONLY_MNEMONICS = {"STA", "STX", "STY"}
READWRITE_MNEMONICS = {"INC", "DEC", "ASL", "LSR", "ROL", "ROR"}

def load_json(path):
    p = Path(path)
    if not p.exists():
        return None
    with p.open("r", encoding="utf-8") as f:
        return json.load(f)

def read_text(path):
    p = Path(path)
    if not p.exists():
        return ""
    return p.read_text(encoding="utf-8")

def count_warning_lines(path):
    count = 0
    for line in read_text(path).splitlines():
        s = line.strip()
        if not s or s.startswith("#"):
            continue
        count += 1
    return count

def parse_unknowns(path):
    text = read_text(path)
    values = {}
    patterns = {
        "undocumented_callables": r"Undocumented callable procedures:\s+(\d+)\s*/\s*(\d+)",
        "noncompliant_data_labels": r"Noncompliant data labels .*:\s+(\d+)\s*/\s*(\d+)",
        "strict_active_raw_lowaddr": r"Strict active raw low-address operands:\s+(\d+)",
    }
    for key, pat in patterns.items():
        m = re.search(pat, text)
        if m:
            values[key] = int(m.group(1))
            if m.lastindex and m.lastindex >= 2:
                values[f"{key}_total"] = int(m.group(2))
    return values

def compute_lxxxx_counts(path):
    text = read_text(path)
    defs = len(re.findall(r"(?m)^L[0-9A-F]{4}:", text))
    occs = len(re.findall(r"\bL[0-9A-F]{4}\b", text))
    return defs, occs

def parse_scorecard_latest_row(path):
    rows = []
    for raw in read_text(path).splitlines():
        line = raw.strip()
        if not (line.startswith("|") and line.endswith("|")):
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        if not cells or cells[0] in {"pass_id", "---"}:
            continue
        if not cells[0].isdigit():
            continue
        rows.append(cells)
    if not rows:
        return None
    last = max(rows, key=lambda row: int(row[0]))
    return {
        "pass_id": int(last[0]),
        "focus": last[1],
        "labels_remaining": last[2],
    }

def status_from_baseline(baseline, key):
    if not baseline:
        return "unknown"
    return baseline.get("checks", {}).get(key, {}).get("status", "unknown")

def section_or_empty(summary, key):
    if not summary:
        return []
    return list(summary.get(key, []))

def label_map(summary):
    out = {}
    if not summary:
        return out
    for section in ("top_callables", "top_jump_targets", "top_data_labels"):
        for entry in summary.get(section, []):
            out[entry["label"]] = entry
    return out

def load_xref(path):
    data = load_json(path)
    if not data:
        return {"symbols": [], "references": []}
    return data

def build_symbol_def_map(xref):
    out = {}
    for sym in xref.get("symbols", []):
        name = sym.get("name")
        definition = sym.get("definition") or {}
        if not name or not definition:
            continue
        out[name] = {
            "file": definition.get("file"),
            "line": definition.get("line"),
            "cpu_address": definition.get("cpu_address"),
        }
    return out

def build_file_symbol_index(xref):
    out = {}
    for sym in xref.get("symbols", []):
        if sym.get("scope") != "global":
            continue
        definition = sym.get("definition") or {}
        file = definition.get("file")
        line = definition.get("line")
        name = sym.get("name")
        if not file or not line or not name:
            continue
        out.setdefault(file, []).append((int(line), name))
    for file, entries in out.items():
        entries.sort()
        out[file] = {
            "lines": [line for line, _ in entries],
            "names": [name for _, name in entries],
        }
    return out

def first_meaningful_line_after(lines, idx):
    for text in lines[idx:]:
        body = text.split(";", 1)[0].strip()
        if body:
            return body
    return ""

def data_labels_from_source(path):
    lines = load_file_lines(path)
    labels = set()
    for idx, text in enumerate(lines):
        m = GLOBAL_LABEL_RE.match(text)
        if not m:
            continue
        body = first_meaningful_line_after(lines, idx + 1)
        if DATA_DIRECTIVE_RE.match(body):
            labels.add(m.group(1))
    return labels

def build_source_owner_index(path):
    data_labels = data_labels_from_source(path)
    entries = [
        (entry["line"], entry["name"])
        for entry in build_global_symbol_list(path)
        if entry["name"] not in data_labels
    ]
    entries.sort()
    return {
        path: {
            "lines": [line for line, _ in entries],
            "names": [name for _, name in entries],
        }
    }

def find_lexical_owner(file_index, file, line):
    info = file_index.get(file)
    if not info or line is None:
        return None
    idx = bisect_right(info["lines"], int(line)) - 1
    if idx < 0:
        return None
    return info["names"][idx]

def build_ref_map(xref):
    out = {}
    for ref in xref.get("references", []):
        sym = ref.get("symbol")
        if not sym:
            continue
        out.setdefault(sym, []).append(ref)
    for refs in out.values():
        refs.sort(key=lambda r: (
            r.get("line", 0),
            r.get("column", 0),
            r.get("use_cpu_address", ""),
        ))
    return out

def load_data_consumers(path):
    data = load_json(path)
    if not data:
        return {}
    return {row["label"]: row for row in data}

def build_owner_ref_map(xref):
    out = {}
    for ref in xref.get("references", []):
        owner = ref.get("owner_routine")
        if not owner:
            continue
        out.setdefault(owner, []).append(ref)
    for refs in out.values():
        refs.sort(key=lambda r: (
            r.get("line", 0),
            r.get("column", 0),
            r.get("use_cpu_address", ""),
            r.get("symbol", ""),
        ))
    return out

def build_data_access_maps(xref):
    owner_reads = {}
    owner_writes = {}
    symbol_reads = {}
    symbol_writes = {}
    for row in xref.get("data_reads", []):
        owner = row.get("owner_routine")
        symbol = row.get("symbol")
        if owner and symbol:
            owner_reads.setdefault(owner, []).append(row)
            symbol_reads.setdefault(symbol, []).append(row)
    for row in xref.get("data_writes", []):
        owner = row.get("owner_routine")
        symbol = row.get("symbol")
        if owner and symbol:
            owner_writes.setdefault(owner, []).append(row)
            symbol_writes.setdefault(symbol, []).append(row)
    return owner_reads, owner_writes, symbol_reads, symbol_writes

def is_ram_symbol(symbol):
    if not symbol:
        return False
    return symbol.startswith("ZP_") or symbol.startswith("RAM_")

def summarize_outbound_edges(label, owner_ref_map, limit_per_kind=4):
    refs = owner_ref_map.get(label, [])
    grouped = {
        "calls": [],
        "jumps": [],
        "branches": [],
        "data_reads": [],
        "data_writes": [],
        "other": [],
    }
    seen = {key: set() for key in grouped}
    access_map = {
        "call": "calls",
        "jump": "jumps",
        "branch": "branches",
        "read": "data_reads",
        "write": "data_writes",
    }
    for ref in refs:
        symbol = ref.get("symbol")
        if not symbol or symbol == label:
            continue
        bucket = access_map.get(ref.get("access"), "other")
        key = (
            symbol,
            ref.get("opcode"),
            ref.get("addressing_mode"),
            ref.get("line"),
        )
        if key in seen[bucket]:
            continue
        seen[bucket].add(key)
        grouped[bucket].append({
            "symbol": symbol,
            "file": ref.get("file"),
            "line": ref.get("line"),
            "cpu_address": ref.get("use_cpu_address"),
            "opcode": ref.get("opcode"),
            "addressing_mode": ref.get("addressing_mode"),
            "access": ref.get("access"),
        })
    for key in grouped:
        grouped[key] = grouped[key][:limit_per_kind]
    return grouped

def load_excerpt(path, line, radius_before=4, radius_after=16):
    if not path or not line:
        return None
    p = Path(path)
    if not p.exists():
        return None
    lines = p.read_text(encoding="utf-8").splitlines()
    center = int(line)
    start = max(1, center - radius_before)
    end = min(len(lines), center + radius_after)
    excerpt_lines = []
    for lineno in range(start, end + 1):
        excerpt_lines.append({
            "line": lineno,
            "text": lines[lineno - 1],
        })
    return {
        "file": path,
        "start_line": start,
        "end_line": end,
        "lines": excerpt_lines,
    }

def adjacent_entrypoints(definition, globals_by_file):
    if not definition:
        return []
    file = definition.get("file")
    line = definition.get("line")
    if not file or not line:
        return []
    prev_name = find_previous_global_owner(globals_by_file, file, line)
    next_name, next_line = find_next_named_owner(globals_by_file, file, line)
    out = []
    if prev_name and not GENERIC_RE.match(prev_name):
        prev_line = None
        for entry in globals_by_file.get(file, []):
            if entry["name"] == prev_name:
                prev_line = entry["line"]
        out.append({
            "symbol": prev_name,
            "file": file,
            "line": prev_line,
            "role": "previous_entrypoint",
        })
    if next_name:
        out.append({
            "symbol": next_name,
            "file": file,
            "line": next_line,
            "role": "next_entrypoint",
        })
    return out

def data_anchor_hints(label, definition, consumer, globals_by_file):
    if not definition:
        return None
    read_sites = consumer.get("read_sites", []) if consumer else []
    write_sites = consumer.get("write_sites", []) if consumer else []
    routine_counts = {}
    for site in read_sites + write_sites:
        routine = site.get("routine")
        if not routine:
            continue
        routine_counts[routine] = routine_counts.get(routine, 0) + 1
    consumer_routines = [
        {"routine": routine, "site_count": count}
        for routine, count in sorted(routine_counts.items(), key=lambda kv: (-kv[1], kv[0]))[:4]
    ]
    return {
        "consumer_routines": consumer_routines,
        "dispatch_or_pointer_owners": consumer_routines,
        "adjacent_entrypoints": adjacent_entrypoints(definition, globals_by_file),
    }

def summarize_ram_provenance(label, owner_reads, owner_writes, symbol_reads, symbol_writes, limit_symbols=4, limit_other_owners=3):
    def summarize(rows):
        by_symbol = {}
        for row in rows:
            symbol = row.get("symbol")
            if not is_ram_symbol(symbol):
                continue
            by_symbol.setdefault(symbol, []).append(row)
        out = []
        for symbol, grouped in sorted(by_symbol.items(), key=lambda kv: (-len(kv[1]), kv[0]))[:limit_symbols]:
            other_readers = sorted({r.get("owner_routine") for r in symbol_reads.get(symbol, []) if r.get("owner_routine") and r.get("owner_routine") != label})[:limit_other_owners]
            other_writers = sorted({r.get("owner_routine") for r in symbol_writes.get(symbol, []) if r.get("owner_routine") and r.get("owner_routine") != label})[:limit_other_owners]
            out.append({
                "symbol": symbol,
                "site_count": len(grouped),
                "other_reading_routines": other_readers,
                "other_writing_routines": other_writers,
            })
        return out

    reads = summarize(owner_reads.get(label, []))
    writes = summarize(owner_writes.get(label, []))
    if not reads and not writes:
        return None
    return {
        "reads": reads,
        "writes": writes,
    }

def load_file_lines(path):
    p = Path(path)
    if not p.exists():
        return []
    return p.read_text(encoding="utf-8").splitlines()

def build_global_symbol_list(path):
    lines = load_file_lines(path)
    out = []
    for idx, text in enumerate(lines, start=1):
        m = GLOBAL_LABEL_RE.match(text)
        if not m:
            continue
        out.append({
            "name": m.group(1),
            "line": idx,
        })
    return out

def mnemonic_access_kind(mnemonic):
    root = (mnemonic or "").split(".", 1)[0].upper()
    if root in WRITE_ONLY_MNEMONICS:
        return "write"
    if root in READWRITE_MNEMONICS:
        return "readwrite"
    return "read"

def parse_raw_lowaddr_accesses(path, file_symbol_index):
    out = []
    for lineno, text in enumerate(load_file_lines(path), start=1):
        m = MNEMONIC_RE.match(text)
        if not m:
            continue
        mnemonic = m.group(1).upper()
        operand = m.group(2).strip()
        if not operand:
            continue
        parts = operand.split()
        if not parts:
            continue
        operand = parts[0]
        if operand.startswith("#"):
            continue
        m2 = RAW_LOWADDR_OPERAND_RE.match(operand)
        if not m2:
            continue
        raw = next((group for group in m2.groups() if group), "").upper()
        if not raw:
            continue
        try:
            addr = int(raw, 16)
        except ValueError:
            continue
        if addr > 0x0FFF:
            continue
        out.append({
            "addr": addr,
            "addr_hex": f"0x{addr:04x}",
            "operand": operand,
            "mnemonic": mnemonic,
            "access_kind": mnemonic_access_kind(mnemonic),
            "file": path,
            "line": lineno,
            "owner_routine": find_lexical_owner(file_symbol_index, path, lineno),
        })
    return out

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

RAW_RAM_STATUS_RANK = {
    "candidate": -1,
    "unreviewed": 0,
    "revisit": 1,
    "deferred": 2,
    "not_semantic_yet": 3,
    "symbolized": 4,
}
RAW_RAM_ACTIONABLE_STATUSES = {"candidate", "unreviewed", "revisit"}
# An owner block touching at least this many distinct raw addresses is "broad".
# Broad + carries deferred/mixed bytes => evidence container, not a pass target.
MIXED_ANCHOR_MIN_MEMBERS = 6

def normalize_raw_ram_status(row):
    return (row.get("status") or "unreviewed").strip() or "unreviewed"

def raw_ram_status_rank(status):
    return RAW_RAM_STATUS_RANK.get(status, 5)

def is_actionable_raw_ram_status(status):
    return status in RAW_RAM_ACTIONABLE_STATUSES

def load_raw_ram_review(path):
    p = Path(path)
    if not p.exists():
        return {}
    with p.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        rows = {}
        for row in reader:
            addr_hex = (row.get("addr_hex") or "").strip().lower()
            if not addr_hex:
                continue
            rows[addr_hex] = row
        return rows

def summarize_raw_owner_counts(rows, kind):
    out = {}
    for row in rows:
        owner = row.get("owner_routine")
        if not owner:
            continue
        if kind == "read" and row["access_kind"] not in {"read", "readwrite"}:
            continue
        if kind == "write" and row["access_kind"] not in {"write", "readwrite"}:
            continue
        out[owner] = out.get(owner, 0) + 1
    return ",".join(
        f"{name}:{count}" for name, count in sorted(out.items(), key=lambda kv: (-kv[1], kv[0]))[:4]
    )

def merge_raw_ram_review(candidates, review_rows):
    active_addrs = {c["addr_hex"] for c in candidates}
    merged_by_addr = {}
    by_addr = {c["addr_hex"]: c for c in candidates}
    for addr_hex, row in review_rows.items():
        # Preserve existing review rows as authored state. The generated pass
        # artifacts carry current owner/count details; rewriting those columns
        # here creates broad churn whenever unrelated owner names change.
        merged_by_addr[addr_hex] = {
            field: row.get(field, "") for field in RAW_RAM_REVIEW_FIELDS
        }
    for addr_hex in active_addrs - set(review_rows):
        candidate = by_addr[addr_hex]
        merged_by_addr[addr_hex] = {
            "addr_hex": addr_hex,
            "status": "unreviewed",
            "proposed_symbol": "",
            "notes": "",
            "last_pass_reviewed": "",
            "active": "yes",
            "operand_count": str(candidate["operand_count"]),
            "distinct_owner_count": str(candidate["distinct_owner_count"]),
            "read_count": str(candidate["read_count"]),
            "write_count": str(candidate["write_count"]),
            "top_readers": summarize_raw_owner_counts(candidate["sites"], "read"),
            "top_writers": summarize_raw_owner_counts(candidate["sites"], "write"),
        }

    def addr_sort_key(addr_hex):
        try:
            return (0, int(addr_hex, 16))
        except ValueError:
            return (1, addr_hex)

    ordered_addrs = list(review_rows)
    ordered_addrs.extend(
        addr for addr in sorted(active_addrs, key=addr_sort_key)
        if addr not in review_rows
    )
    return [merged_by_addr[addr] for addr in ordered_addrs]

def write_raw_ram_review(path, rows):
    p = Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)

    with p.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=RAW_RAM_REVIEW_FIELDS, lineterminator='\n')
        writer.writeheader()
        for row in rows:
            writer.writerow({field: row.get(field, "") for field in RAW_RAM_REVIEW_FIELDS})

def build_raw_ram_candidates(raw_accesses, review_rows, limit=None):
    by_addr = {}
    for row in raw_accesses:
        by_addr.setdefault(row["addr"], []).append(row)
    candidates = []
    for addr, rows in by_addr.items():
        owners = sorted({r["owner_routine"] for r in rows if r.get("owner_routine")})
        by_kind = {"read": 0, "write": 0, "readwrite": 0}
        for row in rows:
            by_kind[row["access_kind"]] = by_kind.get(row["access_kind"], 0) + 1
        lines = sorted(r["line"] for r in rows)
        compactness = (lines[-1] - lines[0]) if len(lines) > 1 else 0
        candidates.append({
            "label": f"raw_${addr:04X}",
            "kind": "raw_ram",
            "addr": addr,
            "addr_hex": f"0x{addr:04x}",
            "operand_count": len(rows),
            "distinct_owner_routines": owners,
            "distinct_owner_count": len(owners),
            "read_count": by_kind.get("read", 0) + by_kind.get("readwrite", 0),
            "write_count": by_kind.get("write", 0) + by_kind.get("readwrite", 0),
            "compactness": compactness,
            "sites": sorted(rows, key=lambda r: (r["line"], r["mnemonic"], r["operand"])),
        })
    def quality_band(candidate):
        owners = candidate["distinct_owner_count"]
        if owners <= 8:
            return 0
        if owners <= 16:
            return 1
        return 2

    def queue_rank(candidate):
        row = review_rows.get(candidate["addr_hex"], {})
        return raw_ram_status_rank(normalize_raw_ram_status(row))

    candidates.sort(key=lambda c: (queue_rank(c), quality_band(c), -c["operand_count"], c["distinct_owner_count"], c["compactness"], c["addr"]))
    if limit is None:
        return candidates
    return candidates[:limit]

def summarize_unnamed_ram_provenance(candidate, raw_accesses, limit_owners=4, limit_neighbors=4):
    addr = candidate["addr"]
    rows = [r for r in raw_accesses if r["addr"] == addr]
    if not rows:
        return None
    read_owners = {}
    write_owners = {}
    for row in rows:
        owner = row.get("owner_routine")
        if not owner:
            continue
        if row["access_kind"] in {"read", "readwrite"}:
            read_owners[owner] = read_owners.get(owner, 0) + 1
        if row["access_kind"] in {"write", "readwrite"}:
            write_owners[owner] = write_owners.get(owner, 0) + 1
    neighbors = []
    for other_addr in sorted({r["addr"] for r in raw_accesses if abs(r["addr"] - addr) <= 4 and r["addr"] != addr}):
        count = sum(1 for r in raw_accesses if r["addr"] == other_addr)
        neighbors.append({"addr_hex": f"0x{other_addr:04x}", "operand_count": count})
    return {
        "addr_hex": candidate["addr_hex"],
        "reads": [{"routine": k, "site_count": v} for k, v in sorted(read_owners.items(), key=lambda kv: (-kv[1], kv[0]))[:limit_owners]],
        "writes": [{"routine": k, "site_count": v} for k, v in sorted(write_owners.items(), key=lambda kv: (-kv[1], kv[0]))[:limit_owners]],
        "adjacent_raw_addresses": neighbors[:limit_neighbors],
    }

def find_previous_global_owner(globals_by_file, file, line):
    globals_list = globals_by_file.get(file, [])
    prev = None
    for entry in globals_list:
        if entry["line"] >= int(line):
            break
        prev = entry["name"]
    return prev

def find_next_named_owner(globals_by_file, file, line):
    globals_list = globals_by_file.get(file, [])
    for entry in globals_list:
        if entry["line"] <= int(line):
            continue
        if GENERIC_RE.match(entry["name"]):
            continue
        return entry["name"], entry["line"]
    return None, None

def classify_scope_barrier(label, refs, anchor_line, corridor_end):
    non_relative = {"call", "jump"}
    has_non_relative = False
    has_cross_scope_ref = False
    for ref in refs:
        access = ref.get("access")
        opcode = ref.get("opcode")
        if access in non_relative and opcode not in {"BNE", "BEQ", "BCC", "BCS", "BMI", "BPL", "BVC", "BVS"}:
            has_non_relative = True
        ref_line = int(ref.get("line") or 0)
        if ref_line < int(anchor_line) or ref_line > int(corridor_end):
            has_cross_scope_ref = True
    if has_non_relative:
        return "jump_target"
    if has_cross_scope_ref:
        return "shared_helper_entry"
    return "non_local_label"

def scope_barriers(file, open_range, anchor_line, anchor_symbol, globals_by_file, ref_map):
    if not file or not open_range or not anchor_line:
        return []
    globals_list = globals_by_file.get(file, [])
    start = open_range.get("start_line")
    end = open_range.get("end_line")
    if start is None or end is None:
        return []
    corridor_start = int(start)
    corridor_end = int(end)
    anchor_start = int(anchor_line)
    out = []
    for entry in globals_list:
        label = entry["name"]
        line = int(entry["line"])
        if line < corridor_start or line > corridor_end:
            continue
        if line <= anchor_start:
            continue
        refs = ref_map.get(label, [])
        out.append({
            "symbol": label,
            "line": line,
            "reason": classify_scope_barrier(label, refs, anchor_start, corridor_end),
        })
    return out

def localize_candidates(file, open_range, anchor_line, anchor_symbol, globals_by_file, ref_map, file_symbol_index):
    if not file or not open_range or not anchor_line:
        return []
    globals_list = globals_by_file.get(file, [])
    start = open_range.get("start_line")
    end = open_range.get("end_line")
    if start is None or end is None:
        return []
    corridor_start = int(start)
    corridor_end = int(end)
    anchor_start = int(anchor_line)
    candidates = []
    for entry in globals_list:
        line = entry["line"]
        label = entry["name"]
        if line < corridor_start or line > corridor_end:
            continue
        if not GENERIC_RE.match(label):
            continue
        refs = ref_map.get(label, [])
        owner = anchor_symbol
        safe = True
        reasons = []
        if line < anchor_start:
            safe = False
            reasons.append("definition lies outside anchor routine scope")
        for ref in refs:
            if ref.get("file") != file:
                safe = False
                reasons.append("referenced from another file")
                continue
            access = ref.get("access")
            opcode = ref.get("opcode")
            if access in {"call", "jump"} and opcode not in {"BNE", "BEQ", "BCC", "BCS", "BMI", "BPL", "BVC", "BVS"}:
                safe = False
                reasons.append("call/jump target")
            ref_line = int(ref.get("line") or 0)
            if ref_line < anchor_start or ref_line > corridor_end:
                safe = False
                reasons.append("references cross anchor routine scope")
        if not refs:
            reasons.append("no inbound references")
        reasons = sorted(set(reasons))
        candidates.append({
            "symbol": label,
            "definition_line": line,
            "definition_owner": owner,
            "reference_count": len(refs),
            "distinct_owner_routines": sorted({
                find_lexical_owner(file_symbol_index, ref.get("file"), ref.get("line"))
                for ref in refs if find_lexical_owner(file_symbol_index, ref.get("file"), ref.get("line"))
            }),
            "safe_localize": safe and bool(refs),
            "reason": "safe within one lexical owner" if safe and refs else "; ".join(reasons) if reasons else "not enough evidence",
        })
    return candidates

def fallback_generic_targets(all_summary):
    if not all_summary:
        return {"top_callables": [], "top_jump_targets": [], "top_data_labels": []}
    out = {}
    for section in ("top_callables", "top_jump_targets", "top_data_labels"):
        out[section] = [e for e in all_summary.get(section, []) if GENERIC_RE.match(e.get("label", ""))]
    return out

def top_named_routines(entry, limit=2):
    out = []
    for item in entry.get("top_referring_routines", []):
        routine = item.get("routine")
        if routine and not GENERIC_RE.match(routine):
            out.append(routine)
        if len(out) >= limit:
            break
    if not out:
        for item in entry.get("top_referring_routines", []):
            routine = item.get("routine")
            if routine:
                out.append(routine)
            if len(out) >= limit:
                break
    return out

def top_caller_sites(label, ref_map, symbol_defs, file_symbol_index, limit=3):
    out = []
    seen = set()
    for ref in ref_map.get(label, []):
        routine = find_lexical_owner(file_symbol_index, ref.get("file"), ref.get("line"))
        if not routine:
            continue
        defn = symbol_defs.get(routine, {})
        key = (routine, ref.get("file"), ref.get("line"))
        if key in seen:
            continue
        seen.add(key)
        out.append({
            "routine": routine,
            "call_file": ref.get("file"),
            "call_line": ref.get("line"),
            "call_cpu_address": ref.get("use_cpu_address"),
            "routine_file": defn.get("file"),
            "routine_line": defn.get("line"),
        })
        if len(out) >= limit:
            break
    return out

def nearby_symbol_sites(entry, symbol_defs, limit=6):
    out = []
    for label in entry.get("nearby_symbols", []):
        defn = symbol_defs.get(label)
        if not defn:
            continue
        out.append({
            "symbol": label,
            "file": defn.get("file"),
            "line": defn.get("line"),
            "cpu_address": defn.get("cpu_address"),
        })
        if len(out) >= limit:
            break
    return out

def recommended_open_range(def_line):
    if not def_line:
        return None
    start = max(1, int(def_line) - 20)
    end = int(def_line) + 40
    return {"start_line": start, "end_line": end}

def choose_recommended_pass(generic_summary, baseline, raw_ram_candidates, raw_ram_clusters):
    parity = status_from_baseline(baseline, "parity")
    docs = status_from_baseline(baseline, "docs_check")
    process = status_from_baseline(baseline, "process_check")
    metrics = (baseline or {}).get("metrics") or {}
    l_defs = metrics.get("lxxxx_definitions")
    raw_lowaddr = metrics.get("strict_active_raw_lowaddr")
    if parity == "fail":
        return {
            "type": "baseline_repair",
            "summary": "Parity is failing; restore a safe baseline before semantic work.",
            "reason": "project_compare is red, so a naming pass would layer on top of an unsafe baseline.",
        }
    if docs == "fail" or process == "fail":
        return {
            "type": "doc_closure",
            "summary": "Process or docs gates are failing; close that gap before starting the next semantic pass.",
            "reason": "Agents should not build new naming work on top of a red documentation/process baseline.",
        }
    if l_defs == 0 and raw_lowaddr and raw_lowaddr > 0 and raw_ram_clusters:
        top = raw_ram_clusters[0]
        return {
            "type": "raw_ram_symbolization",
            "summary": f"Candidate raw-RAM corridor: {top['cluster']}.",
            "reason": top["why"],
        }

    callables = section_or_empty(generic_summary, "top_callables")
    data_labels = section_or_empty(generic_summary, "top_data_labels")
    jump_targets = section_or_empty(generic_summary, "top_jump_targets")
    if callables:
        top = callables[0]
        callers = top_named_routines(top, 2)
        reason = (
            f"Shared caller path across {', '.join(callers)}."
            if callers else
            f"Highest-fanout unresolved callable with {top.get('total_ref_count', 0)} total refs."
        )
        return {
            "type": "procedure_naming",
            "summary": f"Candidate naming corridor starts at {top['label']}.",
            "reason": reason,
        }
    if data_labels:
        top = data_labels[0]
        consumers = top_named_routines(top, 2)
        reason = (
            f"Directly consumed by {', '.join(consumers)} and likely to unlock safer procedure naming."
            if consumers else
            f"Highest-fanout unresolved data declaration with {top.get('total_ref_count', 0)} direct refs."
        )
        return {
            "type": "table_first",
            "summary": f"Candidate table/data corridor starts at {top['label']}.",
            "reason": reason,
        }
    if jump_targets:
        top = jump_targets[0]
        return {
            "type": "local_cleanup",
            "summary": f"Candidate local-cleanup corridor starts at {top['label']}.",
            "reason": f"Highest-fanout unresolved jump/branch target with {top.get('total_ref_count', 0)} refs.",
        }
    return {
        "type": "doc_closure",
        "summary": "No strong unresolved high-fanout targets remain; prioritize documentation closure.",
        "reason": "The structured analyzer outputs did not surface a stronger corridor-level semantic pass.",
    }

def build_raw_ram_clusters(raw_ram_candidates, raw_ram_review, all_label_map, symbol_defs, ref_map, file_symbol_index, owner_ref_map, globals_by_file):
    by_owner = {}
    for candidate in raw_ram_candidates:
        review = raw_ram_review.get(candidate["addr_hex"], {}) or {}
        review_status = normalize_raw_ram_status(review)
        actionable = is_actionable_raw_ram_status(review_status)
        for site in candidate.get("sites", []):
            owner = site.get("owner_routine")
            if not owner:
                continue
            cluster = by_owner.setdefault(owner, {
                "owner": owner,
                "operand_count": 0,
                "actionable_operand_count": 0,
                "reviewed_context_operand_count": 0,
                "read_count": 0,
                "write_count": 0,
                "members": {},
            })
            cluster["operand_count"] += 1
            if actionable:
                cluster["actionable_operand_count"] += 1
            else:
                cluster["reviewed_context_operand_count"] += 1
            if site["access_kind"] in {"read", "readwrite"}:
                cluster["read_count"] += 1
            if site["access_kind"] in {"write", "readwrite"}:
                cluster["write_count"] += 1
            # An address active across more than one owner cannot take a safe
            # global name, but the proven local role here is a scoped-overlay
            # opportunity: alias it inside this owner while other owners' uses
            # stay raw and active. (See AGENTS.md scoped-overlay alias rules.)
            global_owner_count = candidate.get("distinct_owner_count", 0)
            member = cluster["members"].setdefault(candidate["addr_hex"], {
                "addr_hex": candidate["addr_hex"],
                "site_count": 0,
                "actionable_site_count": 0,
                "read_count": 0,
                "write_count": 0,
                "review_status": review_status,
                "actionable": actionable,
                "label": candidate["label"],
                "global_owner_count": global_owner_count,
                "scoped_overlay": actionable and global_owner_count > 1,
            })
            member["site_count"] += 1
            if actionable:
                member["actionable_site_count"] += 1
            if site["access_kind"] in {"read", "readwrite"}:
                member["read_count"] += 1
            if site["access_kind"] in {"write", "readwrite"}:
                member["write_count"] += 1

    clusters = []
    for owner, cluster in by_owner.items():
        members = sorted(
            cluster["members"].values(),
            key=lambda row: (
                not row["actionable"],
                -row["actionable_site_count"],
                -row["site_count"],
                raw_ram_status_rank(row["review_status"]),
                row["addr_hex"],
            ),
        )
        actionable_members = [row for row in members if row["actionable"]]
        if not actionable_members:
            continue
        if len(actionable_members) < 2 and cluster["actionable_operand_count"] < 4:
            continue
        definition = symbol_defs.get(owner, {})
        entry = all_label_map.get(owner, {})
        open_range = recommended_open_range(definition.get("line")) if definition else None
        scratch_members = sum(1 for row in actionable_members if int(row["addr_hex"], 16) <= 0x0007)
        # A broad owner block that already carries deferred/mixed bytes is an
        # evidence container, not a pass target: its actionable bytes are better
        # pursued as focused sub-corridors (often owned by other routines). Flag
        # it so it ranks below focused corridors and reads as "narrow this".
        is_mixed_anchor = (
            len(members) >= MIXED_ANCHOR_MIN_MEMBERS
            and cluster["reviewed_context_operand_count"] > 0
        )
        anchor_role = "mixed_anchor_evidence" if is_mixed_anchor else "actionable_corridor"
        scoped_overlay_members = [
            row["addr_hex"] for row in actionable_members if row.get("scoped_overlay")
        ]
        why = (
            f"{owner} carries {cluster['actionable_operand_count']} actionable raw low-address operand sites "
            f"across {len(actionable_members)} addresses"
        )
        if cluster["reviewed_context_operand_count"]:
            why += f"; {cluster['reviewed_context_operand_count']} reviewed/deferred sites remain as context"
        if scratch_members == len(actionable_members):
            why += "; this corridor is entirely inside the shared scratch window"
        elif scratch_members:
            why += f"; includes {scratch_members} shared scratch bytes"
        if is_mixed_anchor:
            why += (
                "; broad mixed owner block — treat as evidence, name the actionable "
                "bytes as focused sub-corridors and leave deferred bytes raw"
            )
        if scoped_overlay_members:
            why += (
                f"; {len(scoped_overlay_members)} byte(s) are cross-owner — scoped "
                "overlay alias here, leave other owners' uses raw"
            )
        if is_mixed_anchor:
            hint = {
                "kind": "narrow",
                "message": (
                    "Broad mixed anchor; pursue the actionable sub-corridor bytes "
                    "and keep deferred bytes as raw evidence."
                ),
                "actionable_addrs": [row["addr_hex"] for row in actionable_members[:8]],
            }
        elif scoped_overlay_members:
            hint = {
                "kind": "scoped_overlay",
                "message": (
                    "Cross-owner bytes here support a scoped overlay alias while "
                    "other owners' uses stay raw."
                ),
                "scoped_overlay_addrs": scoped_overlay_members[:8],
            }
        else:
            hint = None
        clusters.append({
            "cluster": f"{owner} corridor",
            "anchor": owner,
            "kind": "raw_ram_corridor",
            "anchor_role": anchor_role,
            "mixed_anchor": is_mixed_anchor,
            "scoped_overlay_candidates": scoped_overlay_members[:8],
            "hint": hint,
            "why": why,
            "summary": (
                f"{owner} is a broad mixed raw-RAM owner block; use it as evidence for focused sub-corridors."
                if is_mixed_anchor else
                f"{owner} is the densest unresolved focused raw-RAM owner corridor."
            ),
            "top_callers": top_named_routines(entry, 3),
            "definition": definition or None,
            "caller_sites": top_caller_sites(owner, ref_map, symbol_defs, file_symbol_index),
            "nearby_symbol_sites": nearby_symbol_sites(entry, symbol_defs),
            "recommended_open_range": open_range,
            "outbound_edges": summarize_outbound_edges(owner, owner_ref_map),
            "source_excerpt": load_excerpt(definition.get("file"), definition.get("line")) if definition else None,
            "data_anchor_hints": None,
            "ram_provenance": {
                "reads": [{"routine": owner, "site_count": cluster["read_count"]}] if cluster["read_count"] else [],
                "writes": [{"routine": owner, "site_count": cluster["write_count"]}] if cluster["write_count"] else [],
                "adjacent_raw_addresses": [
                    {"addr_hex": row["addr_hex"], "operand_count": row["site_count"]}
                    for row in members[:6]
                ],
            },
            "scope_barriers": scope_barriers(
                definition.get("file"),
                open_range,
                definition.get("line"),
                owner,
                globals_by_file,
                ref_map,
            ) if definition else [],
            "localize_candidates": localize_candidates(
                definition.get("file"),
                open_range,
                definition.get("line"),
                owner,
                globals_by_file,
                ref_map,
                file_symbol_index,
            ) if definition else [],
            "members": members[:8],
            "member_count": len(members),
            "actionable_member_count": len(actionable_members),
            "operand_count": cluster["operand_count"],
            "actionable_operand_count": cluster["actionable_operand_count"],
            "reviewed_context_operand_count": cluster["reviewed_context_operand_count"],
        })
    clusters.sort(key=lambda row: (
        row["mixed_anchor"],
        -row["actionable_operand_count"],
        -row["actionable_member_count"],
        -row["operand_count"],
        -row["member_count"],
        row["anchor"],
    ))
    if clusters:
        return clusters[:8]

    fallback = []
    for candidate in raw_ram_candidates[:8]:
        sites = candidate.get("sites", [])
        first_site = sites[0] if sites else {}
        read_counts = {}
        write_counts = {}
        for site in sites:
            owner = site.get("owner_routine")
            if not owner:
                continue
            if site["access_kind"] in {"read", "readwrite"}:
                read_counts[owner] = read_counts.get(owner, 0) + 1
            if site["access_kind"] in {"write", "readwrite"}:
                write_counts[owner] = write_counts.get(owner, 0) + 1
        definition = {
            "file": first_site.get("file"),
            "line": first_site.get("line"),
            "cpu_address": None,
        } if first_site else None
        callers = candidate.get("distinct_owner_routines", [])[:3]
        scoped_overlay = candidate["distinct_owner_count"] > 1
        fallback.append({
            "cluster": f"{candidate['label']} corridor",
            "anchor": candidate["label"],
            "kind": "raw_ram_corridor",
            "anchor_role": "actionable_corridor",
            "mixed_anchor": False,
            "scoped_overlay_candidates": [candidate["addr_hex"]] if scoped_overlay else [],
            "hint": {
                "kind": "scoped_overlay",
                "message": (
                    "Cross-owner byte; scoped overlay alias in one owner while "
                    "other owners' uses stay raw."
                ),
                "scoped_overlay_addrs": [candidate["addr_hex"]],
            } if scoped_overlay else None,
            "why": f"{candidate['operand_count']} active operand sites; {candidate['distinct_owner_count']} owner routines",
            "summary": f"{candidate['label']} remains unresolved.",
            "top_callers": callers,
            "definition": definition,
            "caller_sites": [
                {
                    "routine": row.get("owner_routine"),
                    "call_file": row.get("file"),
                    "call_line": row.get("line"),
                    "call_cpu_address": None,
                    "routine_file": row.get("file"),
                    "routine_line": row.get("line"),
                }
                for row in sites[:3]
            ],
            "nearby_symbol_sites": [],
            "recommended_open_range": recommended_open_range(definition.get("line")) if definition else None,
            "outbound_edges": {},
            "source_excerpt": load_excerpt(definition.get("file"), definition.get("line")) if definition else None,
            "data_anchor_hints": None,
            "ram_provenance": {
                "addr_hex": candidate["addr_hex"],
                "reads": [{"routine": owner, "site_count": count} for owner, count in sorted(read_counts.items(), key=lambda kv: (-kv[1], kv[0]))[:4]],
                "writes": [{"routine": owner, "site_count": count} for owner, count in sorted(write_counts.items(), key=lambda kv: (-kv[1], kv[0]))[:4]],
                "adjacent_raw_addresses": [],
            },
            "scope_barriers": [],
            "localize_candidates": [],
            "members": [{
                "addr_hex": candidate["addr_hex"],
                "site_count": candidate["operand_count"],
                "read_count": candidate["read_count"],
                "write_count": candidate["write_count"],
                "review_status": ((raw_ram_review.get(candidate["addr_hex"], {}) or {}).get("status") or "unreviewed"),
                "label": candidate["label"],
            }],
            "member_count": 1,
            "operand_count": candidate["operand_count"],
        })
    return fallback

def make_cluster_candidates(recommended_type, generic_summary, all_label_map, consumers_by_label, symbol_defs, ref_map, file_symbol_index, owner_ref_map, globals_by_file, owner_reads, owner_writes, symbol_reads, symbol_writes, raw_ram_candidates, raw_accesses, raw_ram_review, raw_ram_clusters):
    section_map = {
        "procedure_naming": "top_callables",
        "table_first": "top_data_labels",
        "local_cleanup": "top_jump_targets",
    }
    if recommended_type == "raw_ram_symbolization":
        return raw_ram_clusters
    section = section_map.get(recommended_type)
    if not section:
        return []
    base = section_or_empty(generic_summary, section)
    clusters = []
    seen = set()

    def add_cluster(label, kind, why, top, entry):
        if label in seen or len(clusters) >= 8:
            return
        seen.add(label)
        definition = symbol_defs.get(label, {})
        open_range = recommended_open_range(definition.get("line")) if definition else None
        members = [{
            "symbol": label,
            "kind": "anchor",
            "site_count": entry.get("total_ref_count", 0),
        }]
        for nearby in entry.get("nearby_symbols", []):
            if GENERIC_RE.match(nearby):
                members.append({
                    "symbol": nearby,
                    "kind": "nearby_generic",
                    "site_count": (all_label_map.get(nearby) or {}).get("total_ref_count", 0),
                })
            if len(members) >= 6:
                break
        clusters.append({
            "cluster": f"{label} corridor",
            "anchor": label,
            "kind": kind,
            "why": why,
            "summary": f"{label} is the default candidate corridor anchor for this pass type.",
            "top_callers": top,
            "definition": definition or None,
            "caller_sites": top_caller_sites(label, ref_map, symbol_defs, file_symbol_index),
            "nearby_symbol_sites": nearby_symbol_sites(entry, symbol_defs),
            "recommended_open_range": open_range,
            "outbound_edges": summarize_outbound_edges(label, owner_ref_map),
            "source_excerpt": load_excerpt(definition.get("file"), definition.get("line")) if definition else None,
            "data_anchor_hints": data_anchor_hints(label, definition, consumers_by_label.get(label), globals_by_file) if definition and kind == "data" else None,
            "ram_provenance": summarize_ram_provenance(label, owner_reads, owner_writes, symbol_reads, symbol_writes),
            "scope_barriers": scope_barriers(
                definition.get("file"),
                open_range,
                definition.get("line"),
                label,
                globals_by_file,
                ref_map,
            ) if definition else [],
            "localize_candidates": localize_candidates(
                definition.get("file"),
                open_range,
                definition.get("line"),
                label,
                globals_by_file,
                ref_map,
                file_symbol_index,
            ) if definition else [],
            "members": members,
            "member_count": len(members),
        })

    for entry in base[:6]:
        label = entry["label"]
        top = top_named_routines(entry, 2)
        if section == "top_callables":
            why = f"{entry.get('total_ref_count', 0)} total refs"
            if top:
                why += f"; top callers: {', '.join(top)}"
            add_cluster(label, "callable_corridor", why, top, entry)
        elif section == "top_data_labels":
            consumer = consumers_by_label.get(label, {})
            disps = consumer.get("observed_constant_displacements", [])
            why = f"{entry.get('total_ref_count', 0)} direct refs"
            if consumer:
                why += f"; {consumer.get('distinct_routine_count', 0)} routines"
                if disps:
                    why += f"; displacements {disps[:4]}"
            add_cluster(label, "data_corridor", why, top, entry)
        else:
            why = f"{entry.get('total_ref_count', 0)} branch/jump refs"
            if top:
                why += f"; top referrers: {', '.join(top)}"
            add_cluster(label, "jump_target_corridor", why, top, entry)
    return clusters

def make_follow_up(recommended_type, cluster_candidates):
    if not cluster_candidates:
        return "Re-run pass prep after the next edit batch and rebuild the corridor plan."
    first = cluster_candidates[0].get("anchor") or cluster_candidates[0].get("cluster") or "the same corridor"
    if recommended_type == "raw_ram_symbolization":
        return f"After {first}, keep working the same owner corridor only while fresh evidence supports stable semantics or explicit deferred/not-semantic review status."
    if recommended_type == "procedure_naming":
        return f"After {first}, stay in the same corridor and do a table-first pass on the newly clarified nearby data."
    if recommended_type == "table_first":
        return f"After {first}, rename the direct consumer procedures using the now-proven table structure."
    if recommended_type == "local_cleanup":
        return f"After {first}, continue local cleanup only while the same corridor still has dense branch-target churn."
    if recommended_type == "baseline_repair":
        return "Once baseline parity is green again, rerun pass prep before picking the next semantic target."
    return "After closure, rerun pass prep and refresh the next corridor plan."

baseline = load_json(os.path.join(pass_dir, "baseline_status.json"))
all_summary = load_json(os.path.join(pass_dir, "xref_summary_all.json"))
generic_summary = load_json(os.path.join(pass_dir, "xref_summary_generic.json"))
xref = load_xref(os.path.join(pass_dir, "xref_with_data.json"))
if generic_summary is None:
    generic_summary = fallback_generic_targets(all_summary)

all_label_map = label_map(all_summary) if all_summary else label_map(generic_summary)
consumers_by_label = load_data_consumers(os.path.join(pass_dir, "data_consumers.json"))
symbol_defs = build_symbol_def_map(xref)
file_symbol_index = build_file_symbol_index(xref)
source_owner_index = build_source_owner_index(asm_file)
ref_map = build_ref_map(xref)
owner_ref_map = build_owner_ref_map(xref)
owner_reads, owner_writes, symbol_reads, symbol_writes = build_data_access_maps(xref)
globals_by_file = {asm_file: build_global_symbol_list(asm_file)}
raw_accesses = parse_raw_lowaddr_accesses(asm_file, source_owner_index)
raw_ram_review = load_raw_ram_review(raw_ram_review_path)
all_raw_ram_candidates = build_raw_ram_candidates(raw_accesses, raw_ram_review, limit=None)
raw_ram_candidates = all_raw_ram_candidates[:12]
merged_raw_ram_review = merge_raw_ram_review(all_raw_ram_candidates, raw_ram_review)
write_raw_ram_review(raw_ram_review_path, merged_raw_ram_review)
raw_ram_clusters = build_raw_ram_clusters(
    all_raw_ram_candidates,
    raw_ram_review,
    all_label_map,
    symbol_defs,
    ref_map,
    file_symbol_index,
    owner_ref_map,
    globals_by_file,
)
notes = []
working_notes_path = Path(pass_dir).parent.parent / "WORKING_NOTES.md"
if baseline is None:
    notes.append("baseline status cache missing; run make project-pass-prep PROJECT=<slug> for full resume data")
if all_summary is None:
    notes.append("xref summary cache missing; candidate evidence is inventory-only")
if working_notes_path.exists():
    notes.append(
        "WORKING_NOTES.md present; keep the durable corridor plan there and persist that choice with make project-pass-start PROJECT=<slug> TARGET=<corridor_anchor_or_notes_plan>."
    )

metrics = (baseline or {}).get("metrics") or {}
if metrics:
    l_defs = metrics.get("lxxxx_definitions")
    l_occs = metrics.get("lxxxx_occurrences")
else:
    l_defs, l_occs = compute_lxxxx_counts(asm_file)
unknowns = parse_unknowns(unknowns_file)
undocumented_callables = metrics.get("undocumented_callables", unknowns.get("undocumented_callables"))
undocumented_callables_total = metrics.get("undocumented_callables_total", unknowns.get("undocumented_callables_total"))
noncompliant_data_labels = metrics.get("noncompliant_data_labels", unknowns.get("noncompliant_data_labels"))
noncompliant_data_labels_total = metrics.get("noncompliant_data_labels_total", unknowns.get("noncompliant_data_labels_total"))
warning_baseline_count = metrics.get("warning_baseline_count", count_warning_lines(warn_file))
last_pass = parse_scorecard_latest_row(scorecard_file)

def build_data_label_alternatives(generic_summary, consumers_by_label, limit=3):
    out = []
    for entry in section_or_empty(generic_summary, "top_data_labels")[:limit]:
        label = entry.get("label")
        if not label:
            continue
        consumer = consumers_by_label.get(label, {})
        out.append({
            "label": label,
            "kind": "data_label",
            "total_ref_count": entry.get("total_ref_count", 0),
            "distinct_routine_count": consumer.get("distinct_routine_count", 0),
            "why": (
                f"data-label/format debt with {entry.get('total_ref_count', 0)} refs; "
                "may be higher readability value than another small raw-RAM pass"
            ),
        })
    return out

CONFIDENCE_CAVEAT = (
    "Candidate evidence only: this tool ranks what is visible, not strategic "
    "project value. The operator selects the corridor objective."
)

recommended = choose_recommended_pass(generic_summary, baseline, raw_ram_candidates, raw_ram_clusters)
cluster_candidates = make_cluster_candidates(
    recommended["type"],
    generic_summary,
    all_label_map,
    consumers_by_label,
    symbol_defs,
    ref_map,
    file_symbol_index,
    owner_ref_map,
    globals_by_file,
    owner_reads,
    owner_writes,
    symbol_reads,
    symbol_writes,
    raw_ram_candidates,
    raw_accesses,
    raw_ram_review,
    raw_ram_clusters,
)
follow_up = make_follow_up(recommended["type"], cluster_candidates)

# Advisory (never fails): warn on stderr when the default/top candidate is a
# broad mixed anchor (evidence container). Its actionable bytes should be
# pursued as focused sub-corridors rather than the whole block as one pass.
if cluster_candidates and cluster_candidates[0].get("mixed_anchor"):
    top = cluster_candidates[0]
    addrs = (top.get("hint") or {}).get("actionable_addrs") or top.get("scoped_overlay_candidates") or []
    addr_hint = f" actionable bytes: {', '.join(addrs[:8])}." if addrs else ""
    print(
        f"warning: top candidate {top.get('anchor')} is a broad mixed anchor "
        "(evidence container, not a pass target); name its actionable bytes as "
        f"focused sub-corridors and leave deferred bytes raw.{addr_hint}",
        file=sys.stderr,
    )

# In raw-RAM mode, when the only remaining raw-RAM work is broad mixed anchors
# or small micro-pass clusters, surface data-label/format-debt candidates as
# alternatives so the operator can weigh a higher-readability corridor instead
# of another small raw-byte pass. Advisory; the operator still chooses.
strong_focused_raw = any(
    (not c.get("mixed_anchor")) and c.get("actionable_operand_count", 0) >= 4
    for c in raw_ram_clusters
)
alternative_candidates = []
if recommended["type"] == "raw_ram_symbolization" and not strong_focused_raw:
    alternative_candidates = build_data_label_alternatives(generic_summary, consumers_by_label)

payload = {
    "project": slug,
    "last_pass": last_pass or {"pass_id": None, "focus": "unknown"},
    "kpis": {
        "lxxxx_definitions": l_defs,
        "lxxxx_occurrences": l_occs,
        "undocumented_callables": undocumented_callables,
        "undocumented_callables_total": undocumented_callables_total,
        "noncompliant_data_labels": noncompliant_data_labels,
        "noncompliant_data_labels_total": noncompliant_data_labels_total,
        "warning_baseline_count": warning_baseline_count,
        "strict_active_raw_lowaddr": metrics.get("strict_active_raw_lowaddr", unknowns.get("strict_active_raw_lowaddr")),
    },
    "selection_strategy": "corridor_scan_with_working_notes",
    "baseline": {
        "docs_check": status_from_baseline(baseline, "docs_check"),
        "process_check": status_from_baseline(baseline, "process_check"),
        "parity": status_from_baseline(baseline, "parity"),
    },
    "recommended_pass": recommended,
    "cluster_candidates": cluster_candidates,
    "alternative_candidates": alternative_candidates,
    "confidence_caveat": CONFIDENCE_CAVEAT,
    "follow_up": follow_up,
    "raw_ram_review_file": raw_ram_review_path,
}
if notes:
    payload["notes"] = notes

next_pass_path = Path(pass_dir) / "next_pass.json"
next_pass_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

if out_format == "json":
    print(json.dumps(payload, indent=2))
    sys.exit(0)

print(f"Project: {slug}")
if payload["last_pass"]["pass_id"] is not None:
    print(f"Last pass: {payload['last_pass']['pass_id']} — {payload['last_pass']['focus']}")
else:
    print("Last pass: unknown")
print(
    "KPIs: "
    f"LXXXX {payload['kpis']['lxxxx_definitions']} / {payload['kpis']['lxxxx_occurrences']}, "
    f"undocumented callables {payload['kpis']['undocumented_callables']} / {payload['kpis']['undocumented_callables_total']}, "
    f"noncompliant data {payload['kpis']['noncompliant_data_labels']} / {payload['kpis']['noncompliant_data_labels_total']}, "
    f"raw lowaddr {payload['kpis'].get('strict_active_raw_lowaddr')}, "
    f"warning baseline {payload['kpis']['warning_baseline_count']}"
)
print(
    "Baseline: "
    f"docs {payload['baseline']['docs_check']}, "
    f"process {payload['baseline']['process_check']}, "
    f"parity {payload['baseline']['parity']}"
)
print()
print(f"Selection strategy: {payload['selection_strategy']}")
print("Candidate evidence (advisory; the operator selects the corridor objective):")
print(f"Default candidate pass: {payload['recommended_pass']['type']}")
print(f"Reason: {payload['recommended_pass']['reason']}")
print()
print("Candidate corridors:")
for target in payload["cluster_candidates"]:
    callers = ""
    if target.get("top_callers"):
        callers = f" | top: {', '.join(target['top_callers'])}"
    cluster_name = target.get("cluster") or target.get("anchor") or "corridor"
    role_tag = " [mixed-anchor evidence]" if target.get("mixed_anchor") else ""
    print(f"- {cluster_name} ({target['kind']}){role_tag} — {target['why']}{callers}")
    definition = target.get("definition") or {}
    if target.get("anchor"):
        print(f"  anchor: {target['anchor']}")
    hint = target.get("hint")
    if hint:
        print(f"  hint ({hint.get('kind')}): {hint.get('message')}")
    if target.get("scoped_overlay_candidates"):
        print(f"  scoped overlay: {', '.join(target['scoped_overlay_candidates'])}")
    if definition.get("file") and definition.get("line"):
        print(f"  definition: {definition['file']}:{definition['line']}")
    open_range = target.get("recommended_open_range")
    if definition.get("file") and open_range:
        print(
            f"  open range: {definition['file']}:{open_range['start_line']}-{open_range['end_line']}"
        )
    members = target.get("members") or []
    if members:
        print("  members:")
        for item in members[:6]:
            label = item.get("symbol") or item.get("addr_hex") or "unknown"
            extras = []
            if item.get("site_count") is not None:
                extras.append(f"sites {item['site_count']}")
            if item.get("review_status"):
                extras.append(f"status {item['review_status']}")
            if item.get("kind"):
                extras.append(item["kind"])
            print(f"    - {label}" + (f" ({'; '.join(extras)})" if extras else ""))
    caller_sites = target.get("caller_sites") or []
    if caller_sites:
        print("  callers:")
        for site in caller_sites:
            loc = f"{site['call_file']}:{site['call_line']}" if site.get("call_file") and site.get("call_line") else "unknown"
            print(f"    - {site['routine']} @ {loc}")
    nearby = target.get("nearby_symbol_sites") or []
    if nearby:
        print("  nearby:")
        for site in nearby[:4]:
            if site.get("file") and site.get("line"):
                print(f"    - {site['symbol']} @ {site['file']}:{site['line']}")
            else:
                print(f"    - {site['symbol']}")
    outbound = target.get("outbound_edges") or {}
    if any(outbound.get(k) for k in ("calls", "jumps", "branches", "data_reads", "data_writes", "other")):
        print("  outbound:")
        labels = (
            ("calls", "calls"),
            ("jumps", "jumps"),
            ("branches", "branches"),
            ("data_reads", "reads"),
            ("data_writes", "writes"),
            ("other", "other"),
        )
        for key, label in labels:
            items = outbound.get(key) or []
            if not items:
                continue
            rendered = []
            for item in items:
                loc = ""
                if item.get("file") and item.get("line"):
                    loc = f" @ {item['file']}:{item['line']}"
                rendered.append(f"{item['symbol']}{loc}")
            print(f"    - {label}: {', '.join(rendered)}")
    data_hints = target.get("data_anchor_hints") or {}
    if data_hints:
        consumers = data_hints.get("consumer_routines") or []
        adjacent = data_hints.get("adjacent_entrypoints") or []
        if consumers or adjacent:
            print("  data anchor hints:")
            for item in consumers[:4]:
                print(f"    - consumer: {item['routine']} ({item['site_count']} sites)")
            for item in adjacent[:4]:
                if item.get("file") and item.get("line"):
                    print(f"    - {item['role']}: {item['symbol']} @ {item['file']}:{item['line']}")
                else:
                    print(f"    - {item['role']}: {item['symbol']}")
    ram = target.get("ram_provenance") or {}
    if ram:
        print("  ram provenance:")
        if ram.get("addr_hex"):
            print(f"    - raw addr: {ram['addr_hex']}")
        for bucket in ("reads", "writes"):
            items = ram.get(bucket) or []
            if not items:
                continue
            rendered = []
            for item in items[:4]:
                if "symbol" in item:
                    extras = []
                    if item.get("other_reading_routines"):
                        extras.append("other readers: " + ", ".join(item["other_reading_routines"]))
                    if item.get("other_writing_routines"):
                        extras.append("other writers: " + ", ".join(item["other_writing_routines"]))
                    suffix = f" ({'; '.join(extras)})" if extras else ""
                    rendered.append(f"{item['symbol']} x{item['site_count']}{suffix}")
                else:
                    rendered.append(f"{item['routine']} x{item['site_count']}")
            print(f"    - {bucket}: {', '.join(rendered)}")
        neighbors = ram.get("adjacent_raw_addresses") or []
        if neighbors:
            rendered = [f"{item['addr_hex']} x{item['operand_count']}" for item in neighbors]
            print(f"    - adjacent: {', '.join(rendered)}")
    raw_hint = target.get("raw_ram_candidate") or {}
    if raw_hint:
        print("  raw RAM candidate:")
        print(
            f"    - {raw_hint['addr_hex']}: reads {raw_hint['read_count']}, writes {raw_hint['write_count']}, "
            f"owners {', '.join(raw_hint['distinct_owner_routines'][:4]) if raw_hint.get('distinct_owner_routines') else 'unknown'}"
        )
    localize = target.get("localize_candidates") or []
    barriers = target.get("scope_barriers") or []
    if barriers:
        print("  scope barriers:")
        for item in barriers[:6]:
            print(f"    - {item['symbol']} @ line {item['line']} ({item['reason']})")
    if localize:
        print("  localize:")
        for item in localize[:6]:
            state = "safe" if item.get("safe_localize") else "keep non-local"
            owner = item.get("definition_owner") or "unknown"
            print(
                f"    - {item['symbol']} ({state}; owner {owner}; refs {item['reference_count']})"
            )
            print(f"      reason: {item['reason']}")
    excerpt = target.get("source_excerpt")
    if excerpt:
        print("  excerpt:")
        for row in excerpt.get("lines", [])[:8]:
            print(f"    {row['line']:>5}: {row['text']}")
if payload.get("alternative_candidates"):
    print()
    print("Alternative candidates (consider if higher value than another small raw-RAM pass):")
    for alt in payload["alternative_candidates"]:
        print(f"- {alt['label']} ({alt['kind']}) — {alt['why']}")
print()
print(f"Immediate follow-up: {payload['follow_up']}")
print(f"Caveat: {payload['confidence_caveat']}")
if notes:
    print()
    print("Notes:")
    for note in notes:
        print(f"- {note}")
PY
