#!/usr/bin/env python3
"""Audit raw .DB spans for unrelocated ROM pointer tables.

The monotonic byte-run scan is intentionally advisory unless xasm's indexed
access analysis also proves paired-byte reads at the same table address and the
consumer stores the pair into a ZP pointer that is later dereferenced.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path


BANK_SIZE = 0x4000
DEFAULT_MIN_RUN = 6
MAX_TABLE_EXTENT = 0x400  # generous per-table extent for anchor-range matching
LABEL_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*):")
RAW_BYTE_RE = re.compile(r"^(\$[0-9A-Fa-f]{1,2}|%[01]{1,8}|[0-9]{1,3})$")
BARE_HEX_ADDRESS_RE = re.compile(r"^[0-9A-Fa-f]{4}$")


def parse_int(value: str | int) -> int:
    if isinstance(value, int):
        return value
    text = str(value).strip()
    if text.startswith("$"):
        return int(text[1:], 16)
    if text.lower().startswith("0x"):
        return int(text, 16)
    if re.search(r"[A-Fa-f]", text):
        return int(text, 16)
    if BARE_HEX_ADDRESS_RE.fullmatch(text):
        hex_value = int(text, 16)
        if 0x8000 <= hex_value <= 0xFFFF:
            return hex_value
    return int(text, 10)


def split_operands(payload: str) -> list[str]:
    operands: list[str] = []
    cur: list[str] = []
    depth = 0
    for ch in payload:
        if ch == "(":
            depth += 1
        elif ch == ")" and depth > 0:
            depth -= 1
        if ch == "," and depth == 0:
            operands.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    if cur or payload.endswith(","):
        operands.append("".join(cur).strip())
    return operands


def line_label(source_text: str) -> str:
    match = LABEL_RE.match((source_text or "").strip())
    return match.group(1) if match else ""


def strip_label(source_text: str) -> str:
    return LABEL_RE.sub("", source_text or "", count=1)


def strip_comment(source_text: str) -> str:
    return (source_text or "").split(";", 1)[0]


def is_raw_db_record(record: dict) -> bool:
    if record.get("directive_or_opcode") != ".DB" or not record.get("bytes_hex"):
        return False
    source = (record.get("source_text") or "")
    text = strip_comment(strip_label(source)).strip()
    if not re.match(r"^\.DB(\s|$)", text, re.IGNORECASE):
        return False
    payload = re.sub(r"^\.DB\s*", "", text, count=1, flags=re.IGNORECASE).strip()
    if "<" in payload or ">" in payload:
        return False
    operands = split_operands(payload)
    return bool(operands) and all(RAW_BYTE_RE.match(op) for op in operands)


def run_xasm_analysis(asm_file: str, workdir: str) -> tuple[list[dict], list[dict]]:
    listing = os.path.join(workdir, "listing.json")
    index_patterns = os.path.join(workdir, "index_patterns.json")
    out_bin = os.path.join(workdir, "out.bin")
    cmd = [
        "xasm",
        "--pure-binary",
        "-o",
        out_bin,
        "--listing=" + listing,
        "--listing-format=json",
        "--analyze-index-patterns",
        "--index-patterns-output=" + index_patterns,
        "--index-patterns-format=json",
        asm_file,
    ]
    try:
        subprocess.run(cmd, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    except FileNotFoundError:
        print("error: xasm not found while running embedded pointer audit", file=sys.stderr)
        raise SystemExit(66)
    except subprocess.CalledProcessError as exc:
        print(f"error: xasm analysis failed with exit code {exc.returncode}", file=sys.stderr)
        if exc.stdout:
            print("xasm stdout:", file=sys.stderr)
            print(exc.stdout.rstrip(), file=sys.stderr)
        if exc.stderr:
            print("xasm stderr:", file=sys.stderr)
            print(exc.stderr.rstrip(), file=sys.stderr)
        raise SystemExit(exc.returncode or 1)
    with open(listing, encoding="utf-8") as f:
        records = json.load(f)["records"]
    with open(index_patterns, encoding="utf-8") as f:
        patterns = json.load(f)
    return records, patterns


def prg_bank_count(records: list[dict]) -> int:
    banks = [
        r["output_offset_start"] // BANK_SIZE
        for r in records
        if r.get("output_offset_start") is not None
    ]
    return max(banks) + 1 if banks else 0


def build_raw_spans(records: list[dict], min_run: int) -> tuple[list[dict], dict[str, int], dict[tuple[int, int], str]]:
    records = [r for r in records if r.get("output_offset_start") is not None]
    records.sort(key=lambda r: r["output_offset_start"])

    label_cpu: dict[str, int] = {}
    labels_by_offset: dict[int, str] = {}
    label_by_bank_cpu: dict[tuple[int, int], str] = {}
    for record in records:
        label = line_label(record.get("source_text") or "")
        if not label:
            continue
        off = record["output_offset_start"]
        cpu = parse_int(record["cpu_address_start"])
        bank = off // BANK_SIZE
        if label not in label_cpu:
            label_cpu[label] = cpu
            labels_by_offset[off] = label
            label_by_bank_cpu[(bank, cpu)] = label

    spans: list[dict] = []
    cur: dict | None = None
    prev_end: int | None = None

    def flush() -> None:
        nonlocal cur
        if cur and len(cur["bytes"]) >= 2 * min_run:
            spans.append(cur)
        cur = None

    for record in records:
        off = record["output_offset_start"]
        label = line_label(record.get("source_text") or "")
        raw_db = is_raw_db_record(record)
        if label and not raw_db:
            if cur is not None:
                cur["labels"].append((off, label))
            continue

        if raw_db:
            bank = off // BANK_SIZE
            cpu = parse_int(record["cpu_address_start"])
            if cur is not None and (prev_end is None or off != prev_end + 1 or bank != cur["bank"]):
                flush()
            if cur is None:
                cur = {"bank": bank, "bytes": [], "labels": []}
                if off in labels_by_offset:
                    cur["labels"].append((off, labels_by_offset[off]))
                elif label:
                    cur["labels"].append((off, label))
            for i, byte_hex in enumerate(record["bytes_hex"]):
                cur["bytes"].append((off + i, cpu + i, int(byte_hex, 16)))
            prev_end = record["output_offset_end"]
        else:
            flush()
            prev_end = None
    flush()

    return spans, label_cpu, label_by_bank_cpu


def compute_bank_windows(records: list[dict]) -> dict[int, tuple[int, int]]:
    """Per-bank PRG window inferred from where the bank assembles (its .ORG).

    Mapper-agnostic: each 16 KB PRG bank occupies one of the two NES PRG windows
    ($8000-$BFFF or $C000-$FFFF; CPU-memory-map constants, not game-specific),
    selected by the bank's minimum CPU address (its .ORG).

    If at most one bank sits in the low window, no two banks overlap there: the
    image is flat (NROM-128/256), all banks are simultaneously mapped, and any
    occupied window is a valid target — so every bank gets the union window.
    NROM-256 (32 KB) therefore yields ($8000, $FFFF), and pointers in the last
    bank to $8000-$BFFF are accepted. If several banks share the low window they
    are switchable (e.g. MMC1) and each is scoped to its own half; a switchable
    bank still reaches the shared fixed bank via in_same_window(). NROM-128 at
    $C000 yields ($C000, $FFFF), so the unused $8000-$BFFF mirror is rejected.
    """
    base: dict[int, int] = {}
    for record in records:
        off = record.get("output_offset_start")
        if off is None:
            continue
        bank = off // BANK_SIZE
        cpu = parse_int(record["cpu_address_start"])
        base[bank] = min(base.get(bank, 0xFFFF), cpu)
    low_banks = [b for b, lo in base.items() if lo < 0xC000]
    windows: dict[int, tuple[int, int]] = {}
    if len(low_banks) <= 1:  # flat image: no switchable overlap in the low window
        any_low = any(lo < 0xC000 for lo in base.values())
        any_high = any(lo >= 0xC000 for lo in base.values())
        union = (0x8000 if any_low else 0xC000, 0xFFFF if any_high else 0xBFFF)
        for bank in base:
            windows[bank] = union
    else:  # switchable banks: scope each to its own half
        for bank, lo in base.items():
            windows[bank] = (0xC000, 0xFFFF) if lo >= 0xC000 else (0x8000, 0xBFFF)
    return windows


def in_same_window(
    bank: int,
    address: int,
    bank_windows: dict[int, tuple[int, int]],
    fixed_bank: int,
) -> bool:
    """A pointer in `bank` may target its own assembled window or the shared
    fixed bank's window. Windows come from compute_bank_windows()."""
    own = bank_windows.get(bank)
    if own and own[0] <= address <= own[1]:
        return True
    if fixed_bank != bank:
        fixed = bank_windows.get(fixed_bank)
        if fixed and fixed[0] <= address <= fixed[1]:
            return True
    return False


def find_monotonic_runs(
    spans: list[dict],
    label_by_bank_cpu: dict[tuple[int, int], str],
    min_run: int,
    bank_windows: dict[int, tuple[int, int]],
    fixed_bank: int,
) -> list[dict]:
    hits: list[dict] = []
    for span in spans:
        bytes_ = span["bytes"]
        bank = span["bank"]
        seen: list[tuple[int, int]] = []
        for align in (0, 1):
            i = align
            while i + 1 < len(bytes_):
                targets: list[int] = []
                j = i
                last = -1
                while j + 1 < len(bytes_):
                    addr = bytes_[j][2] | (bytes_[j + 1][2] << 8)
                    if not in_same_window(bank, addr, bank_windows, fixed_bank):
                        break
                    if addr < last or (last >= 0 and addr - last > 0x1000):
                        break
                    targets.append(addr)
                    last = addr
                    j += 2
                if len(targets) >= min_run:
                    start_off = bytes_[i][0]
                    end_off = bytes_[j - 1][0]
                    if not any(not (end_off < a or start_off > z) for a, z in seen):
                        seen.append((start_off, end_off))
                        owner = None
                        for label_off, name in span["labels"]:
                            if label_off <= start_off:
                                owner = name
                        same = sum(1 for a in targets if in_same_window(bank, a, bank_windows, fixed_bank))
                        labeled = sum(1 for a in targets if (bank, a) in label_by_bank_cpu)
                        hits.append({
                            "owner": owner,
                            "bank": bank,
                            "cpu": bytes_[i][1],
                            "count": len(targets),
                            "target_min": min(targets),
                            "target_max": max(targets),
                            "same_window": same,
                            "labeled": labeled,
                            "start_off": start_off,
                            "end_off": end_off,
                            "kind": "monotonic",
                        })
                    i = j
                else:
                    i += 2
    return hits


def nearest_label(label_by_bank_cpu: dict[tuple[int, int], str], bank: int, cpu: int) -> str | None:
    best_name = None
    best_cpu = -1
    for (b, c), name in label_by_bank_cpu.items():
        if b == bank and c <= cpu and c > best_cpu:
            best_cpu = c
            best_name = name
    return best_name


def find_pointer_struct_runs(
    spans: list[dict],
    label_by_bank_cpu: dict[tuple[int, int], str],
    bank_windows: dict[int, tuple[int, int]],
    fixed_bank: int,
    min_run: int,
    covered: list[tuple[int, int]],
) -> list[dict]:
    """Improvement 2: non-monotonic pointer structs.

    A struct of pointers to different tables is not sorted, so the monotonic
    scan skips it. Flag stride-2 raw runs where every pair resolves in-window,
    are not monotonic, and are not already covered by a monotonic run. These are
    advisory candidates; confirmation happens via struct_copy_deref_proof.
    """
    hits: list[dict] = []
    for span in spans:
        bytes_ = span["bytes"]
        bank = span["bank"]
        for align in (0, 1):
            i = align
            while i + 1 < len(bytes_):
                targets: list[int] = []
                j = i
                while j + 1 < len(bytes_):
                    addr = bytes_[j][2] | (bytes_[j + 1][2] << 8)
                    if not in_same_window(bank, addr, bank_windows, fixed_bank):
                        break
                    targets.append(addr)
                    j += 2
                if len(targets) >= min_run:
                    start_off = bytes_[i][0]
                    end_off = bytes_[j - 1][0]
                    monotonic = all(targets[k] <= targets[k + 1] for k in range(len(targets) - 1))
                    overlaps = any(a <= start_off and end_off <= z for a, z in covered)
                    if not monotonic and not overlaps:
                        owner = nearest_label(label_by_bank_cpu, bank, bytes_[i][1])
                        labeled = sum(1 for a in targets if (bank, a) in label_by_bank_cpu)
                        hits.append({
                            "owner": owner,
                            "bank": bank,
                            "cpu": bytes_[i][1],
                            "count": len(targets),
                            "target_min": min(targets),
                            "target_max": max(targets),
                            "same_window": len(targets),
                            "labeled": labeled,
                            "start_off": start_off,
                            "end_off": end_off,
                            "kind": "struct",
                        })
                    i = j
                else:
                    i += 2  # alignment handled by the outer loop; keep runtime linear
    return hits


def struct_copy_deref_proof(asm_lines: list[str], owner: str, owner_cpu: int, aliases: dict[str, str]) -> str:
    """Improvement 3: confirm a struct candidate when the block is block-copied
    into a ZP region (by label, alias, or CPU address) and that ZP pointer is
    later dereferenced `[zp],Y`."""
    code = [strip_comment(line) for line in asm_lines]
    name_alt = "|".join(re.escape(n) for n in names_for_owner(owner, aliases))
    src_re = re.compile(rf"\bLDA\s+(?:{name_alt}|\${owner_cpu:04X})\s*,\s*[XY]\b")
    dest_re = re.compile(r"\bSTA\s+([A-Za-z_]\w*)\s*,\s*[XY]\b")
    for i, line in enumerate(code):
        if not src_re.search(line):
            continue
        for j in range(i, min(i + 4, len(code))):
            match = dest_re.search(code[j])
            if match:
                zp = match.group(1)
                deref = re.compile(rf"[\[\(]{re.escape(zp)}[\]\)]")
                if any(deref.search(x) for x in code):
                    return f"block copied from {owner} into {zp} (indexed) and dereferenced as [{zp}]"
    return ""


EQU_ALIAS_RE = re.compile(r"^\s*([A-Za-z_]\w*)\s+\.EQU\s+([A-Za-z_]\w*)\s*(?:;.*)?$", re.IGNORECASE)


def build_equ_aliases(asm_lines: list[str]) -> dict[str, str]:
    """Improvement 4: map `<alias> .EQU <label>` so a consumer that reads a
    table through an alias (e.g. `Table .EQU TableBankN`) still matches the
    owner label. Fully generic — driven by the .EQU lines in the asm."""
    aliases: dict[str, str] = {}
    for line in asm_lines:
        match = EQU_ALIAS_RE.match(line)
        if match:
            aliases[match.group(1)] = match.group(2)
    return aliases


def names_for_owner(owner: str, aliases: dict[str, str]) -> list[str]:
    names = {owner}
    for alias, target in aliases.items():
        if target == owner:
            names.add(alias)
    return sorted(names)


def routine_block(lines: list[str], routine: str) -> tuple[int, int]:
    start = -1
    for i, line in enumerate(lines):
        if re.match(rf"^\s*{re.escape(routine)}:\s*$", line):
            start = i
            break
    if start < 0:
        return -1, -1
    end = len(lines)
    for i in range(start + 1, len(lines)):
        if LABEL_RE.match(lines[i]) and not lines[i].lstrip().startswith("@@"):
            end = i
            break
    return start, end


def pointer_store_proof(lines: list[str], owner: str, routine: str, aliases: dict[str, str]) -> str:
    start, end = routine_block(lines, routine)
    if start < 0:
        return ""
    block = [strip_comment(line) for line in lines[start:end]]
    code_lines = [strip_comment(line) for line in lines]
    alt = "|".join(re.escape(n) for n in names_for_owner(owner, aliases))
    owner_lo_load_re = re.compile(rf"\bLDA\s+(?:{alt})(?:\b|\s*,[XY]\b|\+)")
    owner_hi_load_re = re.compile(rf"\bLDA\s+(?:{alt})\+1(?:\b|\s*,[XY]\b)")
    for i, line in enumerate(block):
        if not owner_lo_load_re.search(line):
            continue
        lo_symbol = ""
        for j in range(i + 1, min(i + 4, len(block))):
            match = re.search(r"\bSTA\s+([A-Za-z_][A-Za-z0-9_]*PtrLo)\b", block[j])
            if match:
                lo_symbol = match.group(1)
                break
        if not lo_symbol:
            continue
        hi_symbol = lo_symbol[:-2] + "Hi"
        for j in range(i + 1, min(i + 10, len(block))):
            if not owner_hi_load_re.search(block[j]):
                continue
            for k in range(j + 1, min(j + 4, len(block))):
                if re.search(rf"\bSTA\s+{re.escape(hi_symbol)}\b", block[k]):
                    deref_re = re.compile(rf"[\[\(]{re.escape(lo_symbol)}[\]\)]")
                    if any(deref_re.search(src_line) for src_line in code_lines):
                        return f"{routine}: stores {owner}/+1 into {lo_symbol}/{hi_symbol}; {lo_symbol} is dereferenced"
    return ""


def confirm_candidates(
    hits: list[dict],
    patterns: list[dict],
    label_cpu: dict[str, int],
    asm_lines: list[str],
    aliases: dict[str, str],
) -> list[dict]:
    patterns_by_label: dict[str, list[dict]] = {}
    for pattern in patterns:
        if pattern.get("access_pattern") != "paired_byte_reads":
            continue
        patterns_by_label.setdefault(pattern.get("table_label", ""), []).append(pattern)

    confirmed: list[dict] = []
    for hit in hits:
        owner = hit.get("owner")
        if not owner or owner not in label_cpu:
            continue
        candidate_patterns: list[dict] = []
        for name in names_for_owner(owner, aliases):
            candidate_patterns += patterns_by_label.get(name, [])
        for pattern in candidate_patterns:
            displacement = int(pattern.get("displacement", 0))
            anchor = label_cpu[owner] + displacement
            # Improvement 5: composite/shared-heavy tables fragment, so the
            # detected run can start mid-table. Confirm when the run start falls
            # within the table extent of the paired-read anchor, not only at it.
            if not (anchor <= hit["cpu"] <= anchor + MAX_TABLE_EXTENT):
                continue
            proof = pointer_store_proof(asm_lines, owner, pattern.get("routine", ""), aliases)
            if proof:
                enriched = dict(hit)
                enriched["consumer_proof"] = proof
                confirmed.append(enriched)
                break
    return confirmed


def main() -> int:
    if len(sys.argv) not in (2, 3):
        print("usage: embedded_pointer_audit.py <asm_file> [min_run]", file=sys.stderr)
        return 64

    asm_path = Path(sys.argv[1])
    if not asm_path.is_file():
        print(f"error: asm file not found: {asm_path}", file=sys.stderr)
        return 65

    min_run = int(sys.argv[2]) if len(sys.argv) == 3 else DEFAULT_MIN_RUN
    with tempfile.TemporaryDirectory(prefix="nesrev_embedded_ptr.") as workdir:
        records, patterns = run_xasm_analysis(str(asm_path), workdir)

    fixed_bank = prg_bank_count(records) - 1
    bank_windows = compute_bank_windows(records)
    spans, label_cpu, label_by_bank_cpu = build_raw_spans(records, min_run)
    hits = find_monotonic_runs(spans, label_by_bank_cpu, min_run, bank_windows, fixed_bank)
    strong = [
        h for h in hits
        if h["same_window"] >= 0.7 * h["count"] or h["labeled"] >= 0.3 * h["count"]
    ]
    asm_lines = asm_path.read_text(encoding="utf-8").splitlines()
    aliases = build_equ_aliases(asm_lines)
    confirmed = confirm_candidates(strong, patterns, label_cpu, asm_lines, aliases)

    covered = [(h["start_off"], h["end_off"]) for h in hits]
    struct_candidates = find_pointer_struct_runs(
        spans, label_by_bank_cpu, bank_windows, fixed_bank, min_run, covered
    )
    seen_struct: set[tuple] = set()
    for hit in struct_candidates:
        owner = hit.get("owner")
        if not owner or owner not in label_cpu:
            continue
        key = (owner, hit["cpu"])
        if key in seen_struct:
            continue
        proof = struct_copy_deref_proof(asm_lines, owner, label_cpu[owner], aliases)
        if proof:
            seen_struct.add(key)
            enriched = dict(hit)
            enriched["consumer_proof"] = proof
            confirmed.append(enriched)

    print(f"embedded_pointer_raw_runs_total={len(hits)}")
    print(f"embedded_pointer_raw_runs_strong={len(strong)}")
    print(f"embedded_pointer_struct_candidates={len(struct_candidates)}")
    print(f"embedded_pointer_confirmed_unrelocated={len(confirmed)}")

    if confirmed:
        for hit in confirmed[:20]:
            print(
                "FAIL: raw embedded pointer table candidate "
                f"{hit['owner']} bank={hit['bank']} cpu=${hit['cpu']:04X} "
                f"ptrs={hit['count']} targets=${hit['target_min']:04X}-${hit['target_max']:04X}; "
                f"{hit['consumer_proof']}",
                file=sys.stderr,
            )
        if len(confirmed) > 20:
            print(f"FAIL: {len(confirmed) - 20} additional confirmed candidates omitted", file=sys.stderr)
        return 68

    print("OK: embedded pointer raw-run audit passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
