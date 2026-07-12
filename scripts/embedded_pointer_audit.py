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
LABEL_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*):")
RAW_BYTE_RE = re.compile(r"^(\$[0-9A-Fa-f]{1,2}|%[01]{1,8}|[0-9]{1,3})$")


def parse_int(value: str | int) -> int:
    if isinstance(value, int):
        return value
    return int(str(value), 16)


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


def is_raw_db_record(record: dict) -> bool:
    if record.get("directive_or_opcode") != ".DB" or not record.get("bytes_hex"):
        return False
    source = (record.get("source_text") or "")
    text = strip_label(source).split(";", 1)[0].strip()
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


def in_same_window(bank: int, address: int) -> bool:
    if bank == 7:
        return 0xC000 <= address <= 0xFFFF
    return 0x8000 <= address <= 0xBFFF


def find_monotonic_runs(
    spans: list[dict],
    label_by_bank_cpu: dict[tuple[int, int], str],
    min_run: int,
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
                    if not (0x8000 <= addr <= 0xFFFF):
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
                        same = sum(1 for a in targets if in_same_window(bank, a))
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
                        })
                    i = j
                else:
                    i += 2
    return hits


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


def pointer_store_proof(lines: list[str], owner: str, routine: str) -> str:
    start, end = routine_block(lines, routine)
    if start < 0:
        return ""
    block = lines[start:end]
    owner_re = re.escape(owner)
    for i, line in enumerate(block):
        if not re.search(rf"\bLDA\s+{owner_re}(\b|\+)", line):
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
            if not re.search(rf"\bLDA\s+{owner_re}\+1\b", block[j]):
                continue
            for k in range(j + 1, min(j + 4, len(block))):
                if re.search(rf"\bSTA\s+{re.escape(hi_symbol)}\b", block[k]):
                    deref_re = re.compile(rf"[\[\(]{re.escape(lo_symbol)}[\]\)]")
                    if any(deref_re.search(src_line) for src_line in lines):
                        return f"{routine}: stores {owner}/+1 into {lo_symbol}/{hi_symbol}; {lo_symbol} is dereferenced"
    return ""


def confirm_candidates(
    hits: list[dict],
    patterns: list[dict],
    label_cpu: dict[str, int],
    asm_lines: list[str],
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
        for pattern in patterns_by_label.get(owner, []):
            displacement = int(pattern.get("displacement", 0))
            if label_cpu[owner] + displacement != hit["cpu"]:
                continue
            proof = pointer_store_proof(asm_lines, owner, pattern.get("routine", ""))
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

    spans, label_cpu, label_by_bank_cpu = build_raw_spans(records, min_run)
    hits = find_monotonic_runs(spans, label_by_bank_cpu, min_run)
    strong = [
        h for h in hits
        if h["same_window"] >= 0.7 * h["count"] or h["labeled"] >= 0.3 * h["count"]
    ]
    asm_lines = asm_path.read_text(encoding="utf-8").splitlines()
    confirmed = confirm_candidates(strong, patterns, label_cpu, asm_lines)

    print(f"embedded_pointer_raw_runs_total={len(hits)}")
    print(f"embedded_pointer_raw_runs_strong={len(strong)}")
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
