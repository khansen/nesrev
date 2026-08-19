#!/usr/bin/env python3
"""Advisory scan for opcode-like runs still represented as .DB data.

The scanner is intentionally evidence-only. Opcode-dense text, PPU packets,
graphics, pointer tables, and mixed code/data overlays can look executable, so
review the CSV before adding NESrev recovery controls.
"""

from __future__ import annotations

import argparse
import csv
import fnmatch
import json
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, TextIO


BANK_SIZE = 0x4000
MMC1_MAPPER = 1

GLOBAL_LABEL_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
L_BANKED_LABEL_RE = re.compile(r"^L([0-9A-Fa-f])([0-9A-Fa-f]{4})$")
L_CPU_LABEL_RE = re.compile(r"^L([0-9A-Fa-f]{4})$")
COMMENT_RE = re.compile(r"^\s*[#;]")


# Official 6502 opcode sizes. Illegal opcodes are intentionally absent.
OPCODE_SIZE = {
    0x00: 1, 0x01: 2, 0x05: 2, 0x06: 2, 0x08: 1, 0x09: 2, 0x0A: 1, 0x0D: 3, 0x0E: 3,
    0x10: 2, 0x11: 2, 0x15: 2, 0x16: 2, 0x18: 1, 0x19: 3, 0x1D: 3, 0x1E: 3,
    0x20: 3, 0x21: 2, 0x24: 2, 0x25: 2, 0x26: 2, 0x28: 1, 0x29: 2, 0x2A: 1, 0x2C: 3, 0x2D: 3, 0x2E: 3,
    0x30: 2, 0x31: 2, 0x35: 2, 0x36: 2, 0x38: 1, 0x39: 3, 0x3D: 3, 0x3E: 3,
    0x40: 1, 0x41: 2, 0x45: 2, 0x46: 2, 0x48: 1, 0x49: 2, 0x4A: 1, 0x4C: 3, 0x4D: 3, 0x4E: 3,
    0x50: 2, 0x51: 2, 0x55: 2, 0x56: 2, 0x58: 1, 0x59: 3, 0x5D: 3, 0x5E: 3,
    0x60: 1, 0x61: 2, 0x65: 2, 0x66: 2, 0x68: 1, 0x69: 2, 0x6A: 1, 0x6C: 3, 0x6D: 3, 0x6E: 3,
    0x70: 2, 0x71: 2, 0x75: 2, 0x76: 2, 0x78: 1, 0x79: 3, 0x7D: 3, 0x7E: 3,
    0x81: 2, 0x84: 2, 0x85: 2, 0x86: 2, 0x88: 1, 0x8A: 1, 0x8C: 3, 0x8D: 3, 0x8E: 3,
    0x90: 2, 0x91: 2, 0x94: 2, 0x95: 2, 0x96: 2, 0x98: 1, 0x99: 3, 0x9A: 1, 0x9D: 3,
    0xA0: 2, 0xA1: 2, 0xA2: 2, 0xA4: 2, 0xA5: 2, 0xA6: 2, 0xA8: 1, 0xA9: 2, 0xAA: 1, 0xAC: 3, 0xAD: 3, 0xAE: 3,
    0xB0: 2, 0xB1: 2, 0xB4: 2, 0xB5: 2, 0xB6: 2, 0xB8: 1, 0xB9: 3, 0xBA: 1, 0xBC: 3, 0xBD: 3, 0xBE: 3,
    0xC0: 2, 0xC1: 2, 0xC4: 2, 0xC5: 2, 0xC6: 2, 0xC8: 1, 0xC9: 2, 0xCA: 1, 0xCC: 3, 0xCD: 3, 0xCE: 3,
    0xD0: 2, 0xD1: 2, 0xD5: 2, 0xD6: 2, 0xD8: 1, 0xD9: 3, 0xDD: 3, 0xDE: 3,
    0xE0: 2, 0xE1: 2, 0xE4: 2, 0xE5: 2, 0xE6: 2, 0xE8: 1, 0xE9: 2, 0xEA: 1, 0xEC: 3, 0xED: 3, 0xEE: 3,
    0xF0: 2, 0xF1: 2, 0xF5: 2, 0xF6: 2, 0xF8: 1, 0xF9: 3, 0xFD: 3, 0xFE: 3,
}

TERMINATORS = {0x40, 0x4C, 0x60, 0x6C}
CODELIKE_OPS = {
    0x10, 0x20, 0x30, 0x4C, 0x60, 0x85, 0x8D, 0x90, 0xA0, 0xA2,
    0xA5, 0xA9, 0xAD, 0xB0, 0xC0, 0xC9, 0xD0, 0xE0, 0xF0,
}
REVIEW_MARKERS = (
    "REVIEW REQUIRED: intake auto-seed",
)


@dataclass(frozen=True)
class Span:
    label: str
    bank: int | None
    cpu: int | None
    output_offset: int | None
    line_start: int
    line_end: int
    data: tuple[int, ...]


@dataclass(frozen=True)
class EntryKey:
    bank: int | None
    cpu: int


@dataclass(frozen=True)
class DataRange:
    bank: int | None
    start: int
    end: int


@dataclass(frozen=True)
class DecodeRun:
    score: int
    offset: int
    length: int
    terminated: bool
    instruction_count: int
    codelike_count: int
    brk_count: int


def parse_listing_int(value: Any) -> int | None:
    if value is None:
        return None
    if isinstance(value, int):
        return value
    text = str(value).strip()
    if not text:
        return None
    if text.startswith("$"):
        text = "0x" + text[1:]
    try:
        return int(text, 0)
    except ValueError:
        return None


def parse_addr(raw: str) -> int | None:
    value = parse_listing_int(raw)
    return value if value is not None and 0 <= value <= 0xFFFF else None


def parse_bank(raw: str) -> int | None:
    value = parse_listing_int(raw)
    return value if value is not None and 0 <= value <= 0xFF else None


def run_xasm_listing(asm_file: Path) -> list[dict[str, Any]]:
    xasm_bin = os.environ.get("XASM_BIN", "xasm")
    with tempfile.TemporaryDirectory(prefix="orphan_opcode_scan_") as tmpdir:
        listing = os.path.join(tmpdir, "listing.json")
        out_bin = os.path.join(tmpdir, "out.bin")
        cmd = [
            xasm_bin,
            "--pure-binary",
            "-o",
            out_bin,
            "--listing=" + listing,
            "--listing-format=json",
            str(asm_file),
        ]
        try:
            subprocess.run(
                cmd,
                check=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
        except FileNotFoundError:
            print("error: xasm not found while running orphan opcode scan", file=sys.stderr)
            raise SystemExit(66)
        except subprocess.CalledProcessError as exc:
            print(f"error: xasm failed with exit code {exc.returncode}", file=sys.stderr)
            if exc.stdout:
                print("xasm stdout:", file=sys.stderr)
                print(exc.stdout.rstrip(), file=sys.stderr)
            if exc.stderr:
                print("xasm stderr:", file=sys.stderr)
                print(exc.stderr.rstrip(), file=sys.stderr)
            raise SystemExit(exc.returncode or 1)
        with open(listing, encoding="utf-8") as handle:
            return json.load(handle)["records"]


def read_ines_mapper(path: Path) -> int:
    data = path.read_bytes()
    if len(data) < 16 or data[:4] != b"NES\x1A":
        raise ValueError(f"{path} is not an iNES/NES 2.0 ROM")
    flags6 = data[6]
    flags7 = data[7]
    mapper = (flags6 >> 4) | (flags7 & 0xF0)
    if (flags7 & 0x0C) == 0x08 and len(data) >= 9:
        mapper |= (data[8] & 0x0F) << 8
    return mapper


def is_label_record(record: dict[str, Any]) -> bool:
    op = record.get("directive_or_opcode")
    return (
        record.get("addressing_mode") is None
        and not record.get("bytes_hex")
        and isinstance(op, str)
        and GLOBAL_LABEL_RE.match(op) is not None
    )


def is_db_record(record: dict[str, Any]) -> bool:
    return record.get("directive_or_opcode") == ".DB" and bool(record.get("bytes_hex"))


def record_cpu(record: dict[str, Any]) -> int | None:
    value = parse_listing_int(record.get("cpu_address_start"))
    return value if value is not None and 0 <= value <= 0xFFFF else None


def record_output_offset(record: dict[str, Any]) -> int | None:
    value = parse_listing_int(record.get("output_offset_start"))
    return value if value is not None and value >= 0 else None


def record_bytes(record: dict[str, Any]) -> list[int]:
    values: list[int] = []
    for item in record.get("bytes_hex") or []:
        value = parse_listing_int("0x" + str(item))
        if value is None or not 0 <= value <= 0xFF:
            return []
        values.append(value)
    return values


def label_address(label: str) -> tuple[int | None, int | None]:
    banked = L_BANKED_LABEL_RE.match(label)
    if banked:
        return int(banked.group(1), 16), int(banked.group(2), 16)
    cpu_only = L_CPU_LABEL_RE.match(label)
    if cpu_only:
        return None, int(cpu_only.group(1), 16)
    return None, None


def bank_for_span(label: str, output_offset: int | None, mapper: int | None) -> int | None:
    if mapper == MMC1_MAPPER and output_offset is not None:
        return output_offset // BANK_SIZE
    if mapper is not None:
        return None
    label_bank, _ = label_address(label)
    return label_bank


def label_for(bank: int | None, cpu: int | None) -> str:
    if cpu is None:
        return ""
    if bank is None:
        return f"L{cpu:04X}"
    return f"L{bank:X}{cpu:04X}"


def parse_spans(path: Path, mapper: int | None) -> list[Span]:
    records = run_xasm_listing(path)
    spans: list[Span] = []
    current_label: str | None = None
    current_span: Span | None = None
    current_bytes: list[int] = []

    def flush(line_end: int | None = None) -> None:
        nonlocal current_span, current_bytes
        if current_span is not None and current_bytes:
            spans.append(
                Span(
                    label=current_span.label,
                    bank=current_span.bank,
                    cpu=current_span.cpu,
                    output_offset=current_span.output_offset,
                    line_start=current_span.line_start,
                    line_end=line_end if line_end is not None else current_span.line_end,
                    data=tuple(current_bytes),
                )
            )
        current_span = None
        current_bytes = []

    for record in records:
        line = int(record.get("line") or 0)
        if is_label_record(record):
            flush(line - 1 if line else None)
            current_label = str(record["directive_or_opcode"])
            continue

        if not is_db_record(record):
            op = record.get("directive_or_opcode")
            if current_span is not None or record.get("bytes_hex"):
                flush(line - 1 if line else None)
            if record.get("bytes_hex") or (isinstance(op, str) and op.startswith(".")):
                current_label = None
            continue

        if current_label is None:
            flush(line - 1 if line else None)
            continue

        values = record_bytes(record)
        if not values:
            flush(line - 1 if line else None)
            continue

        cpu = record_cpu(record)
        output_offset = record_output_offset(record)
        line_start = line if line else 0
        bank = bank_for_span(current_label, output_offset, mapper)
        contiguous = (
            current_span is not None
            and current_span.label == current_label
            and current_span.output_offset is not None
            and output_offset == current_span.output_offset + len(current_bytes)
        )
        if current_span is None or not contiguous:
            flush(line - 1 if line else None)
            current_span = Span(
                label=current_label,
                bank=bank,
                cpu=cpu,
                output_offset=output_offset,
                line_start=line_start,
                line_end=line_start,
                data=(),
            )
            current_bytes = []
        current_bytes.extend(values)
        if current_span is not None:
            current_span = Span(
                label=current_span.label,
                bank=current_span.bank,
                cpu=current_span.cpu,
                output_offset=current_span.output_offset,
                line_start=current_span.line_start,
                line_end=line_start,
                data=(),
            )

    flush()
    return spans


def cleaned_control_rows(path: Path | None) -> list[list[str]]:
    if path is None or not path.exists():
        return []
    rows: list[list[str]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.split("#", 1)[0].split(";", 1)[0].strip()
        if not line or "|" not in line:
            continue
        rows.append([part.strip() for part in line.split("|")])
    return rows


def read_code_entries(path: Path | None) -> set[EntryKey]:
    entries: set[EntryKey] = set()
    if path is None or not path.exists():
        return entries
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.split("#", 1)[0].split(";", 1)[0].strip()
        if not line:
            continue
        if "|" in line:
            parts = [part.strip() for part in line.split("|")]
            if len(parts) < 2:
                continue
            bank = parse_bank(parts[0])
            addr = parse_addr(parts[1])
            if bank is not None and addr is not None:
                entries.add(EntryKey(bank, addr))
            continue
        addr = parse_addr(line)
        if addr is not None:
            entries.add(EntryKey(None, addr))
    return entries


def read_data_ranges(path: Path | None) -> list[DataRange]:
    ranges: list[DataRange] = []
    for parts in cleaned_control_rows(path):
        if len(parts) == 2:
            start = parse_addr(parts[0])
            length = parse_addr(parts[1])
            if start is not None and length is not None:
                ranges.append(DataRange(None, start, start + length))
        elif len(parts) >= 3:
            bank = parse_bank(parts[0])
            start = parse_addr(parts[1])
            length = parse_addr(parts[2])
            if bank is not None and start is not None and length is not None:
                ranges.append(DataRange(bank, start, start + length))
    return ranges


def read_inline_entries(path: Path | None) -> set[EntryKey]:
    entries: set[EntryKey] = set()
    for parts in cleaned_control_rows(path):
        bank: int | None = None
        address_parts = parts
        if len(parts) in (3, 4):
            maybe_bank = parse_bank(parts[0])
            if maybe_bank is not None and parse_addr(parts[1]) is not None:
                bank = maybe_bank
                address_parts = parts[1:]
        for part in address_parts:
            addr = parse_addr(part)
            if addr is not None:
                entries.add(EntryKey(bank, addr))
    return entries


def read_warning_rationale(path: Path | None) -> dict[str, str]:
    out: dict[str, str] = {}
    if path is None or not path.exists():
        return out
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip() or COMMENT_RE.match(line):
            continue
        if "|" not in line:
            continue
        label, rationale = line.split("|", 1)
        out[label.strip()] = rationale.strip()
    return out


def read_dispositions(path: Path | None) -> dict[str, str]:
    out: dict[str, str] = {}
    if path is None or not path.exists():
        return out
    with path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            label = (row.get("label") or "").strip()
            disposition = (row.get("disposition") or "").strip()
            if label and disposition:
                out[label] = disposition
    return out


def entry_matches(entries: set[EntryKey], bank: int | None, cpu: int | None) -> bool:
    if cpu is None:
        return False
    return EntryKey(bank, cpu) in entries or EntryKey(None, cpu) in entries


def range_matches(ranges: list[DataRange], bank: int | None, cpu: int | None) -> bool:
    if cpu is None:
        return False
    for data_range in ranges:
        if data_range.bank is not None and bank is not None and data_range.bank != bank:
            continue
        if data_range.bank is not None and bank is None:
            continue
        if data_range.start <= cpu < data_range.end:
            return True
    return False


def disposition_for(dispositions: dict[str, str], label: str) -> str:
    for pattern, disposition in dispositions.items():
        if fnmatch.fnmatchcase(label, pattern):
            return disposition
    return ""


def decode_run(data: tuple[int, ...], start: int) -> tuple[int, int, bool, int, int]:
    pos = start
    instruction_count = 0
    codelike_count = 0
    brk_count = 0
    terminated = False
    while pos < len(data):
        op = data[pos]
        size = OPCODE_SIZE.get(op)
        if size is None or pos + size > len(data):
            break
        instruction_count += 1
        if op in CODELIKE_OPS:
            codelike_count += 1
        if op == 0x00:
            brk_count += 1
            if instruction_count > 1:
                break
        pos += size
        if op in TERMINATORS:
            terminated = True
            break
    return pos - start, instruction_count, terminated, codelike_count, brk_count


def score_run(
    length: int,
    instruction_count: int,
    terminated: bool,
    codelike_count: int,
    brk_count: int,
) -> int:
    return length + instruction_count + codelike_count * 2 + (8 if terminated else 0) - brk_count * 6


def decode_candidates(span: Span, max_start_offset: int) -> list[DecodeRun]:
    runs: list[DecodeRun] = []
    for offset in range(min(len(span.data), max_start_offset + 1)):
        length, instruction_count, terminated, codelike_count, brk_count = decode_run(span.data, offset)
        runs.append(
            DecodeRun(
                score_run(length, instruction_count, terminated, codelike_count, brk_count),
                offset,
                length,
                terminated,
                instruction_count,
                codelike_count,
                brk_count,
            )
        )
    return runs


def candidate_is_interesting(
    run: DecodeRun,
    threshold: int,
    rationale: str,
    in_codeentries: bool,
    in_inlinecalls: bool,
    show_all: bool,
    force_marker: bool,
) -> bool:
    if show_all or in_codeentries or in_inlinecalls:
        return True
    if force_marker and any(marker in rationale for marker in REVIEW_MARKERS):
        return True
    if run.score >= threshold:
        return True
    return run.terminated and run.length >= 6 and run.codelike_count >= 2


def write_csv(
    handle: TextIO,
    spans: list[Span],
    warnings: dict[str, str],
    codeentries: set[EntryKey],
    dataranges: list[DataRange],
    inlinecalls: set[EntryKey],
    dispositions: dict[str, str],
    min_size: int,
    threshold: int,
    max_start_offset: int,
    show_all: bool,
) -> int:
    writer = csv.writer(handle)
    writer.writerow(
        [
            "score",
            "span_label",
            "candidate_label",
            "bank",
            "candidate_cpu",
            "candidate_offset",
            "span_size",
            "line_start",
            "line_end",
            "is_best",
            "warning_rationale",
            "in_codeentries",
            "in_datarange",
            "in_inlinecalls",
            "data_blob_disposition",
            "candidate_len",
            "terminated",
            "instruction_count",
            "codelike_count",
            "brk_count",
            "bytes",
        ]
    )
    count = 0
    for span in spans:
        if len(span.data) < min_size:
            continue
        candidates = decode_candidates(span, max_start_offset)
        best = max(candidates, key=lambda run: run.score, default=None)
        for run in candidates:
            candidate_cpu = span.cpu + run.offset if span.cpu is not None else None
            candidate_label = label_for(span.bank, candidate_cpu)
            rationale = warnings.get(candidate_label, warnings.get(span.label, ""))
            in_codeentries = entry_matches(codeentries, span.bank, candidate_cpu)
            in_inlinecalls = entry_matches(inlinecalls, span.bank, candidate_cpu)
            if not candidate_is_interesting(
                run,
                threshold,
                rationale,
                in_codeentries,
                in_inlinecalls,
                show_all,
                force_marker=(best is not None and run.offset == best.offset),
            ):
                continue
            byte_preview = " ".join(
                f"{byte:02X}" for byte in span.data[run.offset:run.offset + min(run.length, 24)]
            )
            writer.writerow(
                [
                    run.score,
                    span.label,
                    candidate_label,
                    "" if span.bank is None else span.bank,
                    "" if candidate_cpu is None else f"${candidate_cpu:04X}",
                    run.offset,
                    len(span.data),
                    span.line_start,
                    span.line_end,
                    "yes" if best is not None and run.offset == best.offset else "",
                    rationale,
                    "yes" if in_codeentries else "",
                    "yes" if range_matches(dataranges, span.bank, candidate_cpu) else "",
                    "yes" if in_inlinecalls else "",
                    disposition_for(dispositions, span.label),
                    run.length,
                    "yes" if run.terminated else "",
                    run.instruction_count,
                    run.codelike_count,
                    run.brk_count,
                    byte_preview,
                ]
            )
            count += 1
    return count


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--asm", type=Path, required=True, help="Assembly source to scan")
    parser.add_argument("--warnings", type=Path, help="WARNING_BASELINE.txt for rationale context")
    parser.add_argument("--codeentries", type=Path, help="NESrev codeentries.txt for configured-code context")
    parser.add_argument("--dataranges", type=Path, help="NESrev dataranges.csv for configured-data context")
    parser.add_argument("--inlinecalls", type=Path, help="NESrev inlinecalls.csv for configured-dispatch context")
    parser.add_argument("--data-blob-dispositions", type=Path, help="data_blob_dispositions.csv for reviewed-data context")
    parser.add_argument("--ref-nes", type=Path, help="Reference ROM for mapper-aware label context")
    parser.add_argument("--mapper", type=int, help="Mapper override when --ref-nes is unavailable")
    parser.add_argument("--out", type=Path, help="Write CSV to this path instead of stdout")
    parser.add_argument("--min-size", type=int, default=12, help="Minimum .DB span size to scan")
    parser.add_argument("--threshold", type=int, default=22, help="Minimum score for unmarked candidates")
    parser.add_argument("--max-start-offset", type=int, default=64, help="Highest offset inside each span to try as a code start")
    parser.add_argument("--all", action="store_true", help="Emit every scanned .DB candidate offset")
    args = parser.parse_args(argv)

    if args.min_size < 1:
        parser.error("--min-size must be >= 1")
    if args.threshold < 0:
        parser.error("--threshold must be >= 0")
    if args.max_start_offset < 0:
        parser.error("--max-start-offset must be >= 0")
    if args.mapper is not None and args.mapper < 0:
        parser.error("--mapper must be >= 0")
    if not args.asm.exists():
        parser.error(f"--asm does not exist: {args.asm}")
    mapper = args.mapper
    if mapper is None and args.ref_nes is not None:
        if not args.ref_nes.exists():
            parser.error(f"--ref-nes does not exist: {args.ref_nes}")
        try:
            mapper = read_ines_mapper(args.ref_nes)
        except ValueError as exc:
            parser.error(str(exc))

    spans = parse_spans(args.asm, mapper)
    warnings = read_warning_rationale(args.warnings)
    codeentries = read_code_entries(args.codeentries)
    dataranges = read_data_ranges(args.dataranges)
    inlinecalls = read_inline_entries(args.inlinecalls)
    dispositions = read_dispositions(args.data_blob_dispositions)

    if args.out is None:
        write_csv(
            sys.stdout,
            spans,
            warnings,
            codeentries,
            dataranges,
            inlinecalls,
            dispositions,
            args.min_size,
            args.threshold,
            args.max_start_offset,
            args.all,
        )
        return 0

    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", encoding="utf-8", newline="") as handle:
        count = write_csv(
            handle,
            spans,
            warnings,
            codeentries,
            dataranges,
            inlinecalls,
            dispositions,
            args.min_size,
            args.threshold,
            args.max_start_offset,
            args.all,
        )
    print(f"orphan-opcode candidates: {count}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
