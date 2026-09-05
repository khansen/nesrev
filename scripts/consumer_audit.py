"""Small building blocks for project-owned, bounded consumer audits.

Caller reachability, record grammar and scheduler invariants remain local proof
obligations. These helpers do not infer a 6502 control-flow model.
"""

from __future__ import annotations

import hashlib
import json
import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path


class AuditError(ValueError):
    pass


def integer(value, minimum, maximum, field):
    if type(value) is not int or not minimum <= value <= maximum:
        raise AuditError(f"{field} must be an integer in {minimum}..{maximum}")
    return value


def adc8(left, right, carry=0):
    total = integer(left, 0, 255, "left") + integer(right, 0, 255, "right") + integer(carry, 0, 1, "carry")
    return total & 255, int(total > 255)


def sbc8(left, right, carry=1):
    total = integer(left, 0, 255, "left") - integer(right, 0, 255, "right") - (1 - integer(carry, 0, 1, "carry"))
    return total & 255, int(total >= 0)


def walk_u8(initial, step):
    """Visit before stepping; step returns the next byte index or None to stop.

    The index must be the complete state of this deterministic model. If carry,
    phase or another channel affects the successor, model that state locally.
    """
    visited, seen = [], set()
    index = integer(initial, 0, 255, "initial index")
    while index is not None:
        integer(index, 0, 255, "next index")
        if index in seen:
            raise AuditError(f"index model cycles at {index}; termination not established")
        seen.add(index)
        visited.append(index)
        index = step(index)
    return visited


@dataclass(frozen=True)
class Span:
    """Half-open offsets in one explicitly chosen address/file-offset domain."""
    start: int
    end: int

    def __post_init__(self):
        if type(self.start) is not int or type(self.end) is not int or not 0 <= self.start <= self.end:
            raise AuditError("span requires nonnegative integer start <= end")

    def contains(self, offset):
        return self.start <= offset < self.end


def read_footprint(allocation, selected_record, reads):
    """Report observed/modelled reads without equating any of the three domains."""
    reads = list(reads)
    if any(type(value) is not int or value < 0 for value in reads):
        raise AuditError("read offsets must be nonnegative integers in the chosen domain")
    unique = sorted(set(reads))
    return {
        "allocation": [allocation.start, allocation.end],
        "selected_record": [selected_record.start, selected_record.end],
        "read_count": len(reads),
        "unique_read_offsets": unique,
        "outside_allocation": [value for value in unique if not allocation.contains(value)],
        "outside_selected_record": [value for value in unique if not selected_record.contains(value)],
    }


class Assembly:
    """One assembled image and its structured symbol definitions.

    Constructing from supplied outputs does not establish freshness. Use
    assemble() for executable audits, or retain the caller's explicit fresh-build
    precondition when adapting an existing pure inspector.
    """
    def __init__(self, binary, xref, provenance=None):
        self.binary = binary
        self.xref = xref
        self.symbols = {}
        for symbol in xref["symbols"]:
            if symbol["defined"]:
                name = symbol["name"]
                if name in self.symbols:
                    raise AuditError(f"duplicate defined symbol: {name}")
                self.symbols[name] = symbol["definition"]
        self.provenance = provenance

    def definition(self, name):
        if name not in self.symbols:
            raise AuditError(f"missing defined symbol: {name}")
        return self.symbols[name]

    def offset(self, name):
        return integer(self.definition(name).get("output_offset"), 0, len(self.binary), f"{name} output offset")

    def value(self, name):
        definition = self.definition(name)
        value = definition.get("value")
        if value is None:
            try:
                value = int(definition["cpu_address"], 0)
            except (KeyError, TypeError, ValueError) as exc:
                raise AuditError(f"{name} has no numeric value/address") from exc
        if type(value) is not int:
            raise AuditError(f"{name} has no integer value")
        return value

    def unique_local(self, name):
        matches = [symbol for symbol in self.symbols if symbol.split("#")[0] == name]
        if len(matches) != 1:
            raise AuditError(f"expected one scoped anchor {name}, found {len(matches)}")
        return matches[0]

    def data(self, name, size, delta=0):
        integer(size, 0, len(self.binary), "read size")
        if type(delta) is not int:
            raise AuditError("read delta must be an integer")
        start = self.offset(name) + delta
        if start < 0 or start + size > len(self.binary):
            raise AuditError(f"{name}: requested bytes escape assembled output")
        return self.binary[start:start + size]

    def require_bytes(self, name, expected, delta=0):
        if not expected:
            raise AuditError("instruction contracts must not be empty")
        if self.data(name, len(expected), delta) != bytes(expected):
            raise AuditError(f"{name}: instruction contract changed; review the consumer model")


def assemble(source, *, cwd=None, assembler="xasm"):
    """Build binary, xref and listing together in fresh scratch; never use caches."""
    directory = Path(cwd or Path.cwd()).resolve()
    source = (directory / source).resolve()
    executable = shutil.which(assembler)
    if executable is None:
        raise AuditError(f"assembler not found: {assembler}")
    executable = str(Path(executable).resolve())
    with tempfile.TemporaryDirectory(prefix="consumer-audit-") as scratch:
        base = Path(scratch)
        binary, xref, listing = (base / name for name in ("image.bin", "xref.json", "listing.json"))
        command = [executable, "--pure-binary", "-o", str(binary),
                   f"--xref={xref}", "--xref-format=json", "--xref-include-locals=true",
                   f"--listing={listing}", "--listing-format=json", str(source)]
        result = subprocess.run(command, cwd=directory, capture_output=True, text=True)
        if result.returncode:
            raise AuditError(f"assembler exit {result.returncode}: {result.stderr.strip() or result.stdout.strip()}")
        try:
            payload, symbols, records = binary.read_bytes(), xref.read_bytes(), listing.read_bytes()
            json.loads(records)
            provenance = {
                "source": str(source), "assembler": executable,
                "assembler_sha256": hashlib.sha256(Path(executable).read_bytes()).hexdigest(),
                "binary_sha256": hashlib.sha256(payload).hexdigest(),
                "xref_sha256": hashlib.sha256(symbols).hexdigest(),
                "listing_sha256": hashlib.sha256(records).hexdigest(),
            }
            return Assembly(payload, json.loads(symbols), provenance)
        except (OSError, ValueError, KeyError, TypeError) as exc:
            raise AuditError(f"assembler did not produce valid binary/structured evidence: {exc}") from exc
