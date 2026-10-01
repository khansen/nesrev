#!/usr/bin/env python3
"""Check named raw pointer tables using a validated xasm listing and data xref.

Names are policy hints, not consumer/dataflow proof. See TOOLING.md's
pointer-table relocation gate for boundaries, exclusions and exit modes.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path
import re
import sys
import tempfile

import analysis_bundle as analysis
from split_pointer_targets import split_counterpart

NAME_RE = re.compile(r'(PtrTable|PointerTable|PtrTbl|PtrList|PointerList|Pointers|Ptrs)', re.I)
SELECTOR_RE = re.compile(r'(?:Ptr|Pointer)[A-Z]?By[A-Z0-9]\w*$')
ADDRESS_RE = re.compile(r'0x[0-9A-Fa-f]{4}')
MIN_WORDS = 2
PRG_RATIO = 0.6
USAGE = 'usage: pointer_table_body_check.py <asm_file> [--strict|--strict-whole-body]'


@lru_cache(maxsize=16384)
def named_table(name):
    return bool(NAME_RE.search(name) or SELECTOR_RE.search(name)
                or split_counterpart(name, True) or split_counterpart(name, False))


@lru_cache(maxsize=65536)
def address(value):
    analysis.require(isinstance(value, str) and ADDRESS_RE.fullmatch(value),
                     'invalid pointer-table address')
    return int(value, 16)


@dataclass
class Body:
    start: int
    cpu: int
    labels: list = field(default_factory=list)
    values: list = field(default_factory=list)
    symbolic: bool = False
    opaque: bool = False
    named: bool = False


def table_bodies(xref, listing, binary):
    """Group consecutive declarations and contiguous data; never read source_text."""
    definitions = {}
    for symbol in xref['symbols']:
        analysis.require(isinstance(symbol, dict), 'invalid xref symbol')
        if symbol.get('kind') != 'label' or symbol.get('scope') != 'global':
            continue
        name, definition = symbol.get('name'), symbol.get('definition')
        analysis.require(isinstance(name, str), 'invalid label name')
        if definition is None:
            continue
        analysis.require(isinstance(definition, dict), f'invalid label definition: {name}')
        if definition.get('file') is None:
            continue
        analysis.require(name not in definitions, f'ambiguous label definition: {name}')
        analysis.require(isinstance(definition.get('file'), str)
                         and type(definition.get('line')) is int
                         and type(definition.get('column')) is int
                         and (definition.get('output_offset') is None
                              or type(definition['output_offset']) is int),
                         f'invalid label definition: {name}')
        definitions[name] = definition

    # Position joins include references owned by another same-address alias.
    # Listing .DB nodes may merge multiple source statements.
    references = {}
    for record in xref['data_directive_references']:
        analysis.require(isinstance(record, dict), 'invalid data reference')
        if record.get('directive') != '.DB' or record.get('use_output_offset') is None:
            continue
        offset = record['use_output_offset']
        analysis.require(type(offset) is int and 0 <= offset < len(binary)
                         and record.get('width_bytes') == 1
                         and type(record.get('emitted_value')) is int
                         and binary[offset] == record['emitted_value'], 'invalid data reference bytes')
        analysis.require(offset not in references, 'ambiguous data reference position')
        references[offset] = record

    tables, seen = {}, set()
    current = None
    for record in listing['records']:
        kind, raw = record['directive_or_opcode'], record['bytes_hex']
        start, cpu = record['output_offset_start'], address(record['cpu_address_start'])
        values = bytes.fromhex(''.join(raw))
        if values:
            analysis.require(0 <= start <= len(binary) - len(values)
                             and record['output_offset_end'] == start + len(values) - 1
                             and address(record['cpu_address_end']) == ((cpu + len(values) - 1) & 0xffff)
                             and binary[start:start + len(values)] == values,
                             'listing bytes disagree with binary')
        definition = definitions.get(kind) if not values else None
        if definition is not None:
            if definition['output_offset'] is None:
                current = None
                continue
            if named_table(kind) or (current is not None and current.named and not current.values):
                analysis.require(kind not in seen
                                 and (definition['file'], definition['line'], definition['column'],
                                      definition['output_offset'], address(definition['cpu_address']))
                                 == (record['file'], record['line'], record['column'], start, cpu),
                                 f'listing definition is ambiguous or redefined: {kind}')
            seen.add(kind)
            if current is None or current.values or current.symbolic or (current.start, current.cpu) != (start, cpu):
                current = Body(start, cpu)
            current.labels.append((kind, definition))
            current.named = current.named or named_table(kind)
            tables[kind] = current
        elif kind in ('.DB', '.DW') and values and current is not None:
            analysis.require(start == current.start + len(current.values)
                             and cpu == ((current.cpu + len(current.values)) & 0xffff),
                             'noncontiguous pointer-table body')
            if kind == '.DW':
                current.symbolic = True
            for i, value in enumerate(values):
                ref = references.get(start + i)
                if ref and ref.get('target_projection') in ('low', 'high'):
                    analysis.require(isinstance(ref.get('target_symbol'), str), 'missing projected target')
                    current.symbolic = True
                # A constant-only expression is not raw numeric pointer evidence.
                current.values.append(None if ref else value)
        else:
            if not values and not kind.startswith('.'):
                # Local/anonymous labels are absent from the default xref.
                if current is not None:
                    current.opaque = True
                analysis.require(not named_table(kind) or '@' in kind or '#' in kind,
                                 f'named declaration has no visible definition: {kind}')
            current = None

    for name, definition in definitions.items():
        analysis.require(not named_table(name) or definition['output_offset'] is None or name in seen,
                         f'named declaration missing from listing: {name}')
    return tables


def classify(pairs):
    words, leading = [], 0
    prefix = True
    for lo, hi in pairs:
        if lo is None or hi is None:
            prefix = False
            continue
        word = lo | hi << 8
        words.append(word)
        if prefix and 0x8000 <= word <= 0xffff:
            leading += 1
        else:
            prefix = False
    prg = sum(0x8000 <= word <= 0xffff for word in words)
    ratio = len(words) >= MIN_WORDS and prg >= PRG_RATIO * len(words)
    return (len(words), prg, leading, ratio) if ratio or leading >= MIN_WORDS else None


def findings(bundle):
    tables = table_bodies(bundle.load('xref'), bundle.load('listing'),
                          analysis.read_bytes(bundle.data['outputs']['binary']['path']))
    result = []
    for name, body in tables.items():
        if not named_table(name) or body.symbolic:
            continue
        preceding = tables.get(name[:-3]) if name.endswith('End') else None
        if (preceding is not None and preceding.values
                and preceding.start + len(preceding.values) == body.start
                and ((preceding.cpu + len(preceding.values)) & 0xffff) == body.cpu):
            continue
        analysis.require(not body.opaque, f'{name}: body interrupted by a label with unavailable scope')
        if not body.values:
            continue
        high_name, low_name = split_counterpart(name, True), split_counterpart(name, False)
        if high_name or low_name:
            if low_name:
                analysis.require(low_name in tables, f'{name}: split pointer counterpart missing')
                continue
            high = tables.get(high_name)
            analysis.require(high is not None, f'{name}: split pointer counterpart missing')
            analysis.require(not high.opaque and len(body.values) == len(high.values)
                             and high is not body, f'{name}: split pointer bodies are incomplete or unequal')
            if high.symbolic:
                continue
            pairs = zip(body.values, high.values)
        else:
            pairs = zip(body.values[::2], body.values[1::2])
        proof = classify(pairs)
        if proof and not (high_name or low_name) and len(body.values) % 2 == 0:
            high_half = body.values[len(body.values) // 2:]
            analysis.require(not all(value is not None and value < 0x80 for value in high_half),
                             f'{name}: ambiguous interleaved ROM or single-label split RAM layout')
        if proof:
            definition = next(d for label, d in body.labels if label == name)
            result.append((name, definition, proof))
    bundle.validate()
    return result


def report(rows, mode):
    for name, definition, (count, prg, leading, ratio) in rows:
        proof = 'whole-body ratio' if ratio else 'leading prefix'
        print(f'advisory: {definition["file"]}:{definition["line"]}  {name} has a raw .DB body '
              f'({count} words, {prg} in $8000-$FFFF, {leading} in the leading prefix; proof: {proof}) '
              '-- relocate to .DW Target or .DB <Target,>Target', file=sys.stderr)
    print(f'[pointer-table] raw_pointer_table_bodies={len(rows)}')
    blocking = [row for row in rows if mode == '--strict' or row[2][3]]
    if mode and blocking:
        print(f'FAIL: {len(blocking)} pointer-table label(s) still hold raw .DB pointer bytes', file=sys.stderr)
        return 68
    return 0


def main(argv):
    paths, modes = [], []
    for arg in argv:
        if arg in ('--strict', '--strict-whole-body'):
            modes.append(arg)
        elif arg.startswith('-'):
            print(USAGE, file=sys.stderr)
            return 64
        else:
            paths.append(arg)
    if len(paths) != 1 or len(modes) > 1:
        print(USAGE, file=sys.stderr)
        return 64
    source = paths[0]
    mode = modes[0] if modes else None
    try:
        bundle = analysis.supplied(source)
        if bundle is not None:
            return report(findings(bundle), mode)
        with tempfile.TemporaryDirectory(prefix='nesrev-pointer-tables-') as directory:
            analysis.prepare_source(directory, source, [], profile='data-listing-v1')
            rc = analysis.produce(directory, source, str(Path(directory) / 'out.bin'))
            if rc:
                return rc if rc in (130, 143) else 65
            return report(findings(analysis.Bundle(Path(directory) / 'bundle.json', source)), mode)
    except (analysis.BundleError, OSError, ValueError, KeyError, TypeError) as exc:
        print(f'error: pointer-table evidence refused: {exc}', file=sys.stderr)
        return 65
    except KeyboardInterrupt:
        return 130


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
