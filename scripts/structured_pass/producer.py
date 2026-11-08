"""Pinned XORcyst source-model acquisition and structural integrity checks.

No assembly parser or expression evaluator lives here. Certification belongs to
the configured assembler; this reader checks the wire contract and its joins.
"""
import base64
import hashlib
import json
import os
from pathlib import Path
import subprocess

from .wire_schema import check as check_schema
import nes_graphics as rom

EXE = None  # Selected once by the operator's pinned project profile.
CONTEXTS = frozenset(('INSTRUCTION_NODE', 'DATA_NODE', 'EQU_NODE', 'ORG_NODE'))
DECLS = frozenset(('LABEL_NODE', 'LOCAL_LABEL_NODE', 'EQU_NODE', 'FORWARD_BRANCH_DECL_NODE', 'BACKWARD_BRANCH_DECL_NODE'))
ERRORS = frozenset('''SOURCE_MODEL_SCHEMA SOURCE_MODEL_NOT_CERTIFIED SOURCE_MODEL_JOIN
 SOURCE_MODEL_PARTITION SOURCE_MODEL_IDENTITY SOURCE_MODEL_BINARY SOURCE_MODEL_PARITY
 SOURCE_MODEL_PRODUCER SOURCE_MODEL_INPUT SOURCE_MODEL_INVOCATION
 PRODUCER_CERTIFICATION_FAILED PRODUCER_UNAVAILABLE REFERENCE_INVALID'''.split())


class ProducerRejected(ValueError):
    pass


def require(condition, code):
    if not condition:
        raise ValueError(code)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read_ines(path):
    try:
        prg, chr_bytes = rom.read_ines(path)
    except rom.GraphicsError:
        raise ValueError('REFERENCE_INVALID') from None
    require(bool(prg), 'REFERENCE_INVALID')
    return prg, chr_bytes


def identity(parts):
    return digest(b''.join(str(len(p.encode())).encode()+b':'+p.encode() for p in parts))


def indexed(rows):
    result = {r['id']: r for r in rows}
    require(len(result) == len(rows), 'SOURCE_MODEL_JOIN')
    return result


def reconstruct(document):
    """Reconstruct using embedded file bytes and units; never open source paths."""
    files = indexed(document['files'])
    require(bool(files), 'SOURCE_MODEL_PARTITION')
    raw = {}
    for fid, f in files.items():
        data = base64.b64decode(f['bytes_base64'], validate=True)
        require(len(data) == f['byte_length'] and digest(data) == f['sha256'], 'SOURCE_MODEL_PARTITION')
        raw[fid] = data
    offsets = dict.fromkeys(files, 0)
    pieces = {fid: [] for fid in files}
    indexed(document['units'])
    for unit in document['units']:
        fid = unit['file_id']; lo = unit['byte_start']; hi = unit['byte_end_exclusive']
        require(fid in files and lo == offsets[fid] and lo < hi <= len(raw[fid]), 'SOURCE_MODEL_PARTITION')
        pieces[fid].append(raw[fid][lo:hi]); offsets[fid] = hi
    require(all(offsets[fid] == len(data) for fid, data in raw.items()), 'SOURCE_MODEL_PARTITION')
    return {fid: b''.join(parts) for fid, parts in pieces.items()}


def load(path, *, certified=True):
    return loads(Path(path).read_bytes(),certified=certified)


def loads(data, *, certified=True):
    doc = json.loads(data)
    try:
        check_schema(doc, json.loads(Path(__file__).with_name('source-model.schema.json').read_bytes()))
    except (ValueError, KeyError, TypeError, RecursionError):
        raise ValueError('SOURCE_MODEL_SCHEMA') from None
    raw = reconstruct(doc)
    options = doc['semantic_options']
    input_id = identity(['xasm-source-model-input-v1',
        'case-insensitive' if options['case_insensitive'] else 'case-sensitive',
        'swapped-parens' if options['swap_parens'] else 'native-parens',
        *[v for f in doc['files'] for v in (f['path'], f['sha256'])]])
    require(input_id == doc['identity']['input_id'] and
            identity(['xasm-source-model:1:asm-edit-v1', input_id, doc['identity']['producer_sha256']]) ==
            doc['identity']['model_id'], 'SOURCE_MODEL_IDENTITY')
    if not certified:
        return doc, raw
    require(doc['status'] == 'certified' and not doc['diagnostics'] and doc['exit_status'] == 0,
            'SOURCE_MODEL_NOT_CERTIFIED')
    require(doc['analysis_outcomes']['comparison'] == 'equal', 'SOURCE_MODEL_PARITY')
    require(len(raw) == 1 and not any(u['kind'] == 'unclassified' for u in doc['units']), 'SOURCE_MODEL_PARTITION')
    syntax = indexed(doc['syntax']); decls = indexed(doc['declarations'])
    exprs = indexed(doc['expressions']); refs = indexed(doc['references'])
    scopes = indexed(doc['scopes']); locations = indexed(doc['locations'])
    segments = indexed(doc['segments']); evaluations = indexed(doc['evaluations'])
    for s in syntax.values():
        span = s['span']
        require(span['file_id'] in raw and 0 <= span['byte_start'] <= span['byte_end_exclusive'] <= len(raw[span['file_id']]), 'SOURCE_MODEL_JOIN')
        require(s['scope_id'] in scopes and (s['parent_id'] is None or s['parent_id'] in syntax), 'SOURCE_MODEL_JOIN')
        require(all(c in syntax and syntax[c]['parent_id'] == s['id'] for c in s['children']), 'SOURCE_MODEL_JOIN')
    for d in decls.values():
        require(d['syntax_id'] in syntax and d['scope_id'] in scopes and
                (d['expression_id'] is None or d['expression_id'] in exprs), 'SOURCE_MODEL_JOIN')
    expected = {e['reference_id'] for e in exprs.values() if 'reference_id' in e}
    require(expected == set(refs) and doc['coverage']['bound_references'] == len(refs) == doc['coverage']['expected_references'], 'SOURCE_MODEL_JOIN')
    for e in exprs.values():
        require(e['syntax_id'] in syntax and e['context_syntax_id'] in syntax and
                e['span'] == syntax[e['syntax_id']]['span'] and all(c in exprs for c in e['children']), 'SOURCE_MODEL_JOIN')
    for r in refs.values():
        require(r['declaration_id'] in decls and r['expression_id'] in exprs and r['diagnostic_id'] is None, 'SOURCE_MODEL_JOIN')
        e = exprs[r['expression_id']]; d = decls[r['declaration_id']]
        require(e.get('reference_id') == r['id'] and r['context_syntax_id'] == e['context_syntax_id'] and r['span'] == e['span'], 'SOURCE_MODEL_JOIN')
        require(r['name'] == d['name'] and r['scope_id'] == syntax[e['syntax_id']]['scope_id'], 'SOURCE_MODEL_JOIN')
        if d['kind'] == 'local':
            require(r['scope_id'] == d['scope_id'], 'SOURCE_MODEL_JOIN')
    require({v['expression_id'] for v in evaluations.values()} == set(exprs) and len(evaluations) == len(exprs), 'SOURCE_MODEL_JOIN')
    for v in evaluations.values():
        require(v['context_syntax_id'] == exprs[v['expression_id']]['context_syntax_id'] and v['pc_context']['segment_id'] in segments, 'SOURCE_MODEL_JOIN')
    for row in locations.values():
        require(row['syntax_id'] in syntax and row['segment_id'] in segments, 'SOURCE_MODEL_JOIN')
    for collection in ('instructions', 'data'):
        records = indexed(doc[collection])
        kind = 'INSTRUCTION_NODE' if collection == 'instructions' else 'DATA_NODE'
        require({r['syntax_id'] for r in records.values()} == {n for n,s in syntax.items() if s['kind'] == kind}, 'SOURCE_MODEL_JOIN')
        for r in records.values():
            require(r['location_id'] in locations and locations[r['location_id']]['syntax_id'] == r['syntax_id'], 'SOURCE_MODEL_JOIN')
            for operand in r['operands']:
                require(operand['expression_id'] in exprs and operand['evaluation_id'] in evaluations and
                        evaluations[operand['evaluation_id']]['expression_id'] == operand['expression_id'], 'SOURCE_MODEL_JOIN')
    binary = base64.b64decode(doc['binary']['bytes_base64'], validate=True)
    require(len(binary) == doc['binary']['byte_length'] and digest(binary) == doc['binary']['sha256'], 'SOURCE_MODEL_BINARY')
    end = 0
    for emission in doc['emissions']:
        require(emission['output_start'] == end and end < emission['output_end_exclusive'] <= len(binary)
                and emission['segment_id'] in segments and emission['syntax_id'] in syntax, 'SOURCE_MODEL_JOIN')
        end = emission['output_end_exclusive']
    require(end == len(binary), 'SOURCE_MODEL_BINARY')
    return doc, raw


def produce(source, capture, reference):
    require(EXE is not None and Path(EXE).is_file(), 'PRODUCER_UNAVAILABLE')
    source = Path(source).resolve(); capture = Path(capture).resolve()
    capture.mkdir(parents=True, exist_ok=False)
    prg, _ = read_ines(reference)
    comparison = capture/'reference.prg'; comparison.write_bytes(prg)
    before = sha(source); executable = Path(EXE).resolve(); producer_sha = sha(executable)
    command = [str(executable), '--pure-binary', str(source), '-o', str(capture/'out.bin'),
        '--source-model='+str(capture/'model.json'), '--source-model-diagnostics='+str(capture/'diagnostic.json'),
        '--compare='+str(comparison)]
    env = {'PATH':'/usr/bin:/bin', 'HOME':str(capture), 'TMPDIR':str(capture), 'LC_ALL':'C', 'LANG':'C'}
    result = subprocess.run(command, cwd=source.parent, env=env, capture_output=True, timeout=120)
    (capture/'producer.log').write_bytes(result.stdout+result.stderr)
    (capture/'invocation.json').write_text(json.dumps({'command':command,'exit_code':result.returncode,'environment':env})+'\n')
    if result.returncode:
        raise ProducerRejected('PRODUCER_CERTIFICATION_FAILED')
    doc, raw = load(capture/'model.json')
    require(sha(source) == before and next(iter(raw.values())) == source.read_bytes(), 'SOURCE_MODEL_INPUT')
    require(doc['identity']['producer_sha256'] == producer_sha == sha(executable), 'SOURCE_MODEL_PRODUCER')
    require(doc['invocation']['argv'] == command and doc['invocation']['cwd'] == str(source.parent), 'SOURCE_MODEL_INVOCATION')
    require((capture/'out.bin').read_bytes() == prg == base64.b64decode(doc['binary']['bytes_base64']), 'SOURCE_MODEL_PARITY')
    inputs = {str(source):('source', before), str(comparison):('compare', digest(prg)), str(executable):('producer', producer_sha)}
    require(all(not row['missing'] and row['path'] in inputs and row['sha256'] == inputs[row['path']][1] for row in doc['dependencies']), 'SOURCE_MODEL_INPUT')
    require(set(inputs) == {row['path'] for row in doc['dependencies']}, 'SOURCE_MODEL_INPUT')
    return doc, raw
