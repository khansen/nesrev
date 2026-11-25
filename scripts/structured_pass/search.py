"""Bounded read queries over certified instruction facts and admitted text.

No source parser or caller-supplied path is used here. Continuations bind the
complete selection and input identities; rows are never silently truncated.
"""
import base64
from bisect import bisect_left
from itertools import islice
from heapq import merge
import hashlib
import json
from pathlib import Path

from . import paging
from . import authored_documents as authored, guidance, ownership, review_pages
from .evidence_views import identity
from . import operation_contract as contract

ERRORS = frozenset(('SEARCH_SCHEMA', 'SEARCH_INPUT_UNKNOWN', 'SEARCH_INPUT_UNAVAILABLE',
    'SEARCH_CONTINUATION_INVALID', 'SEARCH_ITEM_TOO_LARGE'))
MNEMONICS = frozenset('ADC AND ASL BCC BCS BEQ BIT BMI BNE BPL BRK BVC BVS CLC CLD CLI CLV '
    'CMP CPX CPY DEC DEX DEY EOR INC INX INY JMP JSR LDA LDX LDY LSR NOP ORA PHA PHP PLA '
    'PLP ROL ROR RTI RTS SBC SEC SED SEI STA STX STY TAX TAY TSX TXA TXS TYA'.split())
MODES = frozenset(name + '_MODE' for name in ('IMPLIED', 'ACCUMULATOR', 'IMMEDIATE',
    'ZEROPAGE', 'ZEROPAGE_X', 'ZEROPAGE_Y', 'ABSOLUTE', 'ABSOLUTE_X', 'ABSOLUTE_Y',
    'RELATIVE', 'INDIRECT', 'PREINDEXED_INDIRECT', 'POSTINDEXED_INDIRECT'))
SHAPES = frozenset(('none', 'literal', 'bound', 'compound'))
QUERY_SCHEMAS={
    'catalogue':(('kind',),('kinds',)),
    'instructions':(('kind','alternatives'),('context','owner_id','detail')),
    'text':(('kind','inputs'),('terms','prefixes','ignore_case','whole_token','context'))}
CONTEXT_SCHEMA=((),('before','after'))
PREDICATE_SCHEMA=((),('mnemonics','modes','operand','shapes','values','ranges'))
OPERANDS=('immediate','non_immediate','none')
INPUT_KINDS=('document','guidance')
DETAILS=('full','matches')
MATCH_FIELDS=('record_id','owner_id','segment_id','mnemonic','final_mode',
              'operand_value','evaluation','operand_meaning')
MATCH_COLUMNS=('witness_id','alternative','certainty','relative_instruction',
               *('instruction.'+key for key in MATCH_FIELDS))
MATCH_CONSTANTS={'part':'match','context_before':0,'context_after':0}
WORD = frozenset('ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_@')
SLICE = 512
TOOL_HELP = (' Search is read-only for either role. arguments: {generation, query, '
    'continuation?: opaque token, limit?: 1..40}. query.kind is catalogue, instructions or text. '
    'catalogue: optional kinds [document,guidance]; use returned input_id values, never host paths. '
    'instructions: alternatives is 1..8 sequences of 1..2 predicate objects; predicates support '
    'mnemonics and modes (native final-mode names, max16 each), operand (immediate/non_immediate/none), '
    'shapes (literal/bound/compound/none), values (max32 integers), ranges (max4 inclusive [lo,hi]). '
    'Fields are ANDed; values/ranges and alternatives are ORed. Optional owner_id and context '
    '{before,after}, 0..10 each. Indexed values are bases, indirect values are pointers. '
    'text: inputs (1..32 catalogue IDs), terms and/or prefixes (max32 total, max256 characters each), '
    'optional ignore_case and whole_token booleans, context {before,after} 0..10. '
    'No regex. Text predicates are ORed; whole_token uses ASCII letters/digits/underscore/@ boundaries. '
    'Follow continuation with the same generation and query until complete; all rows, including '
    'context and long-line slices, count toward limit. Unknown values remain explicit. '
    'An unavailable input or unsupported predicate is not a zero-match result.')



class Rows:
    """Reiterable evidence; pagination never materializes the complete result."""
    def __init__(self, factory, length=None):
        self.factory, self.length = factory, length

    def __iter__(self):
        return self.factory()

    def __len__(self):
        if self.length is None:
            self.length = sum(1 for _ in self.factory())
        return self.length

    def __getitem__(self, selection):
        if isinstance(selection, slice):
            return list(islice(self.factory(), selection.start or 0, selection.stop, selection.step or 1))
        return next(islice(self.factory(), selection, selection+1))

def require(ok, code='SEARCH_SCHEMA'):
    if not ok:
        raise ValueError(code)


def keys(value, required=(), optional=()):
    contract.check(value,(required,optional),code='SEARCH_SCHEMA',path='query')


def packed(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode()


def digest(value):
    return hashlib.sha256(packed(value)).hexdigest()


def choices(values, allowed, maximum):
    require(isinstance(values, list) and 1 <= len(values) <= maximum
            and all(isinstance(v, str) and v in allowed for v in values)
            and len(set(values)) == len(values))


def integer(value):
    return type(value) is int and -(2**63) <= value < 2**63


def context(value):
    keys(value, *CONTEXT_SCHEMA)
    require(all(type(n) is int and 0 <= n <= 10 for n in value.values()))
    return value.get('before', 0), value.get('after', 0)


def predicate(value):
    keys(value, *PREDICATE_SCHEMA)
    require(bool(value))
    for key, allowed in (('mnemonics', MNEMONICS), ('modes', MODES), ('shapes', SHAPES)):
        if key in value:
            choices(value[key], allowed, 16)
    if 'operand' in value:
        if value['operand'] not in OPERANDS:
            raise contract.RequestError('SEARCH_SCHEMA',field='query.alternatives[][].operand',accepted_values=list(OPERANDS))
    if 'values' in value:
        rows = value['values']
        require(isinstance(rows, list) and 1 <= len(rows) <= 32 and all(map(integer, rows))
                and len(set(rows)) == len(rows))
    if 'ranges' in value:
        rows = value['ranges']
        require(isinstance(rows, list) and 1 <= len(rows) <= 4)
        require(all(isinstance(r, list) and len(r) == 2 and all(map(integer, r))
                    and r[0] <= r[1] for r in rows))


def expression_shape(instruction, expressions):
    if not instruction['operands']:
        return 'none'
    kind = expressions[instruction['operands'][0]['expression_id']]['kind']
    return 'literal' if kind == 'integer' else 'bound' if kind in ('symbol', 'local') else 'compound'


def matches(instruction, shape, pred):
    """Three-valued match; numeric uncertainty must survive filtering."""
    mode = instruction['addressing_mode']
    if 'mnemonics' in pred and instruction['mnemonic'] not in pred['mnemonics']:
        return False
    if 'modes' in pred and mode not in pred['modes']:
        return False
    if 'shapes' in pred and shape not in pred['shapes']:
        return False
    operand = 'none' if not instruction['operands'] else 'immediate' if mode == 'IMMEDIATE_MODE' else 'non_immediate'
    if 'operand' in pred and pred['operand'] != operand:
        return False
    if 'values' not in pred and 'ranges' not in pred:
        return True
    if not instruction['operands']:
        return False
    value = instruction['operand_value']
    if value is None:
        return None
    return value in pred.get('values', []) or any(lo <= value <= hi for lo, hi in pred.get('ranges', []))


def contiguous(model, left, right):
    a, b = model.instructions[left], model.instructions[right]
    if not hasattr(model, '_search_data_starts'):
        model._search_data_starts = sorted(model.ranges[d['syntax_id']][0] for d in model.document['data'])
    data = model._search_data_starts
    index = bisect_left(data, model.ranges[left][1])
    if index < len(data) and data[index] < model.ranges[right][0]:
        return False
    return (a['segment_id'] == b['segment_id']
            and a['output_offset'] + a['length'] == b['output_offset']
            and a['cpu_address'] + a['length'] == b['cpu_address'])


def instruction_rows(model, query):
    keys(query, *QUERY_SCHEMAS['instructions'])
    alternatives = query['alternatives']
    require(isinstance(alternatives, list) and 1 <= len(alternatives) <= 8)
    for sequence in alternatives:
        require(isinstance(sequence, list) and 1 <= len(sequence) <= 2)
        for pred in sequence:
            predicate(pred)
    before, after = context(query.get('context', {}))
    detail=query.get('detail','full')
    if detail not in DETAILS:
        raise contract.RequestError('SEARCH_SCHEMA',field='query.detail',accepted_values=list(DETAILS))
    if detail=='matches' and (before or after):
        raise contract.RequestError('SEARCH_SCHEMA',field='query.context',accepted_values=[{'before':0,'after':0}])
    owner = None
    if 'owner_id' in query:
        owner = model.node(query['owner_id'])
        require(owner in model.declaration_records)
    expressions = {e['id']: e for e in model.document['expressions']}
    nodes = sorted(model.instructions, key=lambda n: (model.ranges[n][0], n))
    shapes = {n: expression_shape(model.instructions[n], expressions) for n in nodes}
    total, unresolved, row_count = 0, 0, 0

    def record(n):
        ins = model.instructions[n]
        mode = ins['addressing_mode']
        meaning = ('no_operand' if not ins['operands'] else
            'immediate_value' if mode == 'IMMEDIATE_MODE' else
            'pointer_expression' if 'INDIRECT' in mode else
            'indexed_base' if mode.endswith(('_X_MODE', '_Y_MODE')) else
            'branch_target' if mode == 'RELATIVE_MODE' else 'direct_operand')
        result = {**identity(model, n), 'mnemonic': ins['mnemonic'], 'final_mode': mode,
            'parsed_mode': ins['parsed_mode'], 'operand_value': ins['operand_value'],
            'evaluation': 'not_applicable' if not ins['operands'] else
                'unresolved' if ins['operand_value'] is None else 'integer',
            'expression_shape': shapes[n], 'operand_meaning': meaning,
            'memory_access': ins['memory_access'], 'control_flow': ins['control_flow']}
        return {key:result[key] for key in MATCH_FIELDS} if detail=='matches' else result

    def witnesses():
        for index, n in enumerate(nodes):
            if owner is not None and model.owners[n] != owner:
                continue
            for alt, sequence in enumerate(alternatives):
                selected = nodes[index:index + len(sequence)]
                if len(selected) != len(sequence) or any(not contiguous(model, a, b) for a, b in zip(selected, selected[1:])):
                    continue
                results = [matches(model.instructions[s], shapes[s], p) for s, p in zip(selected, sequence)]
                if False in results:
                    continue
                lo, hi = index, index + len(sequence)
                for _ in range(before):
                    if lo == 0 or not contiguous(model, nodes[lo-1], nodes[lo]):
                        break
                    lo -= 1
                for _ in range(after):
                    if hi == len(nodes) or not contiguous(model, nodes[hi-1], nodes[hi]):
                        break
                    hi += 1
                yield index, alt, len(sequence), None in results, lo, hi

    for index, alt, size, uncertain, lo, hi in witnesses():
        total += int(not uncertain)
        unresolved += int(uncertain)
        row_count += hi-lo

    def rows():
        for index, alt, size, uncertain, lo, hi in witnesses():
            witness = {'witness_id': f'{alt}:{model.ids[nodes[index]]}', 'alternative': alt,
                       'certainty': 'unresolved' if uncertain else 'match',
                       'context_before': index-lo, 'context_after': hi-index-size}
            for position in range(lo, hi):
                yield {**witness, 'part': 'match' if index <= position < index+size else 'context',
                       'relative_instruction': position-index, 'instruction': record(nodes[position])}
    metadata={'total_matches': total, 'unresolved_candidates': unresolved,
                  'complete_numeric_answer': unresolved == 0,
                  'adjacency': 'Native order and contiguous segment/output/CPU locations; not control-flow proof.'}
    if detail=='matches':
        metadata['detail']='matches'
        metadata['instruction_fields']=list(MATCH_FIELDS)
        metadata['context_route']='Use navigate records with record_id or owner_id for source context and preimages; matches alone do not prove ownership or control flow.'
    return Rows(rows, row_count), metadata


def input_catalogue(editor, generation):
    from .service import file_ownership
    record = editor.state['generations'][generation]
    registered = ownership.read(json.loads((Path(record['capture'])/'ownership.json').read_text()))
    classifier = lambda p, project, source: file_ownership(p, project, source, registered)
    items = []

    def add(kind, path, data):
        sha = authored.sha(data)
        row = {'kind': kind, 'path': path, 'sha256': sha, 'available': data is not None}
        row['input_id'] = 'T-' + digest(row)
        items.append((row, data))

    for path in sorted(record['manifest']):
        try:
            authored.path_allowed(path, editor.project, editor.source, classifier)
        except ValueError:
            continue
        add('document', path, authored.read(record['checkout'], record['manifest'], path))
    for name in guidance.NAMES:
        add('guidance', name, guidance.read(editor, name))
    return items


def terms(value):
    require(isinstance(value, list) and 1 <= len(value) <= 32
            and all(isinstance(t, str) and 1 <= len(t) <= 256 and '\n' not in t and '\r' not in t
                    and '\x00' not in t for t in value) and len(set(value)) == len(value))


def folded_view(line):
    chunks = [c.casefold() for c in line]
    starts = {}; ends = {}; offset = 0
    for index, chunk in enumerate(chunks):
        starts[offset] = index
        offset += len(chunk)
        ends[offset] = index + 1
    return ''.join(chunks), starts, ends


def occurrences(line, term, insensitive, whole, prefix, folded=None):
    """Original Unicode-codepoint positions, including expanding case folds."""
    if insensitive:
        haystack, starts, ends = folded if folded is not None else folded_view(line)
        needle = term.casefold()
    else:
        haystack, needle = line, term
    offset = 0
    while True:
        found = haystack.find(needle, offset)
        if found < 0 or prefix and found != 0:
            return
        finish = found + len(needle)
        if not insensitive or found in starts and finish in ends:
            lo, hi = (starts[found], ends[finish]) if insensitive else (found, finish)
            if not whole or ((lo == 0 or line[lo-1] not in WORD) and (hi == len(line) or line[hi] not in WORD)):
                yield lo, hi
        if prefix:
            return
        offset = found + 1


def text_rows(items, query):
    keys(query, *QUERY_SCHEMAS['text'])
    requested = query['inputs']
    require(isinstance(requested, list) and 1 <= len(requested) <= 32
            and all(isinstance(i, str) for i in requested) and len(set(requested)) == len(requested))
    require('terms' in query or 'prefixes' in query)
    for key in ('terms', 'prefixes'):
        if key in query:
            terms(query[key])
    require(len(query.get('terms', [])) + len(query.get('prefixes', [])) <= 32)
    for key in ('ignore_case', 'whole_token'):
        require(key not in query or type(query[key]) is bool)
    before, after = context(query.get('context', {}))
    by_id = {row['input_id']: (row, data) for row, data in items}
    require(all(i in by_id for i in requested), 'SEARCH_INPUT_UNKNOWN')
    selected = [by_id[i] for i in sorted(requested)]
    require(all(data is not None for _, data in selected), 'SEARCH_INPUT_UNAVAILABLE')
    documents = [(item, data.decode('utf-8').splitlines()) for item, data in selected]

    def positions(line):
        folded = folded_view(line) if query.get('ignore_case', False) else None
        def for_term(kind, index, term):
            for lo, hi in occurrences(line, term, query.get('ignore_case', False),
                    query.get('whole_token', False), kind == 'prefixes', folded):
                yield {'term_index': index, 'predicate': kind, 'start': lo, 'end': hi}
        return merge(*(for_term(kind, index, term) for kind in ('terms', 'prefixes')
            for index, term in enumerate(query.get(kind, []))),
            key=lambda r: (r['start'], r['end'], r['predicate'], r['term_index']))

    def matching_lines():
        for item, lines in documents:
            for index, line in enumerate(lines):
                if next(positions(line), None) is not None:
                    yield item, lines, index

    count = sum(1 for _ in matching_lines())

    def rows():
        for item, lines, index in matching_lines():
            witness = {'witness_id': item['input_id'] + ':' + str(index+1), 'input_id': item['input_id'],
                       'match_line': index+1}
            for number in range(max(0, index-before), min(len(lines), index+after+1)):
                text = lines[number]
                matches_found = positions(text) if number == index else iter(())
                pending = next(matches_found, None)
                for start in range(0, max(1, len(text)), SLICE):
                    end = min(start+SLICE, len(text))
                    row = {**witness, 'part': 'line', 'line': number+1, 'start': start,
                        'end': end, 'line_length': len(text), 'text': text[start:end],
                        'line_complete': end == len(text), 'matches': []}
                    while pending is not None and pending['start'] < end:
                        row['matches'].append(pending)
                        pending = next(matches_found, None)
                        if len(row['matches']) == 8:
                            yield row
                            row = {**witness, 'part': 'positions', 'matches': []}
                    if row['part'] == 'line' or row['matches']:
                        yield row
    return Rows(rows), {'selected_inputs': [r for r, _ in selected], 'total_matches': count,
                  'match_unit': 'line', 'positions': 'One-based lines; zero-based Unicode-codepoint half-open columns.'}


def token(binding, offset):
    value = {'binding': binding, 'offset': offset}
    value['checksum'] = digest(value)
    return base64.urlsafe_b64encode(packed(value)).decode()


def page(rows, metadata, binding, continuation, limit):
    paging.integer(limit, 'limit', 1, 40)
    if metadata.get('detail')=='matches':
        original=rows
        def values():
            for row in original:
                yield [row[key] if '.' not in key else row['instruction'][key.split('.')[1]]
                       for key in MATCH_COLUMNS]
        rows=Rows(values,len(original))
        metadata={**metadata,'encoding':'instruction-matches-columnar-v1',
                  'columns':list(MATCH_COLUMNS),'constants':dict(MATCH_CONSTANTS)}
    offset = 0
    if continuation is not None:
        require(isinstance(continuation, str) and len(continuation) <= 512, 'SEARCH_CONTINUATION_INVALID')
        try:
            value = json.loads(base64.b64decode(continuation, altchars=b'-_', validate=True))
            offset = value['offset']
            valid = type(offset) is int and 0 < offset < len(rows) and continuation == token(binding, offset)
        except (ValueError, KeyError, TypeError):
            valid = False
        require(valid, 'SEARCH_CONTINUATION_INVALID')
    # Every row must occur once on the wire. Exclude envelopes and delimiters,
    # making this a lower bound even when size-limited pages add more overhead.
    minimum_bytes = sum(len(json.dumps(json.dumps(row)).encode())-2 for row in rows)
    result = {**metadata, 'selection_sha256': binding, 'offset': offset, 'total_rows': len(rows),
              'minimum_response_bytes': minimum_bytes,
              'rows': [], 'continuation': None, 'complete': True}
    for row in rows[offset:offset+limit]:
        end = offset + len(result['rows']) + 1
        trial = {**result, 'rows': [*result['rows'], row], 'complete': end == len(rows),
                 'continuation': token(binding, end) if end < len(rows) else None}
        if review_pages.wire_size(trial) > review_pages.BUDGET:
            require(bool(result['rows']), 'SEARCH_ITEM_TOO_LARGE')
            break
        result = trial
    require(review_pages.wire_size(result) <= review_pages.BUDGET, 'SEARCH_ITEM_TOO_LARGE')
    return result


def execute(editor, generation, query, continuation=None, limit=40, *, public_generation=None):
    model = editor.model(generation)
    require(isinstance(query, dict) and isinstance(query.get('kind'), str))
    kind = query['kind']
    generation_name = public_generation or generation
    if kind == 'instructions':
        rows, metadata = instruction_rows(model, query)
        inputs = {'source_sha256': hashlib.sha256(model.source).hexdigest(),
                  'model_id': model.document['identity']['model_id']}
    elif kind in ('catalogue', 'text'):
        items = input_catalogue(editor, generation)
        if kind == 'catalogue':
            keys(query, *QUERY_SCHEMAS['catalogue'])
            kinds = query.get('kinds', ['document', 'guidance'])
            choices(kinds, INPUT_KINDS, 2)
            rows = [r for r, _ in items if r['kind'] in kinds]
            metadata = {'total_inputs': len(rows)}
            inputs = rows
        else:
            rows, metadata = text_rows(items, query)
            inputs = metadata['selected_inputs']
    else:
        raise contract.RequestError('SEARCH_SCHEMA',field='query.kind',accepted_values=list(QUERY_SCHEMAS))
    binding = digest({'generation': generation_name, 'query': query, 'inputs': inputs})
    return page(rows, {'generation': generation_name, 'kind': kind, **metadata}, binding, continuation, limit)
