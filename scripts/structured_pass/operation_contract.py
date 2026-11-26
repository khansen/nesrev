"""Argument-key tables shared by dispatch and the client-visible declaration.

These describe outer argument keys only. Value checks, role authorization,
generation integrity and nested edit/query schemas remain with their owners.
"""
import json

QUESTION_BYTES = 400 * 1024
REQUEST_COUNTING = (
    'Each independent evidence question has ceilings of eight logical requests and '
    f'{QUESTION_BYTES} bytes (400 KiB) of text responses. Add volume.response_bytes from every '
    'response, including refusals and abandoned queries; pagination does not reset the byte total. '
    'Before another call, leave room for its 24576-byte maximum. Inspect first-page totals '
    '(total_rows, total_records or total) before paging; search minimum_response_bytes is a '
    'lower bound for the complete query, not a promise that it fits. Start instruction searches '
    'with detail=matches and context before=0, after=0: matches include their owners. Read needed source context '
    'through bounded navigation, stopping when the required path is covered rather than '
    'automatically reading the rest of a segment. Narrow an oversized query before continuing, '
    'or stop for a decision if the complete evidence needed cannot fit. An incomplete query '
    'is not absence evidence. These ceilings take precedence over generic follow-until-complete '
    'paging help. Images need a separately measured context allowance. '
    'Continuation pages of an unchanged operation and query count as one request: only offset '
    'or the returned continuation token may differ. Keep generation, selector, filters, span '
    'and limit unchanged. A changed selector, including record_id, is a new request; use '
    'next_offset with the original selector to page a segment span. Report logical requests '
    'and transport calls separately. Do not relabel an unchanged question to evade either ceiling. '
    'The preparation must budget delivered inputs, question evidence and room for edits, validation '
    'and closeout against the pinned context window. The question ceiling is not a fresh allowance '
    'when earlier questions already occupy that window. Preparation must deliver a numeric '
    'conversation allowance with its measured startup cost, lifecycle reserve and at least '
    '10 percent estimation margin. Use the smaller of 400 KiB and that remaining allowance; '
    'include analogue reads and additional guidance. If the prepared allowance is missing, '
    'stop for a decision rather than guessing it. A resumed turn does not reset the allowance. '
    'Preparation must price every explicit RAM operand in the declared corridor, all access-owner '
    'contexts, called helper interfaces and both analogues, not a selected successful script. '
    'Read source with navigate source and the complete byte set with evidence ram_set; fetch '
    'editing records separately. The prepared task binds the inventory and complete bridge measurement.'
)

class RequestError(ValueError):
    """Public request diagnostics contain expected fields, never submitted values."""
    def __init__(self, code='REQUEST_SCHEMA', **details):
        super().__init__(code)
        self.details = details


def value(condition, field, expected, code='REQUEST_SCHEMA'):
    if not condition:
        raise RequestError(code, field=field, expected=expected)

INPUTS = (('generation',), ('offset', 'limit'))
INPUT = (('generation', 'input_id'), ('offset', 'limit'))
IMAGE_INPUT = (('generation', 'input_id'), ())

BASE = {
    'status': ((), ()),
    'validation_evidence': (('cid', 'revision', 'attempt'), ('offset', 'limit')),
    'candidate_status': (('cid',), ()),
    'query': (('generation', 'symbol'), ('offset', 'limit')),
    'propose': (('generation', 'operations'), ()),
    'amend': (('cid', 'replacements'), ()),
    'validate': (('cid',), ()),
    'publish': (('cid',), ()),
    'start_chain': (('generation',), ()),
    'review': (('generation', 'base_generation'), ()),
}
RENAME = {
    'evidence': (('generation', 'view'), ('offset', 'limit', 'record_id', 'address', 'decoder',
                                        'byte_offset', 'byte_count', 'artifact', 'analogue_index', 'key', 'set_id')),
    'preview_page': (('generation', 'preview_digest'), ('offset', 'limit')),
    'navigate': (('generation', 'view'), ('symbol', 'record_id', 'contains', 'offset', 'limit', 'analogue_index', 'span')),
    'inputs': INPUTS,
    'input': INPUT,
    'guidance': (('generation', 'name'), ('offset', 'limit')),
    'inspect': (('generation', 'symbol'), ()),
    'q09': (('generation', 'names'), ('offset', 'limit')),
    'search': (('generation', 'query'), ('continuation', 'limit')),
    'documents': (('generation',), ()),
    'document': (('generation', 'path'), ('offset', 'limit')),
    'review': (('generation', 'base_generation'), ('offset', 'limit')),
    'preview': (('generation', 'operations'), ('cid',)),
    'confirm': (('generation', 'preview_digest'), ()),
}
VERDICT = {
    'status': ((), ()),
    'review_report': (('sequence',), ('offset', 'limit')),
    'approve': (('ticket', 'report'), ()),
    'request-changes': (('ticket', 'report'), ()),
}
CORRIDOR = {
    'guidance': (('name',), ('generation', 'offset', 'limit')),
    'review': (('ticket', 'generation', 'base_generation'), ('offset', 'limit')),
    'closeout': ((), ()),
    'reready': (('response',), ()),
}
RETAINED = {
    'status': ((), ()),
    'review': (('generation', 'base_generation'), ('offset', 'limit')),
    'reassemble': (('generation',), ()),
}
INVESTIGATION = {
    'citation': (('generation','kind','record_id'), ('analogue_index','offset','limit')),
    'checkpoint': (('generation','claims','decisions'), ()),
}


def investigating():
    reads=('status','evidence','query','navigate','inspect','q09','documents','document','search','inputs','input')
    return {**{k:corridor()[k] for k in reads}, **INVESTIGATION}


def corridor():
    return {k:v for k,v in {**BASE, **RENAME, **VERDICT, **CORRIDOR}.items() if k!='guidance'}


def offered(role, profile='corridor'):
    if profile=='investigation':return list(investigating())
    if profile=='retained':
        return ['status','evidence','query','review','reassemble','inspect','navigate','q09','document','guidance','inputs','input']
    names=['status','evidence','query','navigate','inspect','q09','documents','document','review',
           'review_report','candidate_status','validation_evidence','search','inputs','input']
    return names+(['preview','preview_page','confirm','validate','publish','start_chain','reready','closeout']
                  if role=='implementer' else ['approve','request-changes'])


def retained(profile='source-v2'):
    names = ['evidence']
    if profile in ('rename', 'source-v2'):
        names += ['navigate', 'inspect', 'q09', 'document', 'inputs', 'input', 'guidance']
    return {'query': BASE['query'], **{name: RENAME[name] for name in names}, **RETAINED}


def keys(spec):
    required, optional = spec
    return {'required': list(required), 'optional': list(optional)}


def check(value, spec, *, code='REQUEST_SCHEMA', path='arguments'):
    required, optional = spec
    expected = keys(spec)
    if not isinstance(value, dict):
        raise RequestError(code, field=path, expected_type='object', **expected)
    missing = sorted(set(required) - set(value))
    if missing or not set(value) <= set(required) | set(optional):
        unexpected = set(value) - set(required) - set(optional)
        known = {key for table in (BASE, RENAME, VERDICT, CORRIDOR, RETAINED, INVESTIGATION)
                 for required_keys, optional_keys in table.values() for key in required_keys + optional_keys}
        named = missing[:1] or sorted(unexpected & known)[:1]
        field = ((path + '.') if path != 'arguments' else '') + named[0] if named else path
        raise RequestError(code, field=field, missing=missing,
                           unexpected_keys=bool(unexpected), **expected)



def request_arguments(operation, arguments, role, profile):
    """Validate JSON types at the public boundary, before owner lookups.

    Keys come from dispatch's tables. Value selection and integrity remain with
    the owners; this does not translate arbitrary exceptions into caller errors.
    """
    if operation not in offered(role, profile):return
    spec = entry(operation, role, profile)
    check(arguments, (spec['required'], spec['optional']))
    strings = {'generation','base_generation','cid','preview_digest','input_id','symbol',
               'path','name','view','kind','decoder','artifact','key','set_id','span',
               'contains','continuation','report','response','ticket'}
    integers = {'revision':(0,None),'attempt':(1,None),'sequence':(1,None),
                'analogue_index':(0,1),'byte_offset':(0,None),'byte_count':(1,4096)}
    for field, argument in arguments.items():
        if argument is None and field in ('cid','record_id','symbol','contains','continuation','analogue_index') and field in spec['optional']:
            continue
        if field in strings:
            value(isinstance(argument,str),field,{'type':'string'})
            if field=='view' and operation in ('evidence','navigate'):
                from . import navigation, rename_service
                allowed=navigation.VIEWS if operation=='navigate' else rename_service.EVIDENCE_ARGUMENTS
                value(argument in allowed,field,{'enum':list(allowed)})
            if field=='span':
                from .navigation import SPANS
                value(argument in SPANS,field,{'enum':list(SPANS)})
        elif field in integers:
            lo,hi=integers[field]
            value(type(argument) is int and argument>=lo and (hi is None or argument<=hi),
                  field,{'type':'integer','minimum':lo,**({'maximum':hi} if hi is not None else {})})
        elif field=='record_id':
            valid=isinstance(argument,str) and bool(argument)
            if operation=='navigate':
                valid |= isinstance(argument,list) and 0<len(argument)<=128 and all(isinstance(v,str) and v for v in argument) and len(set(argument))==len(argument)
            value(valid,field,{'source':'navigate record IDs; navigate also accepts a unique list of 1..128 IDs'})
        elif field=='address':
            valid=lambda v:type(v) is int and 0<=v<=65535
            ok=(isinstance(argument,list) and 0<len(argument)<=128 and all(valid(v) for v in argument) and len(set(argument))==len(argument)
                if arguments.get('view')=='ram_set' else valid(argument))
            value(ok,field,{'type':'unique array of 1..128 integers' if arguments.get('view')=='ram_set' else 'integer','minimum':0,'maximum':65535})
        elif field=='query':value(isinstance(argument,dict),field,{'type':'search_query object'})
        elif field=='names':value(isinstance(argument,list) and all(isinstance(v,str) and v for v in argument),field,{'type':'array of nonempty strings'})
        elif field in ('operations','claims','decisions'):
            value(isinstance(argument,list) and all(isinstance(v,dict) for v in argument),field,{'type':'array of objects'})
    if operation=='preview':
        from . import edit_contract
        shapes={kind:shape for owner in edit_contract.owners() for kind,shape in owner.OPERATION_SCHEMAS.items()}
        for op in arguments['operations']:
            value(isinstance(op.get('kind'),str),'operations[].kind',{'enum':list(shapes)})
            if op['kind'] in shapes:
                edit_contract.check(op,shapes[op['kind']],'REQUEST_SCHEMA')
            # Unknown/forbidden kinds retain their owner's access check.


def entry(operation, role, profile='corridor'):
    result = keys((investigating() if profile=='investigation' else corridor() if profile == 'corridor' else retained())[operation])
    sources = {
        'cid': ['confirm.candidate', 'preview.candidate'],
        'preview_digest': ['preview.preview_digest'],
        'input_id': ['inputs.records[].id'],
        'generation': ['status.generation'],
    }
    if profile == 'corridor':
        sources.update(ticket=['status.ticket'], sequence=['status.handoff.latest_review.sequence'])
        if role == 'reviewer':
            sources.update({key: ['status.handoff.published_candidate.' + key]
                            for key in ('cid', 'revision', 'attempt')})
        elif operation == 'validation_evidence':
            sources.update(cid=['validate.candidate'], revision=['validate.revision'], attempt=['validate.attempt'])
        if operation == 'review':
            sources.update(ticket=['status.handoff.coverage.required_edges[].1'],
                           generation=['status.handoff.coverage.required_edges[].1'],
                           base_generation=['status.handoff.coverage.required_edges[].0'])
    elif operation == 'review':
        sources['base_generation'] = ['status.evidence[-2].artifact_id']
    result['sources'] = {key: sources[key] for key in result['required'] + result['optional'] if key in sources}
    if not result['sources']:
        del result['sources']
    if operation == 'input' and role == 'implementer' and profile == 'corridor':
        result['reference_image'] = keys(IMAGE_INPUT)
    return result


DESCRIPTION_MARKER = '\nArgument contract (required and optional keys; no other keys accepted):\n'


def describe(operations, role, profile='corridor'):
    from .error_policy import HELP
    if profile=='investigation':
        return ('Read operation-reference and investigation-assignment through input. '
                'This phase is read-only. citation resolves delivered native record IDs to checked citations. '
                'checkpoint stages claims; only the final native audit can accept coverage. '
                'Generation comes from status.generation; input IDs from inputs.records[].id.'+HELP+
                DESCRIPTION_MARKER+json.dumps({op:entry(op,role,profile) for op in operations},separators=(',',':')))
    return ('Read input input_id=operation-reference for value contracts and edit/query shapes before editing. '
            'Sources are paths in your role results; [] selects a record, .0/.1 an array element. Review every required edge, taking all three identities from the same pair. '
            'A new preview has no candidate: '
            'use confirm.candidate first; preview.candidate refers to an existing candidate. '
            'Retained review uses the last two evidence entries.' + HELP
            + DESCRIPTION_MARKER + json.dumps(
        {op: entry(op, role, profile) for op in operations}, separators=(',', ':')))


def complete_entry(operation, role, profile='corridor', document_paths=()):
    from . import guidance, navigation, evidence_views, artifact_edits, rename_service
    result=entry(operation,role,profile)
    values={
        'kind':{'enum':['record','ram']},
        'claims':{'type':'array of investigation_claim'},
        'decisions':{'type':'array of investigation_decision'},
        'symbol':{'authored':'nonempty symbol spelling; use navigate symbols to discover names'},
        'names':{'authored':'array of symbol spellings to check in prose'},
        'report':{'authored':'review Markdown with exactly one Learning Candidates section'},
        'response':{'authored':'rework Markdown, nonempty, at most 65536 UTF-8 bytes, exactly one Learning Candidates section'},
        'operations':{'type':'array of operations from this reference'},
        'path':{'enum':list(document_paths)},
        'name':{'enum':list(guidance.NAMES)},
        'query':{'type':'search_query'},
        'view':{'enum':list(navigation.VIEWS if operation=='navigate' else rename_service.EVIDENCE_ARGUMENTS)},
        'record_id':{'source':'navigate.records[].record_id or their expressions[].record_id and recursive children',
                     'source_view':'For navigate source, also accepts 1..128 unique statement IDs, selecting their lexical label blocks together; span must be label. For navigate edit, the same array selects exactly those statements, not their blocks; span must be label.'},
        'address':{'authored':'integer in 0..65535; evidence ram_set instead requires 1..128 unique such integers'},
        'contains':{'authored':'nonempty substring up to 256 characters'},
        'decoder':{'enum':list(evidence_views.DECODERS)},
        'artifact':{'enum':sorted(artifact_edits.PATHS)},
        'key':{'source':'evidence(view=artifact_rows).records[].key'},
        'set_id':{'source':'evidence(view=ram_compact).shared.set_id'},
        'analogue_index':{'enum':[0,1]},
        'span':{'enum':list(navigation.SPANS),'default':'label',
                'constraint':'segment is only valid with navigate view=records, records_compact or source (single selector)'},
        'byte_offset':{'authored':'nonnegative integer within the selected data'},
        'byte_count':{'authored':'integer in 1..4096 within the selected data; align offset/count to decoder width'},
        'offset':{'source':'same operation next_offset; 0 for first page'},
        'limit':{'authored':'positive integer; omit to use the route default',
                 'view_limits':'navigate source permits 1..128; other navigate views 1..40. RAM set/summary/compact/shared permit 1..128.',
                 'maximum':{'navigate':128,'input':8192,'guidance':400,'document':80,'review_report':1024}.get(operation,40)},
        'continuation':{'source':'search.continuation; absent for first page'},
    }
    if operation=='validation_evidence':
        result['availability']='Failure diagnostics only; EVIDENCE_UNAVAILABLE when no error records exist. Read candidate_status.gates for successful checks.'
    result['values']={key:values[key] for key in result['required']+result['optional']
                      if key not in result.get('sources',{}) and key in values}
    return result
