"""Argument-key tables shared by dispatch and the client-visible declaration.

These describe outer argument keys only. Value checks, role authorization,
generation integrity and nested edit/query schemas remain with their owners.
"""
import json

REQUEST_COUNTING = (
    'The practicality ceiling is eight logical requests per independent evidence question. '
    'Continuation pages of an unchanged operation and query count as one request: only offset '
    'or the returned continuation token may differ. Keep generation, selector, filters, span '
    'and limit unchanged. A changed selector, including record_id, is a new request; use '
    'next_offset with the original selector to page a segment span. Report logical requests '
    'and transport calls separately. Retrieve every page needed for the question; an incomplete '
    'page is not absence evidence. Do not relabel an unchanged question to evade the ceiling.'
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


def corridor():
    return {k:v for k,v in {**BASE, **RENAME, **VERDICT, **CORRIDOR}.items() if k!='guidance'}


def offered(role, profile='corridor'):
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
        raise RequestError(code, field=path, missing=missing,
                           unexpected_keys=not set(value) <= set(required) | set(optional), **expected)


def entry(operation, role, profile='corridor'):
    result = keys((corridor() if profile == 'corridor' else retained())[operation])
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
        'symbol':{'authored':'nonempty symbol spelling; use navigate symbols to discover names'},
        'names':{'authored':'array of symbol spellings to check in prose'},
        'report':{'authored':'review Markdown with exactly one Learning Candidates section'},
        'response':{'authored':'rework Markdown, nonempty, at most 65536 UTF-8 bytes, exactly one Learning Candidates section'},
        'operations':{'type':'array of operations from this reference'},
        'path':{'enum':list(document_paths)},
        'name':{'enum':list(guidance.NAMES)},
        'query':{'type':'search_query'},
        'view':{'enum':list(navigation.VIEWS if operation=='navigate' else rename_service.EVIDENCE_ARGUMENTS)},
        'record_id':{'source':'navigate.records[].record_id or their expressions[].record_id and recursive children'},
        'address':{'authored':'integer in 0..65535'},
        'contains':{'authored':'nonempty substring up to 256 characters'},
        'decoder':{'enum':list(evidence_views.DECODERS)},
        'artifact':{'enum':sorted(artifact_edits.PATHS)},
        'key':{'source':'evidence(view=artifact_rows).records[].key'},
        'set_id':{'source':'evidence(view=ram_compact).shared.set_id'},
        'analogue_index':{'enum':[0,1]},
        'span':{'enum':list(navigation.SPANS),'default':'label',
                'constraint':'segment is only valid with navigate view=records'},
        'byte_offset':{'authored':'nonnegative integer within the selected data'},
        'byte_count':{'authored':'integer in 1..4096 within the selected data; align offset/count to decoder width'},
        'offset':{'source':'same operation next_offset; 0 for first page'},
        'limit':{'authored':'positive integer; omit to use the route default',
                 'maximum':{'input':8192,'guidance':400,'document':80,'review_report':1024}.get(operation,40)},
        'continuation':{'source':'search.continuation; absent for first page'},
    }
    if operation=='validation_evidence':
        result['availability']='Failure diagnostics only; EVIDENCE_UNAVAILABLE when no error records exist. Read candidate_status.gates for successful checks.'
    result['values']={key:values[key] for key in result['required']+result['optional']
                      if key not in result.get('sources',{}) and key in values}
    return result
