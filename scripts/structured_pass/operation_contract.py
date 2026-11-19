"""Argument-key tables shared by dispatch and the client-visible declaration.

These describe outer argument keys only. Value checks, role authorization,
generation integrity and nested edit/query schemas remain with their owners.
"""
import json

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
    'navigate': (('generation', 'view'), ('symbol', 'record_id', 'contains', 'offset', 'limit', 'analogue_index')),
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
    return {**BASE, **RENAME, **VERDICT, **CORRIDOR}


def retained(profile='source-v2'):
    names = ['evidence']
    if profile in ('rename', 'source-v2'):
        names += ['navigate', 'inspect', 'q09', 'document', 'inputs', 'input', 'guidance']
    return {'query': BASE['query'], **{name: RENAME[name] for name in names}, **RETAINED}


def keys(spec):
    required, optional = spec
    return {'required': list(required), 'optional': list(optional)}


def check(value, spec):
    required, optional = spec
    if (not isinstance(value, dict) or not set(required) <= set(value)
            or not set(value) <= set(required) | set(optional)):
        raise ValueError('REQUEST_SCHEMA')


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
        if operation == 'review':
            sources.update(generation=['status.handoff.coverage.pass_head'],
                           base_generation=['status.handoff.coverage.pass_base'])
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
    return ('Sources are paths in operation results, not argument names; [] means a record in a list. '
            'Use non-null identities from the current workflow. A new preview has no candidate: '
            'use confirm.candidate first; preview.candidate refers to an existing candidate. '
            'A source operation may belong to the other role. Retained review uses the last two evidence entries.'
            + DESCRIPTION_MARKER + json.dumps(
        {op: entry(op, role, profile) for op in operations}, separators=(',', ':')))
