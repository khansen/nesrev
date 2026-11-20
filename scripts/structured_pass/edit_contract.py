"""Render edit shapes owned and enforced by the individual operation modules."""
import json
from . import operation_contract as contract

INPUT_ID = 'operation-reference'
value = contract.value


def fields(required, optional='', **notes):
    return {'required': required.split(), 'optional': optional.split(), **notes}


def check(value, spec, code, *, path='operations[]'):
    required = list(spec['required'])
    for condition in spec.get('when', []):
        if isinstance(value, dict) and value.get(condition['field']) == condition['equals']:
            required += condition.get('required', [])
    contract.check(value, (required, spec['optional']), code=code, path=path)


def owners():
    from . import rename_service, source_edits, artifact_edits, authored_documents, mixed_documents
    return (rename_service, source_edits, artifact_edits, authored_documents, mixed_documents)


def reference(document_paths=()):
    operations = {}; types = {}
    for owner in owners():
        for kind, spec in owner.OPERATION_SCHEMAS.items():
            if kind in operations:
                raise ValueError('DUPLICATE_OPERATION_CONTRACT')
            operations[kind] = {**spec}
        for name, spec in owner.REFERENCE_TYPES.items():
            if name in types:
                raise ValueError('DUPLICATE_OPERATION_CONTRACT')
            types[name] = spec
    from . import search, navigation, rename_service, evidence_views
    types['document_fields']={**types['document_fields'],'path':{'enum':list(document_paths)}}
    profiles={name:{operation:contract.complete_entry(operation,role,profile,document_paths)
                    for operation in contract.offered(role,profile)}
              for name,role,profile in (('implementer','implementer','corridor'),
                    ('reviewer','reviewer','corridor'),('retained-reviewer','reviewer','retained'))}
    queries={kind:contract.keys(spec) for kind,spec in search.QUERY_SCHEMAS.items()}
    types['search_query']={'variants':queries,'fields':{
        'kind':{'enum':list(search.QUERY_SCHEMAS)},
        'kinds':{'enum_items':list(search.INPUT_KINDS),'length':'1..2, unique'},
        'alternatives':{'type':'array of arrays of search_predicate','length':'1..8 alternatives; 1..2 predicates each'},
        'owner_id':{'source':'navigate.records[].record_id for a declaration'},
        'inputs':{'source':'search(kind=catalogue).rows[].input_id','length':'1..32, unique'},
        'terms':{'authored':'array of nonempty strings, at most 256 characters each'},
        'prefixes':{'authored':'array of nonempty strings, at most 256 characters each'},
        'ignore_case':{'authored':'boolean'},'whole_token':{'authored':'boolean'},
        'context':{'type':'search_context'}},
        'text_constraint':'terms and/or prefixes required; at most 32 strings total; no regex'}
    types['search_context']={**contract.keys(search.CONTEXT_SCHEMA),
        'values':{'authored':'integers 0..10; defaults 0'}}
    types['search_predicate']={**contract.keys(search.PREDICATE_SCHEMA),'nonempty':True,
        'fields':{'mnemonics':{'enum_items':sorted(search.MNEMONICS),'length':'1..16 unique'},
            'modes':{'enum_items':sorted(search.MODES),'length':'1..16 unique'},
            'operand':{'enum':list(search.OPERANDS)},'shapes':{'enum_items':sorted(search.SHAPES),'length':'1..16 unique'},
            'values':{'authored':'1..32 unique signed 64-bit integers'},
            'ranges':{'authored':'1..4 inclusive [lo,hi] signed 64-bit integer pairs, lo<=hi'}}}
    return {'schema': 'operation-reference-v1',
            'instructions': ['Each operation requires kind equal to its entry name.',
                'No other fields are accepted. Conditional required fields apply when their selector matches.',
                'Use record identities and preimages from the same generation. Never infer them from addresses.',
                'In a corridor preview, include scorecard_update and closeout together.',
                'After preview, confirm its preview_digest; validate and publish confirm.candidate as cid.'],
            'arguments': profiles,
            'view_arguments': {'evidence':{view:contract.keys(spec) for view,spec in rename_service.EVIDENCE_ARGUMENTS.items()},
                'navigate':{'views':list(navigation.VIEWS),'selection':'records/uses require exactly one of symbol or record_id; symbols/comments forbid both; contains is for symbols/comments only'},
                'ram':'exactly one of address or record_id for ram and ram_compact',
                'analogue_index':'only the seven base evidence views and navigation; selected models only',
                'decode':{'decoders':list(evidence_views.DECODERS),'byte_count':'1..4096','default_byte_count':256}},
            'operations': operations, 'types': types}


def text(document_paths=()):
    return (json.dumps(reference(document_paths), ensure_ascii=True, sort_keys=True, indent=2)+'\n').encode()
