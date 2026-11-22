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
    from . import search, navigation, rename_service, evidence_views, ram_evidence
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
        'detail':{'enum':list(search.DETAILS),'default':'full',
                  'matches':'Zero context only. Keeps every match/unknown and its native owner identity; read source facts and preimages with navigate. Rows use instruction-matches-columnar-v1: zip columns with each row array, place instruction.* keys under instruction, and add constants. Every page decodes independently.',
                  'instruction_fields':list(search.MATCH_FIELDS)},
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
            'request_counting': contract.REQUEST_COUNTING,
            'question_budget': {'logical_requests':8,'text_response_bytes':contract.QUESTION_BYTES,
                'page_maximum_bytes':24576,'counter':'volume.response_bytes on every text tool response',
                'conversation_allowance':'Numeric allowance in the prepared task, including startup cost, lifecycle reserve and at least 10 percent estimation margin. Use the smaller of this remainder and the question ceiling; missing allowance requires a decision.',
                'first_page':'total_rows for search, total_records for compact RAM, total for navigation; search minimum_response_bytes excludes envelopes and is only a lower bound',
                'enforcement':'Caller accounting; no automatic question/session counter. Narrow or stop before exceeding either ceiling.'},
            'arguments': profiles,
            'view_arguments': {'evidence':{view:contract.keys(spec) for view,spec in rename_service.EVIDENCE_ARGUMENTS.items()},
                'navigate':{'views':list(navigation.VIEWS),'selection':'records/records_compact/source/uses require exactly one of symbol or record_id; symbols/comments forbid both; contains is for symbols/comments only',
                    'source':{'columns':list(navigation.SOURCE_COLUMNS),'encoding':'source-text-v1: zip columns with each record row; every page declares its columns.',
                        'coverage':'Read source and analogues here before editing. Text is exact producer-span source; comments are included separately once. No preimages, expression trees or inferred semantics. Fetch records or records_compact for selected edits in the same generation.',
                        'batch':'record_id may instead be 1..128 unique statement IDs, with span=label. Returns the union of their lexical label blocks, deduplicated in source order. Single selectors support span=segment. Page with unchanged selectors and next_offset; at most 128 lean records per page, still bounded by 24 KiB.'},
                    'records_compact':{'encoding':'source-records-columnar-v1',
                        'decode':navigation.COMPACT_HELP,
                        'coverage':'Lossless editing records with the same selectors, span and continuation as records. Use source for reading; fetch these records when preparing edits.'},
                    'records_span':{'enum':list(navigation.SPANS),'default':'label',
                        'segment':'Cross global labels within one segment, stopping before ORG/END or a changed segment. EQU/ORG/END selections stay single records. Up to 40 records, fewer if needed for the response cap. Lexical coverage, not control-flow proof.',
                        'continuation':'Keep the starting selector and use next_offset. next_record_id identifies the next undelivered statement, or null at the boundary; scope.boundary_record_id names the excluded boundary. A new record_id selector is a new logical request.'}},
                'ram':'exactly one of address or record_id for ram, ram_compact and ram_summary',
                'ram_set':{'address':'1..128 unique integer addresses, each in 0..65535; required, no record_id',
                    'limit':'1..128; start with 128',
                    'coverage':'Read the entire selected corridor byte set together, not a full ram_summary for each byte. Every legacy fact is retained, including direct accesses and their proofs, possible indexed sites and unresolved indirect sites. Equal facts occur once with their exact addresses membership; different proof/category facts stay separate. All pages are needed; no ram_shared download.',
                    'decode':'Expand constants plus columns zipped with each row, then dictionaries as in ram_summary. For each address in addresses, copy the row without addresses and add requested_address=address and requested_declaration_id=null. This exactly reconstructs the original per-byte RAM evidence.'},
                'ram_summary':{'limit':'1..128; start with 128',
                    'coverage':'Every access row, owner, alias proof, possible indexed alias and unresolved indirect destination. Includes shared unknowns; no ram_shared fetch is needed.',
                    'encoding':'ram-columnar-summary-v1: constants plus columns zipped with each row; then for each field in dictionaries replace row[field] with dictionaries[field][str(row[field])]. Each page contains its own complete dictionaries and decodes independently.',
                    'omitted_fields':list(ram_evidence.SUMMARY_OMITTED),
                    'details':'Use navigate records with the same generation and record_id for source locations and edit preimages. The ram/ram_compact views remain unchanged. A possible access is still unknown, never a proven destination.'},
                'analogue_index':'only the seven base evidence views and navigation; selected models only',
                'decode':{'decoders':list(evidence_views.DECODERS),'byte_count':'1..4096','default_byte_count':256}},
            'operations': operations, 'types': types}


def text(document_paths=()):
    return (json.dumps(reference(document_paths), ensure_ascii=True, sort_keys=True,
                       separators=(',', ':'))+'\n').encode()
