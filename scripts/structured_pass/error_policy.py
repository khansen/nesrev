"""Recovery is about a valid next request, not the spelling of an error code.

Correctable refusals leave state unchanged and have a correction obtainable
from delivered results or a missing earlier step. Only busy states are
transient. Access/boundary, integrity/provenance, tooling/configuration drift,
internal failures and exhausted limits are terminal. Unknown codes fail closed.
"""

TRANSIENT = frozenset('''
REVIEW_RESTORE_IN_PROGRESS REVIEW_STATE_BUSY VALIDATION_IN_PROGRESS
'''.split())
CORRECTABLE = frozenset('''
ARTIFACT_EDIT_PREIMAGE ARTIFACT_EDIT_SCHEMA ARTIFACT_ROW_DUPLICATE ARTIFACT_ROW_INVALID
CANDIDATE_NOT_AMENDABLE CANDIDATE_NOT_PUBLISHABLE CANDIDATE_NOT_VALIDATABLE
CHAIN_REQUIRES_PUBLISHED_BASE CLOSEOUT_REQUIRED COMMENT_NOT_FOUND COMMENT_PREIMAGE_MISMATCH
CORRIDOR_NOT_PUBLISHED CORRIDOR_NOT_STARTED CORRIDOR_WRAPPER_REQUIRED DECLARATION_ANCHOR_REQUIRED
DOCUMENT_DUPLICATE_OPERATION DOCUMENT_NOT_FOUND DOCUMENT_PASS_MISMATCH DOCUMENT_PATH_CASE_MISMATCH
DOCUMENT_SCHEMA DUPLICATE_DECLARATION DUPLICATE_RENAME EVIDENCE_RANGE_INVALID
EVIDENCE_REQUEST_INVALID INPUT_MEDIA_REQUIRED INPUT_UNKNOWN INVALID_AMENDMENT INVALID_BATCH
INVALID_COMMENT INVALID_PAGINATION INVALID_RENAME INVALID_SYMBOL LEARNING_BODY_INVALID
INVESTIGATION_CHECKPOINT_INVALID INVESTIGATION_CITATION_INVALID INVESTIGATION_COVERAGE_INCOMPLETE
LEARNING_INPUT_INVALID LEARNING_REQUIRED LEARNING_TOO_LARGE LEDGER_PREIMAGE_MISMATCH
LEDGER_RENAME_MISMATCH LEDGER_SCHEMA MIXED_DOCUMENT_SCHEMA MIXED_GENERATION_COMPARISON
NAVIGATION_AMBIGUOUS_SYMBOL NAVIGATION_RECORD_REQUIRED NAVIGATION_SELECTION_REQUIRED
NAVIGATION_UNKNOWN_SYMBOL NONZERO_BASE_REQUIRES_DIAGNOSTIC_COMPARISON OVERLAPPING_EDITS
PREIMAGE_MISMATCH PREVIEW_ITEM_TOO_LARGE PREVIEW_REQUIRED REQUEST_SCHEMA REVIEW_COVERAGE_INCOMPLETE
REVIEW_NOT_READY SEARCH_INPUT_UNKNOWN SEARCH_SCHEMA SINGLE_OPERAND_INSTRUCTION_REQUIRED
SOURCE_EDIT_EXPRESSION SOURCE_EDIT_OVERLAP SOURCE_EDIT_PREIMAGE SOURCE_EDIT_SCHEMA STALE_GENERATION
STALE_PREVIEW STALE_VALIDATION_EVIDENCE UNCHANGED_LEDGER_REQUIRED UNDISPOSED_STALE_PROSE
UNKNOWN_CANDIDATE UNKNOWN_CONSTANT UNKNOWN_GENERATION UNKNOWN_OPERATION UNKNOWN_PREVIEW
UNKNOWN_RECORD UNSUPPORTED_EXPRESSION UNSUPPORTED_OPERATION WARNING_NOT_CURRENT
WARNING_RATIONALE_REQUIRED
'''.split())
TERMINAL = frozenset('''
APPLICATION_APPROVAL_CHANGED APPLICATION_FRICTION_CHANGED APPLICATION_FRICTION_DIRTY
ARTIFACT_BLOB_MISMATCH ARTIFACT_CAPTURE_MISMATCH ARTIFACT_EXPORT_FAILED ARTIFACT_FILE_MISMATCH
ARTIFACT_LAYOUT_UNSUPPORTED ARTIFACT_MANIFEST_MISMATCH ARTIFACT_PATH_INVALID
ARTIFACT_PROVENANCE_MISMATCH ARTIFACT_SCHEMA_UNSUPPORTED ARTIFACT_UNIT_MISMATCH
BASE_ARTIFACT_MISMATCH BRIDGE_RUN_CHANGED CANDIDATE_CHANGED_AFTER_VALIDATION CANDIDATE_SETUP_FAILED
CAPTURE_CHANGED CAPTURE_SOURCE_MISMATCH CLOSEOUT_ALREADY_APPLIED CLOSEOUT_EVIDENCE_UNAVAILABLE
CLOSEOUT_RESULT_INVALID CLOSEOUT_TOOLING_CHANGED CORRIDOR_CONFIG_CHANGED CORRIDOR_OUTSIDE_PASS
CORRIDOR_ROLE_INVALID CORRIDOR_RUN_CHANGED DEFERRAL_ROW_CONFLICT DESTINATION_EXISTS
DOCUMENT_DELETE_CANONICAL_FORBIDDEN DOCUMENT_PATH_FORBIDDEN DOCUMENT_PREIMAGE_MISMATCH
EVIDENCE_UNAVAILABLE FILE_WRITES_NOT_ENABLED_IN_THIS_CASE FORBIDDEN_PATH GATE_ENVIRONMENT_INVALID
GATE_TOOLCHAIN_CHANGED GATE_TOOLCHAIN_UNAVAILABLE GENERATED_CATALOG_WRONG
GENERATED_PATH_SERVICE_OWNED GENERATION_INPUT_CHANGED HEAD_OWNED_BY_PUBLISHER HEAVY_RUN_IN_PROGRESS
INPUTS_UNAVAILABLE INPUT_CHANGED INPUT_LIMIT_EXCEEDED INPUT_SELECTION_INVALID
INVESTIGATION_CHANGED INVESTIGATION_PLAN_INVALID INVESTIGATION_RECEIPT_INVALID
INVESTIGATION_CHECKPOINT_TOO_LARGE INVESTIGATION_TRANSITION_INVALID INVESTIGATION_READ_ONLY
INVESTIGATION_AUDIT_MISMATCH INVESTIGATION_CONFLICT
INSUFFICIENT_DISK_SPACE INTERNAL_SERVICE_ERROR INVALID_REVIEW_PROVENANCE LEARNING_HISTORY_CHANGED
LEARNING_SOURCE_CHANGED MISSING_REVIEW_PROVENANCE MIXED_DOCUMENT_PREIMAGE
MIXED_FILE_REQUIRES_TYPED_UPDATE MULTI_RECORD_SELECTION_UNSUPPORTED NEW_GATE_FAILURE
OWNERSHIP_MANIFEST_INVALID PASS_BASE_NOT_ANCESTOR PREVIEW_CONTENT_CHANGED PREVIEW_DIGEST_MISMATCH
PRODUCER_CERTIFICATION_FAILED PRODUCER_UNAVAILABLE PROJECT_PROFILE_CHANGED PROJECT_PROFILE_INVALID
PUBLICATION_CHAIN_LIMIT PUBLICATION_RECEIPT_MISMATCH PUBLISHER_BASE_MISMATCH PUBLISHER_HEAD_MISMATCH
PUBLISHER_STATE_UNAVAILABLE PUBLISHER_STORE_MISMATCH RAW_RAM_JUDGMENT_CHANGED
RAW_RAM_REFRESH_UNSUPPORTED REASSEMBLY_DEPENDENCY_INVALID REASSEMBLY_FAILED
REASSEMBLY_INPUT_OUTSIDE_TREE RECORD_ALIGNMENT_FAILED REFERENCE_CHANGED REFERENCE_FORMAT_UNSUPPORTED
REFERENCE_INVALID RESPONSE_TOO_LARGE RETENTION_NOT_CONFIGURED RETENTION_PATH_INVALID
REVIEWER_MUTATION_DENIED REVIEWER_ONLY REVIEW_ARCHIVE_EXISTS REVIEW_PASS_CONTEXT_MISSING
REVIEW_PROFILE_INVALID REVIEW_READ_ONLY REVIEW_SESSION_CHANGED ROM_PARITY RUNTIME_PROFILE_MISMATCH
SEARCH_CONTINUATION_INVALID SEARCH_INPUT_UNAVAILABLE SEARCH_ITEM_TOO_LARGE SEMANTIC_CONTRACT
SOURCE_EDIT_BINDING SOURCE_EDIT_BOUNDARY SOURCE_EDIT_IDENTITY SOURCE_EDIT_LAYOUT
SOURCE_EDIT_LIVE_DECLARATION SOURCE_EDIT_SCOPE SOURCE_MODEL_BINARY SOURCE_MODEL_IDENTITY
SOURCE_MODEL_INPUT SOURCE_MODEL_INVOCATION SOURCE_MODEL_JOIN SOURCE_MODEL_NOT_CERTIFIED
SOURCE_MODEL_PARITY SOURCE_MODEL_PARTITION SOURCE_MODEL_PRODUCER SOURCE_MODEL_SCHEMA
TOOLCHAIN_UNAVAILABLE TOOLING_IDENTITY_MISMATCH VALIDATION_INTERRUPTED VERDICT_OUTSIDE_PASS
VERIFICATION_POLICY_CHANGED VERIFICATION_POLICY_INVALID WARNING_IDENTITY_CHANGED
WARNING_LAYOUT_UNSUPPORTED WARNING_ORDER_CHANGED WRAPPER_OWNED_FIELD WRAPPER_OWNED_ROW
WRONG_DECLARATION_SCOPE
'''.split())
ACTIONS = {
    'correctable': 'Correct your request using the field contract; continue within this turn and its budgets.',
    'transient': 'Wait and retry the same request within the deadline.',
    'terminal': 'Stop and report this refusal; do not replace the client invocation.',
}
HELP = (' error_class decides recovery: correctable=fix your request in this turn; '
        'transient=wait and retry unchanged within the deadline; terminal=stop. '
        'No class authorizes a replacement invocation.')


def classify(code):
    return 'transient' if code in TRANSIENT else 'correctable' if code in CORRECTABLE else 'terminal'


def diagnostics(code, operation, role, profile):
    from . import operation_contract as contract
    sources = {
        'STALE_GENERATION': ('generation', 'status.generation'),
        'UNKNOWN_GENERATION': ('generation', 'status.generation'),
        'STALE_PREVIEW': ('preview_digest', 'fresh preview.preview_digest at status.generation'),
        'UNKNOWN_PREVIEW': ('preview_digest', 'preview.preview_digest'),
        'PREIMAGE_MISMATCH': ('operations[].preimage', 'navigate.records[].preimage_sha256'),
        'SOURCE_EDIT_PREIMAGE': ('operations[].preimage', 'navigate or evidence preimage for the selected record'),
        'COMMENT_PREIMAGE_MISMATCH': ('operations[].preimage', 'navigate(view=comments).records[].preimage_sha256'),
        'LEDGER_PREIMAGE_MISMATCH': ('operations[].preimage', 'inspect.ledger.sha256'),
        'ARTIFACT_EDIT_PREIMAGE': ('operations[].preimage/changes[].preimage', 'evidence(view=artifact_rows) file and row hashes'),
        'STALE_VALIDATION_EVIDENCE': ('cid/revision/attempt', 'candidate_status of the published candidate from status'),
    }
    if code in sources:
        field, source = sources[code]
        return {'field': field, 'source': source}
    from . import source_edits, artifact_edits, authored_documents, mixed_documents
    owner_types = {code:sorted(owner.REFERENCE_TYPES) for code,owner in (
        ('SOURCE_EDIT_SCHEMA',source_edits),('ARTIFACT_EDIT_SCHEMA',artifact_edits),
        ('DOCUMENT_SCHEMA',authored_documents),('MIXED_DOCUMENT_SCHEMA',mixed_documents))}
    owner_types['SEARCH_SCHEMA']=['search_query']
    if code in owner_types:
        return {'field': 'query' if code == 'SEARCH_SCHEMA' else 'operations[]',
                'contract_sources': ['input(operation-reference).types.'+name for name in owner_types[code]]}
    if operation in contract.offered(role,profile):
        return {'field':'arguments', 'expected':contract.complete_entry(operation,role,profile),
                'source':'status and operation-reference; re-read current facts before correcting'}
    return {'field':'operation','accepted_values':contract.offered(role,profile)}


def describe(code, correction=None, request_error=False):
    category = ('correctable' if request_error or (code == 'RESPONSE_TOO_LARGE' and correction)
                else classify(code))
    if code == 'RESPONSE_TOO_LARGE' and category == 'terminal':
        return {'error_class': category, 'retryable': False}
    return {'error_class': category, 'action': correction or ACTIONS[category], 'retryable': category == 'transient'}


def repeated_refusals(calls):
    """Summarize identical correctable requests without retaining their values."""
    import hashlib
    import json
    counts = {}
    for call in calls:
        result = call['result']
        if result.get('error_class') != 'correctable':
            continue
        code = result['error']
        operation = call['operation']
        fingerprint = hashlib.sha256(json.dumps([operation, call['arguments']],
            sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode()).hexdigest()
        key = (operation, code, fingerprint)
        counts[key] = counts.get(key, 0) + 1
    return [{'operation':operation, 'error':code, 'request_sha256':fingerprint,
             'count':count, 'disposition':'learning candidate: repeated correctable refusal'}
            for (operation,code,fingerprint),count in sorted(counts.items()) if count > 1]
