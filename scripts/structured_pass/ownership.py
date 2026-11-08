"""Operator-owned path registry. A suffix or an existing file grants no writes."""
from pathlib import PurePosixPath

from .producer import require

SCHEMA = 'structured-pass-ownership-v1'
DOCUMENTS = frozenset({
    'docs/crosswalk/TERMINOLOGY_CROSSWALK.md',
    *('docs/reverse_engineering/'+name for name in (
        'ONBOARDING.md', 'QUICK_REFERENCE.md', 'MEMORY_MAP.md',
        'SEMANTIC_CLAIMS.md', 'WORKING_NOTES.md', 'CURIOSITIES.md',
        'PARITY_GAPS.md', 'ACTOR_ENUMS.md')),
})
TYPED = {
    'docs/reverse_engineering/inventory/renames.csv': 'rename-ledger',
    'docs/reverse_engineering/inventory/data_extent_assertions.csv': 'extent-rows',
    'docs/reverse_engineering/inventory/data_blob_dispositions.csv': 'blob-rows',
    'docs/reverse_engineering/WARNING_BASELINE.txt': 'warning-baseline',
    **{'docs/reverse_engineering/inventory/'+name: owner for name, owner in (
        ('data_format_targets.csv', 'deferred-row-writer'),
        ('policy_baseline.csv', 'deferred-row-writer'),
        ('proof_debt_acknowledged.csv', 'deferred-row-writer'),
        ('kpis.conf', 'kpi-wrapper'),
        ('constant_magic_allowlist.csv', 'allowlist-writer'),
        ('hardware_local_allowlist.txt', 'allowlist-writer'),
        ('runtime_evidence.json', 'runtime-writer'),
        ('process_friction_receipts.json', 'friction-wrapper'))},
    'PROCESS_FRICTION.md': 'friction-wrapper',
}


def registry(paths=()):
    require(isinstance(paths, (list, tuple)), 'OWNERSHIP_MANIFEST_INVALID')
    result=set(DOCUMENTS); seen={p.casefold() for p in result}
    for path in paths:
        require(isinstance(path, str), 'OWNERSHIP_MANIFEST_INVALID')
        parts=PurePosixPath(path).parts
        require(path.startswith('docs/') and path.endswith('.md')
                and str(PurePosixPath(path))==path and all(not p.startswith('.') for p in parts)
                and not any(c in path for c in '\\\x00\r\n')
                and not any(p.casefold() in ('inventory','reviews') for p in parts)
                and path.casefold() not in ('docs/reverse_engineering/progress_scorecard.md',),
                'OWNERSHIP_MANIFEST_INVALID')
        require(path.casefold() not in seen or path in result, 'OWNERSHIP_MANIFEST_INVALID')
        result.add(path); seen.add(path.casefold())
    return {'schema': SCHEMA, 'authored_documents': sorted(result)}


def read(value):
    require(isinstance(value, dict) and set(value)=={'schema','authored_documents'}
            and value['schema']==SCHEMA, 'OWNERSHIP_MANIFEST_INVALID')
    expected=registry(value['authored_documents'])
    require(value==expected, 'OWNERSHIP_MANIFEST_INVALID')
    return expected['authored_documents']
