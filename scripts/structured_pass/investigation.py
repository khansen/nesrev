"""Frozen investigation evidence and checked, immutable checkpoint payloads.

This module validates data. Callers must hold the session lock and supply
service-owned delivery receipts, reconciled with the finished native audit.
"""
import json

from . import analogue_inputs, corridor_inventory, navigation, ram_evidence, review_pages, declared_inputs, operation_contract
from .model import digest
from .producer import require, sha

ERRORS = frozenset('''INVESTIGATION_CHANGED INVESTIGATION_PLAN_INVALID
    INVESTIGATION_RECEIPT_INVALID INVESTIGATION_CHECKPOINT_INVALID
    INVESTIGATION_CHECKPOINT_TOO_LARGE INVESTIGATION_CITATION_INVALID
    INVESTIGATION_COVERAGE_INCOMPLETE INVESTIGATION_TRANSITION_INVALID
    INVESTIGATION_READ_ONLY INVESTIGATION_AUDIT_MISMATCH INVESTIGATION_CONFLICT'''.split())

CLAIM_SCHEMA=(tuple('id kind subject statement confidence citations searched_sets unknowns contrary'.split()),
              ('dependencies','conflicts'))
DECISION_SCHEMA=(('statement','claims'),())


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode()


def identity(value):
    return digest(canonical(value))


def catalog(model, generation, inventory):
    """Identities are built once for the whole parent, before partitioning."""
    corridor_inventory.verify(model, inventory)
    files = {p.name: sha(p) for p in sorted(model.capture.iterdir()) if p.is_file()}
    binding = {'generation': generation, 'source_sha256': digest(model.source),
               'model_id': model.document['identity']['model_id'],
               'capture_sha256': identity(files), 'inventory_sha256': inventory['inventory_sha256']}
    evidence = {}; units = {}; sets = {}

    def record(scope, source, record_id):
        node = source.node(record_id)
        content = {'statement': source.statement(node),
                   'source': source.source[slice(*source.ranges[node])].decode()}
        value = {'kind': 'record', 'scope': scope, 'record_id': record_id,
                 'content_sha256': identity(content)}
        key = 'S-' + identity([binding, value])
        evidence[key] = value
        units[key] = {'evidence_id': key}
        return key

    def block(name, scope, source, records):
        sets[name] = sorted({record(scope, source, r) for r in records})

    block('vector', 'local', model, inventory['vector_records'])
    for kind in ('roots', 'helpers', 'access_owner_blocks'):
        for i, row in enumerate(inventory[kind]):
            block(kind + ':' + str(i), 'local', model, row['records'])
    statements = {r for name, members in sets.items() for r in members}
    local_nodes = {model.node(evidence[key]['record_id']) for key in statements}
    dependencies = {decl for ref, decl in model.bindings.items() if model.context(ref) in local_nodes}
    block('declarations', 'local', model, [model.ids[n] for n in sorted(dependencies, key=lambda n: model.ranges[n])])
    for i, row in enumerate(inventory['analogues']):
        other = analogue_inputs.project(model, row['choice']['index'])
        block('analogues:' + str(i), 'analogue:' + str(row['choice']['index']), other, row['records'])
    rows = ram_evidence.set_rows(model, inventory['ram_addresses'])[0] if inventory['ram_addresses'] else []
    for address in inventory['ram_addresses']:
        sets['ram:' + str(address)] = []
    for row in rows:
        value = {'kind': 'ram', 'content_sha256': identity(row), 'fact': row}
        key = 'F-' + identity([binding, value])
        evidence[key] = value
        for address in row['addresses']:
            unit = key + ':' + str(address)
            units[unit] = {'evidence_id': key, 'address': address}
            sets['ram:' + str(address)].append(unit)
    sets = {name: sorted(values) for name, values in sets.items()}
    inputs={}
    if (model.capture/declared_inputs.FILE).is_file():
        for item in declared_inputs.load(model.capture)['items']:
            if item['kind']=='reference_image':continue
            text=(model.capture/item['file']).read_bytes().decode('utf-8')
            inputs[item['id']]={'sha256':item['sha256'],'characters':len(text)}
    result = {'schema': 'investigation-catalog-v1', 'binding': binding,
              'evidence': evidence, 'units': units, 'sets': sets, 'inputs':inputs}
    return {**result, 'sha256': identity(result)}


def check_catalog(value):
    require(set(value) == {'schema', 'binding', 'evidence', 'units', 'sets', 'inputs', 'sha256'} and
            value['schema'] == 'investigation-catalog-v1' and
            value['sha256'] == identity({k: v for k, v in value.items() if k != 'sha256'}),
            'INVESTIGATION_CHANGED')


def edit_targets(model, inventory):
    """The complete frozen edit envelope, independent of proposed names."""
    corridor_inventory.verify(model,inventory)
    rows=ram_evidence.set_rows(model,inventory['ram_addresses'])[0] if inventory['ram_addresses'] else []
    targets=set(inventory['vector_records'])|{r for block in inventory['roots']+inventory['helpers'] for r in block['records']}
    targets.update(r['record_id'] for r in rows if r['category'] in ('direct','indexed_exact_base','pointer_byte'))
    nodes={model.node(r) for r in targets}
    targets.update(model.ids[decl] for ref,decl in model.bindings.items() if model.context(ref) in nodes)
    return sorted(targets,key=lambda r:model.ranges[model.node(r)])


def record_page(value, model, record_ids, *, offset=0, limit=40, view='records_compact'):
    """Resolve checked noncontiguous targets with the requested native codec."""
    check_catalog(value)
    require(value['binding']['source_sha256'] == digest(model.source) and
            value['binding']['model_id'] == model.document['identity']['model_id'] and
            value['binding']['capture_sha256'] == identity({p.name: sha(p) for p in
                sorted(model.capture.iterdir()) if p.is_file()}), 'INVESTIGATION_CHANGED')
    allowed = {r['record_id'] for r in value['evidence'].values()
               if r['kind'] == 'record' and r['scope'] == 'local'}
    require(isinstance(record_ids, list) and bool(record_ids) and
            all(isinstance(r, str) and r in allowed for r in record_ids) and
            len(record_ids) == len(set(record_ids)) and type(offset) is int and offset >= 0 and
            type(limit) is int and 1 <= limit <= 40, 'INVESTIGATION_PLAN_INVALID')
    selected = sorted(record_ids, key=lambda r: model.ranges[model.node(r)])
    from . import edit_records
    require(view in ('records_compact', 'edit'), 'INVESTIGATION_PLAN_INVALID')
    nav = navigation.Navigation(model)
    project = nav.record if view == 'records_compact' else lambda n: edit_records.project(model, n)
    encode = navigation.compact_records if view == 'records_compact' else edit_records.encode
    rows = [project(model.node(r)) for r in selected[offset:offset+limit]]
    while True:
        end = offset + len(rows)
        result = encode({'generation': value['binding']['generation'],
            'catalog_sha256': value['sha256'], 'selection_sha256': identity(selected),
            'offset': offset, 'limit': limit, 'total': len(selected),
            'records': rows, 'next_offset': end if end < len(selected) else None})
        if review_pages.wire_size(result) <= review_pages.BUDGET - 4096:
            return result
        require(len(rows) > 1, 'RESPONSE_TOO_LARGE')
        rows.pop()


def partition_plan(value, assignments):
    """Each assignment selects whole root/interface/analogue or RAM-byte sets."""
    check_catalog(value)
    require(isinstance(assignments, list) and bool(assignments), 'INVESTIGATION_PLAN_INVALID')
    entries = []; names = set(); covered = set()
    for item in assignments:
        require(isinstance(item, dict) and set(item) == {'id', 'sets'} and
                isinstance(item['id'], str) and item['id'] and item['id'] not in names and
                isinstance(item['sets'], list) and bool(item['sets']) and
                all(isinstance(s, str) and s in value['sets'] for s in item['sets']) and
                len(item['sets']) == len(set(item['sets'])), 'INVESTIGATION_PLAN_INVALID')
        names.add(item['id'])
        assigned = sorted({u for name in item['sets'] for u in value['sets'][name]})
        entries.append({**item, 'units': assigned})
        covered.update(assigned)
    require(covered == set(value['units']), 'INVESTIGATION_COVERAGE_INCOMPLETE')
    result = {'schema': 'investigation-plan-v1', 'catalog_sha256': value['sha256'], 'entries': entries}
    return {**result, 'sha256': identity(result)}


def receipt(value, session_id, call_id, units, response_sha256):
    """Construct from a service response, never from model-supplied coverage."""
    check_catalog(value)
    require(all(isinstance(s, str) and s for s in (session_id, call_id, response_sha256)) and
            isinstance(units, list) and len(units) == len(set(units)) and
            set(units) <= set(value['units']), 'INVESTIGATION_RECEIPT_INVALID')
    return {'session_id': session_id, 'call_id': call_id, 'catalog_sha256': value['sha256'],
            'units': sorted(units), 'response_sha256': response_sha256}


def coverage(value, assigned, receipts, audit):
    """Only actual deliveries in the final native context can cover a unit."""
    check_catalog(value)
    require(set(audit) == {'session_id', 'last_compaction', 'deliveries'} and
            type(audit['last_compaction']) is int and audit['last_compaction'] >= -1 and
            isinstance(audit['deliveries'], list), 'INVESTIGATION_RECEIPT_INVALID')
    delivered = {}
    for row in audit['deliveries']:
        require(set(row) == {'call_id', 'response_sha256', 'position'} and
                type(row['position']) is int and row['position'] > audit['last_compaction'] and
                row['call_id'] not in delivered, 'INVESTIGATION_RECEIPT_INVALID')
        delivered[row['call_id']] = row['response_sha256']
    completed = set()
    for row in receipts:
        require(row['session_id'] == audit['session_id'] and row['catalog_sha256'] == value['sha256'] and
                set(row['units']) <= set(value['units']), 'INVESTIGATION_RECEIPT_INVALID')
        if delivered.get(row['call_id']) == row['response_sha256']:
            completed.update(row['units'])
    assigned = set(assigned)
    require(assigned <= set(value['units']), 'INVESTIGATION_PLAN_INVALID')
    return {'completed': sorted(assigned & completed), 'remaining': sorted(assigned - completed),
            'audit_sha256': identity(audit), 'last_compaction': audit['last_compaction']}


def checkpoint(value, entry, submission, receipts, audit, *, maximum_bytes):
    """Typed claims cite frozen evidence; completion is derived by the service."""
    check_catalog(value)
    require(type(maximum_bytes) is int and maximum_bytes > 0 and isinstance(submission, dict) and
            set(submission) == {'claims', 'decisions'} and
            isinstance(submission['claims'], list) and isinstance(submission['decisions'], list),
            'INVESTIGATION_CHECKPOINT_INVALID')
    cov = coverage(value, entry['units'], receipts, audit)
    completed = set(cov['completed']); ids = set()
    reached = {value['units'][u]['evidence_id'] for u in completed}
    delivered={row['call_id']:row['response_sha256'] for row in audit['deliveries']}
    input_spans=[span for receipt in receipts if delivered.get(receipt['call_id'])==receipt['response_sha256']
                 for span in receipt.get('input_spans',[])]
    for claim in submission['claims']:
        operation_contract.check(claim,CLAIM_SCHEMA,code='INVESTIGATION_CHECKPOINT_INVALID',path='claims[]')
        require(
            isinstance(claim['id'], str) and claim['id'] and claim['id'] not in ids and
            isinstance(claim['subject'],str) and claim['subject'].strip() and
            isinstance(claim['statement'], str) and claim['statement'].strip() and
            claim['confidence'] in ('proven', 'inferred', 'unknown') and
            claim['kind'] in ('positive', 'absence', 'unknown') and
            isinstance(claim['citations'], list) and isinstance(claim['contrary'], list) and
            isinstance(claim['searched_sets'], list) and isinstance(claim['unknowns'], str),
            'INVESTIGATION_CHECKPOINT_INVALID')
        for name in ('dependencies','conflicts'):
            require(isinstance(claim.get(name,[]),list) and all(isinstance(ref,dict) and
                set(ref)=={'partition_id','claim_id'} and all(isinstance(v,str) and v for v in ref.values())
                for ref in claim.get(name,[])), 'INVESTIGATION_CHECKPOINT_INVALID')
        ids.add(claim['id'])
        require(bool(claim['citations']) or claim['confidence'] == 'unknown' and claim['unknowns'].strip(),
                'INVESTIGATION_CITATION_INVALID')
        require(claim['kind'] != 'absence' or bool(claim['searched_sets']),
                'INVESTIGATION_COVERAGE_INCOMPLETE')
        for citation in claim['citations'] + claim['contrary']:
            if isinstance(citation,dict) and 'input_id' in citation:
                require(set(citation)=={'input_id','sha256','start','end'} and
                        citation['input_id'] in value['inputs'], 'INVESTIGATION_CITATION_INVALID')
                source=value['inputs'][citation['input_id']]
                require(citation['sha256']==source['sha256'] and
                        type(citation['start']) is int and type(citation['end']) is int and
                        0<=citation['start']<citation['end']<=source['characters'], 'INVESTIGATION_CITATION_INVALID')
                spans=sorted((row['start'],row['end']) for row in input_spans
                    if row['id']==citation['input_id'] and row['sha256']==source['sha256'])
                end=citation['start']
                for lo,hi in spans:
                    if lo<=end:end=max(end,hi)
                require(end>=citation['end'],'INVESTIGATION_CITATION_INVALID')
                continue
            require(isinstance(citation, dict) and set(citation) == {'id', 'sha256'} and
                    citation['id'] in reached and
                    citation['sha256'] == value['evidence'][citation['id']]['content_sha256'],
                    'INVESTIGATION_CITATION_INVALID')
        for name in claim['searched_sets']:
            require(name in value['sets'] and set(value['sets'][name]) <= completed,
                    'INVESTIGATION_COVERAGE_INCOMPLETE')
    for decision in submission['decisions']:
        operation_contract.check(decision,DECISION_SCHEMA,code='INVESTIGATION_CHECKPOINT_INVALID',path='decisions[]')
        require(
                isinstance(decision['statement'], str) and decision['statement'].strip() and
                isinstance(decision['claims'], list) and bool(decision['claims']) and
                set(decision['claims']) <= ids, 'INVESTIGATION_CHECKPOINT_INVALID')
    result = {'schema': 'investigation-checkpoint-v1', 'catalog_sha256': value['sha256'],
              'binding': value['binding'], 'partition_id': entry['id'], 'session_id': audit['session_id'],
              'coverage': cov, 'completion': 'partial' if cov['remaining'] else 'complete', **submission}
    result['sha256'] = identity(result)
    require(len(canonical(handoff(result, value))) <= maximum_bytes, 'INVESTIGATION_CHECKPOINT_TOO_LARGE')
    return result


def handoff(saved, value):
    """Keep the complete membership witness server-side, identified by hash.

    Consumers see claim citations and locators, plus coverage counts and hashes;
    they do not load thousands of receipt IDs as conversational evidence.
    """
    check_catalog(value)
    require(saved['catalog_sha256'] == value['sha256'] and saved['sha256'] ==
            identity({k: v for k, v in saved.items() if k != 'sha256'}), 'INVESTIGATION_CHANGED')
    cited = {c['id'] for claim in saved['claims'] for c in claim['citations'] + claim['contrary'] if 'id' in c}
    sources = {}
    for key in sorted(cited):
        row = value['evidence'][key]
        sources[key] = ({k: row[k] for k in ('kind', 'scope', 'record_id', 'content_sha256')}
            if row['kind'] == 'record' else {'kind': 'ram', 'record_id': row['fact']['record_id'],
                'addresses': row['fact']['addresses'], 'content_sha256': row['content_sha256']})
    cov = saved['coverage']
    return {**{k: saved[k] for k in ('schema', 'sha256', 'catalog_sha256', 'binding', 'partition_id',
                                   'session_id', 'completion', 'claims', 'decisions')},
            'sources': sources, 'coverage': {'completed_count': len(cov['completed']),
                'remaining_count': len(cov['remaining']), 'sha256': identity(cov),
                'last_compaction': cov['last_compaction']}}


def recheck(saved, current, entry, receipts, audit, *, maximum_bytes, allow_partial=False):
    """Consumer admission repeats the check using the finalized session audit."""
    require(saved['sha256'] == identity({k: v for k, v in saved.items() if k != 'sha256'}),
            'INVESTIGATION_CHANGED')
    result = checkpoint(current, entry, {k: saved[k] for k in ('claims', 'decisions')},
                        receipts, audit, maximum_bytes=maximum_bytes)
    # Later ordinary calls may extend the audit without invalidating reads.
    # A later compaction requires a new accepted checkpoint, even after re-reads.
    def comparable(record):
        return {**{k: v for k, v in record.items() if k not in ('sha256', 'coverage')},
                'coverage': {k: v for k, v in record['coverage'].items() if k != 'audit_sha256'}}
    require(comparable(result) == comparable(saved) and (allow_partial or result['completion'] == 'complete'),
            'INVESTIGATION_CHANGED')
    return {'checkpoint_sha256': saved['sha256'], 'catalog_sha256': current['sha256'],
            'audit_sha256': identity(audit), 'completion': result['completion']}
