"""Read-only coverage calculation for future agent_review.py verdict history.

This module cannot record or authorize a verdict. The caller must supply history
from the protected handoff state. Hashes check identity, not reviewer authority.
Only receipts and tickets are read; no source state or blob is restored.
"""
import json
from pathlib import Path
import re

from .durable_artifact import canonical,digest,SCHEMAS
from .publication import read_ticket,ticket_path


def require(ok,code):
    if not ok:raise ValueError(code)


def receipt(store,artifact):
    require(isinstance(artifact,str) and re.fullmatch(r'E-[0-9a-f]{64}',artifact),'INVALID_REVIEW_ARTIFACT')
    try:body=json.loads((Path(store)/'artifacts'/artifact/'receipt.json').read_bytes())
    except (OSError,ValueError):raise ValueError('REVIEW_RECEIPT_UNAVAILABLE') from None
    require(isinstance(body,dict) and 'E-'+digest(canonical(body))==artifact,'REVIEW_RECEIPT_CHANGED')
    require(body.get('schema')==SCHEMAS['artifact'],'ARTIFACT_SCHEMA_UNSUPPORTED')
    return body


def pass_edges(store,base,head):
    chain=[];seen=set();current=head;identity=None
    while True:
        require(current not in seen,'REVIEW_CHAIN_CYCLE');seen.add(current)
        body=receipt(store,current)
        scope=(body['source_path'],body['reference_path'],body['reference_sha256'])
        if identity is None:identity=scope
        require(scope==identity,'MIXED_REVIEW_PROJECT')
        chain.append(current)
        if current==base:break
        current=body['base_artifact']
        require(current is not None,'PASS_BASE_NOT_ANCESTOR')
    chain.reverse()
    return [[a,b] for a,b in zip(chain,chain[1:])]


def window(store,head):
    ticket=read_ticket(store,head);items=ticket['artifacts']
    require(len(items)>=2 and len(items)==len(set(items)),'INVALID_REVIEW_WINDOW')
    first=receipt(store,items[0])
    if ticket['schema']=='published-review-v1':
        require(first['base_artifact'] is None,'BASE_ARTIFACT_MISMATCH')
    else:require(ticket['anchor_artifact']==items[0],'BASE_ARTIFACT_MISMATCH')
    edges=pass_edges(store,items[0],head)
    require(edges==[[a,b] for a,b in zip(items,items[1:])],'BASE_ARTIFACT_MISMATCH')
    return {'ticket':head,'ticket_sha256':digest(ticket_path(store,head).read_bytes()),
            'anchor':items[0],'head':head,'edges':edges}


def coverage(store,base,head,history,*,run_id,reviewer):
    """Consume existing-authority history; never infer a verdict from a ticket."""
    require(isinstance(history,list),'INVALID_VERDICT_HISTORY')
    required=pass_edges(store,base,head);known={tuple(edge):None for edge in required}
    for event in history:
        require(isinstance(event,dict),'INVALID_VERDICT_HISTORY')
        require(event.get('run_id')==run_id and event.get('reviewer')==reviewer,'VERDICT_SCOPE_MISMATCH')
        require(event.get('verdict') in ('APPROVED','CHANGES_REQUESTED','WITHDRAWN'),'INVALID_WINDOW_VERDICT')
        expected=window(store,event.get('ticket'))
        require(all(event.get(key)==value for key,value in expected.items()),'VERDICT_WINDOW_MISMATCH')
        require(isinstance(event.get('review_file'),str) and bool(event['review_file']) and
                isinstance(event.get('review_sha256'),str) and re.fullmatch('[0-9a-f]{64}',event['review_sha256'])
                and type(event.get('round')) is int and event['round']>0,'INVALID_VERDICT_HISTORY')
        for edge in expected['edges']:
            require(tuple(edge) in known,'VERDICT_OUTSIDE_PASS')
            known[tuple(edge)]=event['verdict']
    uncovered=[edge for edge in required if known[tuple(edge)]!='APPROVED']
    return {'pass_base':base,'pass_head':head,'required_edges':required,'uncovered_edges':uncovered,
            'coverage_complete':bool(required) and not uncovered,
            'scope':'Coverage only. Verdict authority and file permissions belong to agent_review.py integration.'}
