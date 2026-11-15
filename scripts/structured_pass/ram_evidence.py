"""Lossless compact transport of the existing native RAM evidence view."""
from collections import Counter
import json

from . import evidence_views, review_pages
from .model import digest
from .producer import require

CONTEXT=('requested_address','requested_declaration_id')
MAX_ROWS=128
TOOL_HELP=(" Evidence view ram_compact accepts generation and exactly one address or record_id; "
           "use limit=128 for compact pages. Each record is constants plus columns zipped with its row array, "
           "then selection. Fetch view ram_shared with its set_id once per generation, expand its records "
           "the same way and apply the current selection. Both sets are needed for complete evidence; "
           "follow each next_offset until null. Indexed possibilities and unknown indirect destinations "
           "are not proven accesses. The original ram view is unchanged.")


def packed(rows,metadata,offset,limit):
    require(type(offset) is int and offset>=0 and type(limit) is int and 1<=limit<=MAX_ROWS,
            'EVIDENCE_REQUEST_INVALID')
    keys=sorted({key for row in rows for key in row})
    canonical=lambda value:json.dumps(value,sort_keys=True,separators=(',',':'))
    constants={key:rows[0][key] for key in keys
               if all(canonical(row[key])==canonical(rows[0][key]) for row in rows)}
    columns=[key for key in keys if key not in constants]
    result={**metadata,'constants':constants,'columns':columns,'records':[],'offset':offset,
            'total_records':len(rows),'next_offset':None}
    # Leave room for an enclosing transport's generation and continuation fields.
    for row in rows[offset:offset+limit]:
        values=[row[key] for key in columns]
        trial={**result,'records':result['records']+[values]}
        if review_pages.wire_size(trial)>review_pages.BUDGET-4096:
            require(bool(result['records']),'RESPONSE_TOO_LARGE');break
        result['records'].append(values)
    end=offset+len(result['records'])
    result['next_offset']=end if end<len(rows) else None
    require(review_pages.wire_size(result)<=review_pages.BUDGET,'RESPONSE_TOO_LARGE')
    return result


def shared_rows(model):
    # Every indirect destination is unknown for every requested byte. Indexed
    # bases and pointer bytes remain in the per-byte set: their membership varies.
    return [{k:v for k,v in row.items() if k not in CONTEXT}
            for row in evidence_views.memory(model,address=0)
            if row['category']=='unresolved_indirect_destination']


def shared_id(model,generation,rows):
    return 'R-'+digest(json.dumps([generation,digest(model.source),rows],sort_keys=True,
                                  separators=(',',':')).encode())


def query(model,generation,view,offset=0,limit=40,**arguments):
    shared=shared_rows(model);ident=shared_id(model,generation,shared)
    metadata={'generation':generation,'encoding':'ram-columnar-v2'}
    if view=='ram_shared':
        require(set(arguments)=={'set_id'} and arguments['set_id']==ident,'EVIDENCE_REQUEST_INVALID')
        return packed(shared,{**metadata,'set_id':ident},offset,limit)
    require(view=='ram_compact' and set(arguments) in ({'address'},{'record_id'}),'EVIDENCE_REQUEST_INVALID')
    rows=evidence_views.memory(model,**arguments)
    if rows:selection={k:rows[0][k] for k in CONTEXT}
    else:
        # Empty evidence still carries the validated selector; no facts are invented.
        address=arguments.get('address')
        record=arguments.get('record_id')
        if record is not None:
            n=model.node(record)
            address=model.values.get(model.name(n),model.locations.get(n,{}).get('cpu_address'))
        selection={'requested_address':address,'requested_declaration_id':record}
    selected=[{k:v for k,v in row.items() if k not in CONTEXT} for row in rows
              if row['category']!='unresolved_indirect_destination']
    return packed(selected,{**metadata,'selection':selection,
        'category_counts':dict(Counter(r['category'] for r in rows)),
        'total_evidence_records':len(rows),
        'shared':{'set_id':ident,'total_records':len(shared),
                  'view':'ram_shared','context':'Apply selection to shared records too.'}},offset,limit)
