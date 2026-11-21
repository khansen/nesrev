"""Lossless compact transport of the existing native RAM evidence view."""
from collections import Counter
import json

from . import evidence_views, review_pages
from .model import digest
from .producer import require

CONTEXT=('requested_address','requested_declaration_id')
SUMMARY_OMITTED=('preimage','span','cpu_address','output_offset','segment_id')
SUMMARY_DICTIONARIES=('memory_access','category','access','mnemonic')
MAX_ROWS=128
TOOL_HELP=(" Evidence view ram_compact accepts generation and exactly one address or record_id; "
           "use limit=128 for compact pages. Each record is constants plus columns zipped with its row array, "
           "then selection. Fetch view ram_shared with its set_id once per generation, expand its records "
           "the same way and apply the current selection. Both sets are needed for complete evidence; "
           "follow each next_offset until null. Indexed possibilities and unknown indirect destinations "
           "are not proven accesses. The original ram view is unchanged.")


def packed(rows,metadata,offset,limit,decorate=lambda page:page):
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
        trial=decorate({**result,'records':result['records']+[values]})
        if review_pages.wire_size(trial)>review_pages.BUDGET-4096:
            require(bool(result['records']),'RESPONSE_TOO_LARGE');break
        result['records'].append(values)
    end=offset+len(result['records'])
    result['next_offset']=end if end<len(rows) else None
    result=decorate(result)
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


VIEW_ARGUMENTS={'ram_shared':(('set_id',),()),'ram_compact':((),('address','record_id')),
                'ram_summary':((),('address','record_id')),'ram_set':(('address',),())}


def dictionary_rows(rows,fields=SUMMARY_DICTIONARIES):
    values={k:[] for k in fields}
    identities={k:{} for k in fields};selected=[]
    for row in rows:
        projected=dict(row)
        for field in fields:
            value=row[field];key=json.dumps(value,sort_keys=True,separators=(',',':'))
            if key not in identities[field]:
                identities[field][key]=len(values[field]);values[field].append(value)
            projected[field]=identities[field][key]
        selected.append(projected)
    def dictionary(page):
        tables={}
        for field in fields:
            keys=({page['constants'][field]} if field in page['constants'] else
                  {r[page['columns'].index(field)] for r in page['records']}
                  if page['records'] else set())
            tables[field]={str(k):values[field][k] for k in sorted(keys)}
        return {**page,'dictionaries':tables}
    return selected,dictionary


def set_rows(model,addresses):
    require(isinstance(addresses,list) and 0<len(addresses)<=128 and
            all(type(a) is int and 0<=a<=65535 for a in addresses) and
            len(set(addresses))==len(addresses),'EVIDENCE_REQUEST_INVALID')
    combined={};counts={}
    for address in sorted(addresses):
        rows=evidence_views.memory(model,address=address)
        counts[str(address)]=dict(Counter(r['category'] for r in rows))
        for original in rows:
            row={k:v for k,v in original.items() if k not in CONTEXT}
            key=json.dumps(row,sort_keys=True,separators=(',',':'))
            if key not in combined:combined[key]={**row,'addresses':[]}
            combined[key]['addresses'].append(address)
    return list(combined.values()),counts


def query(model,generation,view,offset=0,limit=40,**arguments):
    from .operation_contract import check
    if view in VIEW_ARGUMENTS:check(arguments,VIEW_ARGUMENTS[view],code='EVIDENCE_REQUEST_INVALID',path='evidence.'+view)
    if view=='ram_set':
        rows,counts=set_rows(model,arguments['address'])
        selected,dictionary=dictionary_rows(rows,(*SUMMARY_DICTIONARIES,'addresses'))
        return packed(selected,{'generation':generation,'encoding':'ram-set-columnar-v1',
            'selection':sorted(arguments['address']),
            **({'category_counts_by_address':counts} if offset==0 else {}),
            'total_evidence_records':sum(sum(c.values()) for c in counts.values()),
            'coverage':'Every original RAM evidence fact. Expand constants/columns and page-local dictionaries, then for each address in addresses copy the row without addresses and add requested_address=address and requested_declaration_id=null. Equal facts are stored once with their exact byte membership. Different categories or alias proofs remain separate. Possible indexed and unresolved indirect destinations are not proven accesses. All pages are required; no separate shared-set fetch.'},offset,limit,dictionary)
    if view=='ram_summary':
        require(set(arguments) in ({'address'},{'record_id'}),'EVIDENCE_REQUEST_INVALID')
        rows=evidence_views.memory(model,**arguments)
        values={k:[] for k in SUMMARY_DICTIONARIES}
        identities={k:{} for k in SUMMARY_DICTIONARIES};selected=[]
        for row in rows:
            projected={k:v for k,v in row.items() if k not in SUMMARY_OMITTED}
            for field in SUMMARY_DICTIONARIES:
                value=row[field];key=json.dumps(value,sort_keys=True,separators=(',',':'))
                if key not in identities[field]:
                    identities[field][key]=len(values[field]);values[field].append(value)
                projected[field]=identities[field][key]
            selected.append(projected)
        def dictionary(page):
            tables={}
            for field in SUMMARY_DICTIONARIES:
                keys=({page['constants'][field]} if field in page['constants'] else
                      {r[page['columns'].index(field)] for r in page['records']}
                      if page['records'] else set())
                tables[field]={str(k):values[field][k] for k in sorted(keys)}
            return {**page,'dictionaries':tables}
        return packed(selected,
            {'generation':generation,'encoding':'ram-columnar-summary-v1',
             'category_counts':dict(Counter(r['category'] for r in rows)),
             'total_evidence_records':len(rows),'omitted_fields':list(SUMMARY_OMITTED),
             'coverage':'Every RAM evidence row, including all possible indexed aliases and unresolved indirect destinations. No separate shared-set fetch is needed. Expand constants plus columns zipped with each row, then for each field in dictionaries replace row[field] with dictionaries[field][str(row[field])]. Each page has its own complete dictionaries. This is access evidence, not an edit preimage.',
             'details':'Read navigate records by record_id in this generation for source locations and edit preimages; ram/ram_compact retain the complete original evidence.'},offset,limit,dictionary)
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
