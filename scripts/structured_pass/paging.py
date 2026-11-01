"""Response ceiling and bounded previews. Reviews page declarations and uses separately.

The bridge also checks serialized MCP bytes so escaping cannot cause a spill.
"""
import json

MAX_BYTES = 24576


def preview_records(details):
    records=[]
    for rename in details['renames']:
        records.append({k:rename[k] for k in ('declaration_id','old_name','new_name')} |
                       {'kind':'rename','use_count':len(rename['uses'])})
        for use in rename['uses']:
            s=use['record']
            records.append({'kind':'bound_use','declaration_id':rename['declaration_id'],
                'reference_id':use['reference_id'],'owner':use['owner'],'record_id':s['record_id'],
                'statement_kind':s['kind'],'mnemonic':s.get('mnemonic'),'span':s['span'],
                'segment_id':s.get('segment_id')})
    for row in details['authored_ledger_rows']:records.append({'kind':'ledger_row','row':row})
    for item in details['authored_documents']:
        # Document text is paginated through document(); preview supplies identity.
        records.append({k:v for k,v in item.items() if k not in ('before','after','before_text','after_text','hunks')} |
                       {'kind':'document'})
    for op in details['comment_dispositions']:records.append(op)
    if details['mixed_documents'] is not None:
        records.append({'kind':'mixed_documents',**details['mixed_documents']})
    for hit in details['q09']['mentions']:records.append({'kind':'prose_sweep','item':hit})
    return records


def page(records,offset=0,limit=12):
    if type(offset) is not int or offset<0 or type(limit) is not int or not 1<=limit<=40:
        raise ValueError('REQUEST_SCHEMA')
    result=[]
    for record in records[offset:offset+limit]:
        # An exceptionally long comment/doc cell must be reduced by the caller;
        # never silently drop it or return a response the client will spill.
        if len(json.dumps(record).encode())>MAX_BYTES-2048:
            raise ValueError('PREVIEW_ITEM_TOO_LARGE')
        if len(json.dumps(result+[record]).encode())>MAX_BYTES-2048:break
        result.append(record)
    end=offset+len(result)
    return {'records':result,'offset':offset,'total_records':len(records),
            'next_offset':end if end<len(records) else None,'max_response_bytes':MAX_BYTES}
