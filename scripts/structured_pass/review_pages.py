"""Bound review views without dropping changed records or their identities."""
import json
from . import paging

# Leave room for retained-session evidence, window metadata and the request ID.
BUDGET = paging.MAX_BYTES - 2048


def wire_size(value):
    content={'content':[{'type':'text','text':json.dumps(value)}]}
    return len(json.dumps({'jsonrpc':'2.0','id':0,'result':content}).encode())+1


def continuation(result):
    return {key:result[key] for key in ('offset','total_changes','next_offset','total_pages')
            if key in result and (result[key] is None or type(result[key]) is int)}


def ledger_pages(rows):
    """At most 16 rows, with byte headroom for identities and review metadata."""
    offset=0
    while offset<len(rows):
        chunk=[]
        for row in rows[offset:offset+16]:
            if chunk and wire_size({'added_rows':chunk+[row]})>BUDGET-8192:break
            chunk.append(row)
        yield offset,chunk
        offset+=len(chunk)


def fit(result):
    """Optional context/excerpts may shrink; assembler facts never do."""
    if wire_size(result)<=BUDGET:return result
    for change in result.get('changes',[]):
        omitted=False
        for key in ('before','after'):
            view=change.get(key)
            if isinstance(view,dict) and 'record' in view:
                omitted |= bool(view.get('before') or view.get('after'))
                view.pop('before',None);view.pop('after',None)
        if omitted:change['neighbors_omitted']=True
    if wire_size(result)<=BUDGET:return result
    # Remove whole lines from the larger document side until the encoded page
    # fits. Hashes, total line counts, path, reason and the comparison remain.
    excerpts=[change[key] for change in result.get('changes',[]) if change.get('kind')=='authored_document'
              for key in ('before','after') if change.get(key) is not None]
    while wire_size(result)>BUDGET:
        nonempty=[view for view in excerpts if view['lines']]
        if not nonempty:break
        largest=max(nonempty,key=lambda view:len(json.dumps(view['lines']).encode()))
        largest['lines'].pop();largest['truncated']=True
    if wire_size(result)>BUDGET:
        from .service import ServiceError
        raise ServiceError('RESPONSE_TOO_LARGE',**continuation(result))
    return result
