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
    # Trim the last hunk first, preserving exact locations for document() reads.
    documents=[change for change in result.get('changes',[]) if change.get('kind')=='authored_document']
    while wire_size(result)>BUDGET:
        nonempty=[change for change in documents if change['hunks']]
        if not nonempty:break
        change=nonempty[-1];hunk=change['hunks'][-1]
        sides=[side for side in ('before','after') if hunk[side+'_lines']]
        side=max(sides,key=lambda key:len(json.dumps(hunk[key+'_lines']).encode()))
        if not any(hunk.get(key+'_truncated') for key in ('before','after')):change['omitted_hunks']+=1
        view=change[side]
        if not hunk.get(side+'_truncated'):view['omitted_hunks']+=1
        hunk[side+'_truncated']=True;view['truncated']=True
        hunk[side+'_lines'].pop()
        line=hunk[side+'_line']+len(hunk[side+'_lines'])
        view['first_omitted_line']=min(view['first_omitted_line'] or line,line)
        if not hunk['before_lines'] and not hunk['after_lines']:change['hunks'].pop()
    if wire_size(result)>BUDGET:
        from .service import ServiceError
        raise ServiceError('RESPONSE_TOO_LARGE',**continuation(result))
    return result
