"""Paginated producer records for investigation; never recover facts from asm."""
from bisect import bisect_right

from .model import producer

ERRORS=frozenset(('NAVIGATION_SELECTION_REQUIRED','NAVIGATION_UNKNOWN_SYMBOL',
                  'NAVIGATION_AMBIGUOUS_SYMBOL','NAVIGATION_RECORD_REQUIRED'))


def require(value,code='REQUEST_SCHEMA'):
    if not value:raise ValueError(code)


class Navigation:
    def __init__(self,model):
        self.m=model
        self.statements=sorted((n for n,f in model.facts.items()
            if f['kind'] in producer.CONTEXTS|producer.DECLS|{'END_NODE'}),key=lambda n:model.ranges[n])
        self.position={n:i for i,n in enumerate(self.statements)}
        self.globals=[n for n in self.statements if model.facts[n]['kind']=='LABEL_NODE']
        self.global_offsets=[model.ranges[n][0] for n in self.globals]
        self.layout=model.locations

    def owner(self,n):
        return self.m.owners[n]

    def record(self,n):
        m=self.m;out=m.statement(n);owner=self.owner(n)
        out['lexical_owner_id']=m.ids[owner] if owner is not None else None
        location=self.layout.get(n)
        if location:
            out['layout']={k:location[k] for k in ('segment_id','cpu_address','output_offset','length','bytes')}
        return out

    def select(self,symbol,record_id):
        m=self.m
        require((symbol is None)!=(record_id is None),'NAVIGATION_SELECTION_REQUIRED')
        if record_id is not None:
            require(isinstance(record_id,str) and record_id in m.nodes,'NAVIGATION_RECORD_REQUIRED')
            return m.nodes[record_id]
        require(isinstance(symbol,str) and bool(symbol))
        found=[n for n in self.statements if m.facts[n]['kind'] in producer.DECLS and m.name(n)==symbol]
        require(found,'NAVIGATION_UNKNOWN_SYMBOL')
        require(len(found)==1,'NAVIGATION_AMBIGUOUS_SYMBOL')
        return found[0]

    def query(self,view,*,symbol=None,record_id=None,contains=None,offset=0,limit=12):
        require(view in ('symbols','records','uses','comments'))
        require(type(offset) is int and offset>=0 and type(limit) is int and 1<=limit<=40)
        require(contains is None or isinstance(contains,str) and 0<len(contains)<=256)
        m=self.m;items=[];scope=None;comment_records=[]
        if view=='symbols':
            require(symbol is None and record_id is None)
            selected=[n for n in self.statements if m.facts[n]['kind'] in producer.DECLS
                and (contains is None or contains.casefold() in (m.name(n) or '').casefold())]
            total=len(selected);items=[self.record(n) for n in selected[offset:offset+limit]]
        elif view=='comments':
            require(symbol is None and record_id is None)
            from .rename_service import comments
            selected=[c for c in comments(m) if contains is None or contains.casefold() in c['text'].casefold()]
            total=len(selected);items=selected[offset:offset+limit]
        else:
            require(contains is None)
            n=self.select(symbol,record_id)
            if view=='uses':
                require(m.facts[n]['kind'] in producer.DECLS,'NAVIGATION_RECORD_REQUIRED')
                refs=sorted((r for r,d in m.bindings.items() if d==n),key=lambda r:m.ranges[r])
                total=len(refs)
                items=[{'reference':m.expression(r),'statement':self.record(m.context(r))}
                       for r in refs[offset:offset+limit]]
                scope={'declaration':self.record(n),'coverage':'Every direct producer-bound reference, including data and nested expressions. Fall-through and raw/indirect transfers are not inferred.'}
            else:
                require(n in self.position,'NAVIGATION_RECORD_REQUIRED')
                start=self.position[n]
                # An EQU is one declaration. Label views are explicitly lexical
                # blocks, not a claim that every branch stays inside a procedure.
                end=start+1 if m.facts[n]['kind']=='EQU_NODE' else next(
                    (i for i in range(start+1,len(self.statements))
                     if m.facts[self.statements[i]]['kind'] in ('LABEL_NODE','ORG_NODE','END_NODE')),
                    len(self.statements))
                selected=self.statements[start:end];total=len(selected)
                page=selected[offset:offset+limit]
                items=[self.record(k) for k in page]
                if page:
                    from .rename_service import comments
                    all_comments=comments(m)
                    first=m.facts[page[0]]['span'][0]
                    last=m.facts[page[-1]]['span'][2]
                    # Consecutive comment-only header lines are lexical units.
                    # Do not attach comments across a blank line or code token.
                    if offset==0:
                        comment_lines={c['line'] for c in all_comments}
                        code_lines={u['line'] for u in m.units if u['kind'] not in ('comment','whitespace','newline')}
                        while first-1 in comment_lines and first-1 not in code_lines:first-=1
                    comment_records=[c for c in all_comments if first<=c['line']<=last]
                scope={'start_record_id':m.ids[n],'next_record_id':m.ids[self.statements[end]] if end<len(self.statements) else None,
                       'coverage':'Lexical statements through the next global label or segment boundary; follow bound references or next_record_id to continue.'}
        return {'view':view,'offset':offset,'limit':limit,'total':total,'records':items,
                'next_offset':offset+limit if offset+limit<total else None,'scope':scope,
                'comments':comment_records}
