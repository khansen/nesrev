"""Paginated producer records for investigation; never recover facts from asm."""
from bisect import bisect_right
import json

from .model import producer

ERRORS=frozenset(('NAVIGATION_SELECTION_REQUIRED','NAVIGATION_UNKNOWN_SYMBOL',
                  'NAVIGATION_AMBIGUOUS_SYMBOL','NAVIGATION_RECORD_REQUIRED'))


def require(value,code='REQUEST_SCHEMA'):
    if not value:raise ValueError(code)


VIEWS=('symbols','records','records_compact','source','uses','comments')
SPANS=('label','segment')
SOURCE_COLUMNS=('record_id','address','label','text')
SOURCE_LIMIT=128
LAYOUT_FIELDS=('cpu_address','output_offset','bytes','segment_id')
COMPACT_HELP=('Each row starts with a schema index. Combine constants with '
    'zip(schemas[row[0]], row[1:]). If layout is present, its value is length; '
    'restore layout with that length and the top-level cpu_address, output_offset, '
    'bytes and segment_id. Every field and preimage is retained. Each page decodes independently.')


def compact_records(page):
    rows=[]
    for original in page['records']:
        row=dict(original)
        if 'layout' in row:
            require(set(row['layout'])==set(LAYOUT_FIELDS)|{'length'} and
                    all(key in row and row[key]==row['layout'][key] for key in LAYOUT_FIELDS),
                    'SOURCE_MODEL_JOIN')
            row['layout']=row['layout']['length']
        rows.append(row)
    keys=set.intersection(*(set(row) for row in rows)) if rows else set()
    canonical=lambda value:json.dumps(value,sort_keys=True,separators=(',',':'))
    constants={key:rows[0][key] for key in sorted(keys)
               if all(canonical(row[key])==canonical(rows[0][key]) for row in rows)}
    schemas=[];records=[]
    for row in rows:
        fields=sorted(set(row)-set(constants))
        if fields not in schemas:schemas.append(fields)
        records.append([schemas.index(fields),*[row[key] for key in fields]])
    return {**page,'view':'records_compact','encoding':'source-records-columnar-v1',
            'constants':constants,'schemas':schemas,'records':records,'decode':COMPACT_HELP}


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

    def query(self,view,*,symbol=None,record_id=None,contains=None,offset=0,limit=12,span='label'):
        if view not in VIEWS:
            from .operation_contract import RequestError
            raise RequestError(field='view',accepted_values=list(VIEWS))
        if view=='source':
            require(contains is None)
            return self.source(symbol,record_id,offset,limit,span)
        compact=view=='records_compact'
        if compact:view='records'
        require(type(offset) is int and offset>=0 and type(limit) is int and 1<=limit<=40)
        require(contains is None or isinstance(contains,str) and 0<len(contains)<=256)
        if span not in SPANS or (view!='records' and span!='label'):
            from .operation_contract import RequestError
            raise RequestError(field='span',accepted_values=list(SPANS) if view=='records' else ['label'])
        if view=='records' and span=='segment':
            require(contains is None)
            return self.segment_records(self.select(symbol,record_id),offset,limit,compact=compact)
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
                    if compact and offset:first=m.facts[selected[offset-1]]['span'][2]+1
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
        answer={'view':view,'offset':offset,'limit':limit,'total':total,'records':items,
                'next_offset':offset+limit if offset+limit<total else None,'scope':scope,
                'comments':comment_records}
        if not compact:return answer
        from . import review_pages
        while True:
            result=compact_records(answer)
            if review_pages.wire_size(result)<=review_pages.BUDGET-4096:return result
            require(len(answer['records'])>1,'RESPONSE_TOO_LARGE')
            answer['records'].pop()
            answer['next_offset']=offset+len(answer['records'])
            last=answer['records'][-1]['span'][2]
            answer['comments']=[c for c in answer['comments'] if c['line']<=last]

    def segment_records(self,n,offset,limit,compact=False):
        """A lexical span, not a procedure or control-flow completeness claim."""
        from . import review_pages
        from .rename_service import comments
        m=self.m
        require(n in self.position,'NAVIGATION_RECORD_REQUIRED')
        start=self.position[n]
        segment=self.layout.get(n,{}).get('segment_id')
        if m.facts[n]['kind'] in ('EQU_NODE','ORG_NODE','END_NODE'):
            end=start+1
        else:
            end=next((i for i in range(start+1,len(self.statements))
                if m.facts[self.statements[i]]['kind'] in ('ORG_NODE','END_NODE') or
                (self.statements[i] in self.layout and
                 self.layout[self.statements[i]]['segment_id']!=segment)),len(self.statements))
        selected=self.statements[start:end]
        page=selected[offset:offset+limit]
        all_comments=comments(m)
        first=m.facts[page[0]]['span'][0] if page else 0
        if page and offset:
            first=m.facts[selected[offset-1]]['span'][2]+1
        elif page:
            comment_lines={c['line'] for c in all_comments}
            code_lines={u['line'] for u in m.units if u['kind'] not in ('comment','whitespace','newline')}
            while first-1 in comment_lines and first-1 not in code_lines:first-=1
        result={'view':'records','span':'segment','offset':offset,'limit':limit,'total':len(selected),
                'scope':{'start_record_id':m.ids[n],'segment_id':segment,
                         'boundary_record_id':m.ids[self.statements[end]] if end<len(self.statements) else None,
                         'coverage':'Lexical statements across global labels in one segment; stops before ORG/END or a segment change. Not control-flow proof. EQU/ORG/END selections are single records.'}}
        while True:
            following=offset+len(page)
            next_offset=following if following<len(selected) else None
            answer={**result,'records':[self.record(k) for k in page],
                    'next_offset':next_offset,
                    'next_record_id':m.ids[selected[following]] if next_offset is not None else None,
                    'comments':[c for c in all_comments if page and first<=c['line']<=m.facts[page[-1]]['span'][2]]}
            if compact:answer=compact_records(answer)
            # Reserve the same envelope headroom as other evidence views. Shrink
            # whole records only; an oversized single record is refused intact.
            if review_pages.wire_size(answer)<=review_pages.BUDGET-4096:return answer
            require(len(page)>1,'RESPONSE_TOO_LARGE')
            page.pop()

    def selection(self,n,span):
        """Shared lexical bounds for preparation and the reading projection."""
        require(n in self.position,'NAVIGATION_RECORD_REQUIRED')
        start=self.position[n];m=self.m;segment=self.layout.get(n,{}).get('segment_id')
        if m.facts[n]['kind'] in ('EQU_NODE','ORG_NODE','END_NODE'):return [n]
        end=next((i for i in range(start+1,len(self.statements))
            if m.facts[self.statements[i]]['kind'] in ('ORG_NODE','END_NODE') or
            (self.statements[i] in self.layout and
             self.layout[self.statements[i]]['segment_id']!=segment) or
            (span=='label' and m.facts[self.statements[i]]['kind']=='LABEL_NODE')),
            len(self.statements))
        return self.statements[start:end]

    def source(self,symbol,record_id,offset,limit,span):
        """Exact producer source spans, without an editing record's metadata."""
        from . import review_pages
        from .rename_service import comments
        require(type(offset) is int and offset>=0 and type(limit) is int and 1<=limit<=SOURCE_LIMIT)
        require(span in SPANS)
        if isinstance(record_id,list):
            require(symbol is None and span=='label' and 0<len(record_id)<=128)
            require(all(isinstance(value,str) for value in record_id) and
                    len(set(record_id))==len(record_id))
            roots=[self.select(None,value) for value in record_id]
        else:roots=[self.select(symbol,record_id)]
        m=self.m;blocks=[self.selection(n,span) for n in roots]
        selected=sorted({n for block in blocks for n in block},key=lambda n:m.ranges[n])
        all_comments=comments(m)
        # Bind each comment to its following statement (or the final statement
        # on its own line). This retains gaps once, even for overlapping blocks.
        attached={n:[] for n in selected};seen=set()
        code_lines={u['line'] for u in m.units if u['kind'] not in ('comment','whitespace','newline')}
        comment_lines={c['line'] for c in all_comments}
        for block in blocks:
            first=m.facts[block[0]]['span'][0]
            while first-1 in comment_lines and first-1 not in code_lines:first-=1
            for n in block:
                last=m.facts[n]['span'][2]
                for i,c in enumerate(all_comments):
                    if i not in seen and first<=c['line']<=last:
                        attached[n].append(c);seen.add(i)
                first=last+1
        page=selected[offset:offset+limit]
        while True:
            end=offset+len(page);following=selected[end] if end<len(selected) else None
            answer={'view':'source','encoding':'source-text-v1','columns':list(SOURCE_COLUMNS),
                'span':span,'offset':offset,'limit':limit,'total':len(selected),
                'records':[[m.ids[n],self.layout.get(n,{}).get('cpu_address'),
                            m.name(n),m.source[slice(*m.ranges[n])].decode('utf-8')]
                           for n in page],
                'comments':[c for n in page for c in attached[n]],
                'next_offset':end if following is not None else None,
                'next_record_id':m.ids[following] if following is not None else None,
                'coverage':'Exact source at producer spans, in lexical order. No control-flow or ownership proof. Fetch records by record_id in this generation for editing metadata and preimages.'}
            if review_pages.wire_size(answer)<=review_pages.BUDGET-4096:return answer
            require(len(page)>1,'RESPONSE_TOO_LARGE');page.pop()
