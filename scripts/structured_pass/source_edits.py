"""Typed source operations; xasm alone parses, binds, evaluates and lays out them.

Copied operand identities are carried by byte ranges, never inferred from equal
values. A request expresses intent; certification must independently confirm it.
"""
import json
import re

from .model import digest, translated
from .producer import require, CONTEXTS, DECLS

KINDS = frozenset(('declare', 'replace_expression', 'delete_declaration',
                   'localize', 'reflow_data', 'unit_replace', 'comment_insert'))
ERRORS = frozenset(('SOURCE_EDIT_SCHEMA', 'SOURCE_EDIT_PREIMAGE', 'SOURCE_EDIT_BOUNDARY',
    'SOURCE_EDIT_BINDING', 'SOURCE_EDIT_LAYOUT', 'SOURCE_EDIT_IDENTITY',
    'SOURCE_EDIT_SCOPE', 'SOURCE_EDIT_LIVE_DECLARATION', 'SOURCE_EDIT_OVERLAP','SOURCE_EDIT_EXPRESSION'))


def shape(op, fields):
    require(set(op)==set(fields.split())|{'kind','reason'}, 'SOURCE_EDIT_SCHEMA')
    require(isinstance(op['reason'],str) and 0<len(op['reason'].strip())<=2000, 'SOURCE_EDIT_SCHEMA')


def selected(model, ident, preimage):
    n=model.node(ident); lo,hi=model.ranges[n]
    require(digest(model.source[lo:hi])==preimage, 'SOURCE_EDIT_PREIMAGE')
    return n


def declaration_anchor(model, node):
    """Keep leading native comment units attached to the selected statement."""
    start, _ = model.ranges[node]
    require(start == 0 or model.source[start-1:start] == b'\n', 'SOURCE_EDIT_BOUNDARY')
    leading = []
    for unit in reversed(model.units):
        if unit['byte_start'] >= start:
            continue
        if unit['kind'] not in ('comment', 'whitespace', 'newline'):
            break
        require(unit['byte_end_exclusive'] <= start, 'SOURCE_EDIT_BOUNDARY')
        leading.append(unit)
    for unit in reversed(leading):
        if unit['kind'] != 'comment':
            continue
        line = model.source.rfind(b'\n', 0, unit['byte_start']) + 1
        # A preceding statement's inline comment belongs to that statement.
        if not model.source[line:unit['byte_start']].strip(b' \t'):
            return line
    return start


def descendants(model, n):
    return [n]+[child for c in model.children[n] for child in descendants(model,c)]


def boundary_header(boundary):
    lines=boundary.get('header',[])
    require(isinstance(lines,list) and len(lines)<=16 and
            all(isinstance(line,str) and line.startswith(';') and
                not any(c in line for c in '\r\n\x00') for line in lines), 'SOURCE_EDIT_SCHEMA')
    text='\n'.join(lines).encode()
    require(len(text)<=4096,'SOURCE_EDIT_SCHEMA')
    return text+b'\n' if lines else b''


def operand_spelling(model,node,format_,width):
    if format_ is None:
        return model.source[slice(*model.ranges[node])]
    require(format_ in ('decimal','hex','binary'),'SOURCE_EDIT_SCHEMA')
    expression=model.expression_records[node]
    require(expression['kind']=='integer' and not expression['children'] and
            type(expression['value']) is int and 0<=expression['value']<1<<(8*width),
            'SOURCE_EDIT_EXPRESSION')
    value=expression['value']
    if format_=='decimal':return str(value).encode()
    if format_=='hex':return ('$'+format(value,'0'+str(2*width)+'X')).encode()
    return ('%'+format(value,'0'+str(8*width)+'b')).encode()


def typed_expression(model, value, additions, depth=0):
    require(depth<32 and isinstance(value,dict), 'SOURCE_EDIT_SCHEMA')
    if set(value) in ({'integer'},{'integer','format'}):
        v=value['integer'];require(type(v) is int and -(2**31)<=v<2**31,'SOURCE_EDIT_SCHEMA')
        format_=value.get('format','decimal')
        require(format_ in ('decimal','hex','binary') and (v>=0 or format_=='decimal'),'SOURCE_EDIT_SCHEMA')
        if format_=='hex':return ('$'+format(v,'X')).encode(), []
        if format_=='binary':return ('%'+format(v,'b')).encode(), []
        return str(v).encode(), []
    if set(value)=={'declaration_id'}:
        ident=value['declaration_id']
        if ident in additions:name=additions[ident]
        else:
            n=model.node(ident);require(n in model.declaration_records,'SOURCE_EDIT_BINDING')
            name=model.name(n)
            require(model.declaration_records[n]['kind'] in ('global','equ','local'),'SOURCE_EDIT_BINDING')
        return name.encode(), [ident]
    if set(value)=={'operator','operands'}:
        op=value['operator']; args=value['operands']
        require(isinstance(args,list) and (op in ('-','~','<','>') and len(args)==1
                or op in ('+','-','*','/','%','<<','>>','&','|','^') and len(args)==2), 'SOURCE_EDIT_SCHEMA')
        parts=[typed_expression(model,a,additions,depth+1) for a in args]
        right=(parts[1][0] if len(args)==2 and set(args[1])=={'integer'} and args[1]['integer']>=0 else
               b'('+parts[1][0]+b')' if len(args)==2 else b'')
        text=(op.encode()+b'('+parts[0][0]+b')' if len(parts)==1 else
              b'('+parts[0][0]+b')'+op.encode()+right)
        require(len(text)<=4096,'SOURCE_EDIT_SCHEMA')
        return text,[ref for _,refs in parts for ref in refs]
    raise ValueError('SOURCE_EDIT_SCHEMA')


def localization_scopes(model, operations):
    requests={}
    for op in operations:
        if op['kind']!='localize':continue
        shape(op,'declaration_id preimage scope_id new_name')
        n=selected(model,op['declaration_id'],op['preimage']);owner=model.node(op['scope_id'])
        require(model.declaration_records.get(n,{}).get('kind')=='global'
                and model.declaration_records.get(owner,{}).get('kind')=='global'
                and n not in requests,'SOURCE_EDIT_SCOPE')
        require(isinstance(op['new_name'],str) and re.fullmatch('@@[a-z][A-Za-z0-9]*',op['new_name']), 'SOURCE_EDIT_SCHEMA')
        requests[n]=(owner,op['new_name'])
    if not requests:return {}
    globals_=sorted((n for n,r in model.declaration_records.items() if r['kind']=='global'),key=lambda n:model.ranges[n])
    positions={n:i for i,n in enumerate(globals_)};result={}
    for n,(owner,name) in requests.items():
        a,b=positions[owner],positions[n]
        require(owner not in requests and a<b and
                all(requests.get(d,(None,None))[0]==owner for d in globals_[a+1:b+1]),'SOURCE_EDIT_SCOPE')
        following=next((d for d in globals_[b+1:] if requests.get(d,(None,None))[0]!=owner),None)
        start=model.ranges[owner][0];end=model.ranges[following][0] if following else len(model.source)
        refs=[r for r,d in model.bindings.items() if d==n]
        require(refs and all(start<=model.ranges[r][0]<end and
                model.context(r) in model.instructions and model.instructions[model.context(r)]['mnemonic'] not in ('JSR','JMP')
                for r in refs),'SOURCE_EDIT_SCOPE')
        names=[new for target,new in requests.values() if target==owner]
        names.extend(r['name'] for d,r in model.declaration_records.items()
                     if r['kind']=='local' and start<=model.ranges[d][0]<end)
        require(len(set(names))==len(names),'SOURCE_EDIT_SCOPE')
        result[n]=(owner,refs)
    return result


def plan(model, operations):
    ops=[op for op in operations if op.get('kind') in KINDS]
    require(len(ops)<=256,'SOURCE_EDIT_SCHEMA')
    additions={}
    for op in ops:
        names=[op.get('name')] if op['kind']=='declare' else []
        if op['kind']=='reflow_data' and 'boundaries' in op:
            require(isinstance(op['boundaries'],list),'SOURCE_EDIT_SCHEMA')
            for boundary in op['boundaries']:
                require(isinstance(boundary,dict) and set(boundary) in
                        ({'operand_id','name'},{'operand_id','name','header'}),'SOURCE_EDIT_SCHEMA')
                boundary_header(boundary)
                names.append(boundary['name'])
        for name in names:
            require(isinstance(name,str) and re.fullmatch('[A-Za-z_][A-Za-z0-9_]*',name)
                    and name not in model.declarations and 'new:'+name not in additions,'SOURCE_EDIT_SCHEMA')
            additions['new:'+name]=name
    scopes=localization_scopes(model,ops)
    edits=[]; copies=[]; removed=set(); replaced=set(); intents=[]; localized=set(); insertions={}
    deleted=set();cleared=[]
    # Resolve explicit removals before checking gaps between data records.
    for op in sorted(ops,key=lambda op:op['kind']=='reflow_data'):
        kind=op['kind']
        if kind=='declare':
            fields='anchor_id preimage name declaration_kind'
            if op.get('declaration_kind')=='equ':fields+=' expression'
            shape(op,fields)
            n=selected(model,op['anchor_id'],op['preimage'])
            require(model.facts[n]['kind'] in CONTEXTS|{'LABEL_NODE','LOCAL_LABEL_NODE','END_NODE'},'SOURCE_EDIT_BOUNDARY')
            require(op['declaration_kind'] in ('equ','label'),'SOURCE_EDIT_SCHEMA')
            lo=declaration_anchor(model,n)
            refs=[]
            if op['declaration_kind']=='equ':
                value,refs=typed_expression(model,op['expression'],additions)
                text=op['name'].encode()+b' .EQU '+value+b'\n'
            else:text=op['name'].encode()+b':\n'
            insertions.setdefault(lo,[]).append(text);intents.append(('declare',op['name'],refs))
        elif kind=='replace_expression':
            shape(op,'expression_id preimage expression')
            n=selected(model,op['expression_id'],op['preimage'])
            require(n in model.expression_records,'SOURCE_EDIT_BOUNDARY')
            text,refs=typed_expression(model,op['expression'],additions)
            edits.append((*model.ranges[n],text));replaced.update(descendants(model,n))
            intents.append(('expression',n,refs))
        elif kind=='delete_declaration':
            shape(op,'declaration_id preimage')
            n=selected(model,op['declaration_id'],op['preimage'])
            require(n in model.declaration_records and model.declaration_records[n]['kind'] in ('equ','global','local'), 'SOURCE_EDIT_BOUNDARY')
            edit=(*model.ranges[n],b'');edits.append(edit);cleared.append(edit)
            removed.update(descendants(model,n));deleted.add(n)
        elif kind=='localize':
            n=model.node(op['declaration_id']);owner,refs=scopes[n]
            span=model.declaration_records[n]['name_span']
            edits.append((span['byte_start'],span['byte_end_exclusive'],op['new_name'].encode()))
            edits.extend((*model.ranges[r],op['new_name'].encode()) for r in refs)
            localized.update([n,*refs]);intents.append(('localize',n,owner))
        elif kind=='unit_replace':
            shape(op,'unit_id preimage text')
            require(isinstance(op['unit_id'],str) and re.fullmatch('u[0-9]+',op['unit_id']), 'SOURCE_EDIT_SCHEMA')
            i=int(op['unit_id'][1:]);require(i<len(model.units),'SOURCE_EDIT_BOUNDARY')
            unit=model.units[i];text=op['text']
            require(digest(bytes.fromhex(unit['hex']))==op['preimage'],'SOURCE_EDIT_PREIMAGE')
            require(isinstance(text,str) and len(text.encode())<=4096,'SOURCE_EDIT_SCHEMA')
            require(unit['kind']=='comment' and (text=='' or text.startswith(';') and not any(c in text for c in '\r\n\x00'))
                    or unit['kind']=='whitespace' and all(c in ' \t' for c in text)
                    or unit['kind']=='newline' and all(c in ' \t\n' for c in text),'SOURCE_EDIT_BOUNDARY')
            edit=(unit['byte_start'],unit['byte_end_exclusive'],text.encode());edits.append(edit)
            if text=='':cleared.append(edit)
        elif kind=='comment_insert':
            shape(op,'anchor_id preimage text'+(' position' if 'position' in op else ''))
            n=selected(model,op['anchor_id'],op['preimage']);lo,hi=model.ranges[n]
            require(model.facts[n]['kind'] in CONTEXTS|{'LABEL_NODE','LOCAL_LABEL_NODE','END_NODE'}, 'SOURCE_EDIT_BOUNDARY')
            text=op['text'];require(isinstance(text,str) and text.startswith(';') and len(text.encode())<=4096
                                  and not any(c in text for c in '\r\n\x00'),'SOURCE_EDIT_SCHEMA')
            position=op.get('position','header');require(position in ('header','inline'),'SOURCE_EDIT_SCHEMA')
            if position=='header':
                require(lo==0 or model.source[lo-1:lo]==b'\n','SOURCE_EDIT_BOUNDARY')
                edits.append((lo,lo,text.encode()+b'\n'))
            else:
                tail=model.source[hi:].split(b'\n',1)[0]
                require(tail.strip(b' \t')==b'','SOURCE_EDIT_BOUNDARY')
                edits.append((hi,hi,b' '+text.encode()))
        elif kind=='reflow_data':
            shape(op,'record_ids preimages groups'+(' boundaries' if 'boundaries' in op else '')+
                  (' formats' if 'formats' in op else '')+
                  (' continuation_indent' if 'continuation_indent' in op else ''))
            indent=op.get('continuation_indent','')
            require(isinstance(indent,str) and len(indent)<=16 and all(c in ' \t' for c in indent),'SOURCE_EDIT_SCHEMA')
            ids=op['record_ids'];groups=op['groups']
            require(isinstance(ids,list) and 1<=len(ids)<=128 and len(set(ids))==len(ids)
                    and isinstance(op['preimages'],list) and len(ids)==len(op['preimages'])
                    and isinstance(groups,list) and groups and all(isinstance(g,list) and g for g in groups),'SOURCE_EDIT_SCHEMA')
            nodes=[selected(model,i,h) for i,h in zip(ids,op['preimages'])]
            data={r['syntax_id']:r for r in model.document['data']}
            require(all(n in data for n in nodes),'SOURCE_EDIT_BOUNDARY')
            require(nodes==sorted(nodes,key=lambda n:model.ranges[n]),'SOURCE_EDIT_IDENTITY')
            widths={data[n]['element_width'] for n in nodes}
            require(len(widths)==1,'SOURCE_EDIT_BOUNDARY')
            operands=[model.node(model.ids[next(e for e,r in model.expression_records.items() if r['id']==o['expression_id'])])
                      for n in nodes for o in data[n]['operands']]
            require([i for g in groups for i in g]==[model.ids[n] for n in operands],'SOURCE_EDIT_IDENTITY')
            formats=op.get('formats',{})
            require(isinstance(formats,dict) and set(formats)<={model.ids[n] for n in operands}
                    and all(isinstance(f,str) and f in ('decimal','hex','binary') for f in formats.values()),
                    'SOURCE_EDIT_SCHEMA')
            locs=[model.locations[n] for n in nodes]
            require(len({l['segment_id'] for l in locs})==1 and all(a['output_offset']+a['length']==b['output_offset']
                    for a,b in zip(locs,locs[1:])),'SOURCE_EDIT_LAYOUT')
            lo=model.ranges[nodes[0]][0];hi=model.ranges[nodes[-1]][1]
            for a,b in zip(nodes,nodes[1:]):
                start,end=model.ranges[a][1],model.ranges[b][0];gap=model.source[start:end]
                for x,y,_ in sorted(cleared,reverse=True):
                    if start<=x<=y<=end:gap=gap[:x-start]+gap[y-start:]
                require(gap.strip(b' \t\r\n')==b'','SOURCE_EDIT_BOUNDARY')
            cleared_ranges={(a,b) for a,b,_ in cleared}
            require(all((u['byte_start'],u['byte_end_exclusive']) in cleared_ranges
                        for u in model.units if u['kind']=='comment' and lo<=u['byte_start']<hi),'SOURCE_EDIT_BOUNDARY')
            text=b'';directive=b'.DB ' if next(iter(widths))==1 else b'.DW '
            boundaries={b['operand_id']:b for b in op.get('boundaries',[])}
            require(len(boundaries)==len(op.get('boundaries',[])) and set(boundaries)<={g[0] for g in groups},'SOURCE_EDIT_BOUNDARY')
            for group in groups:
                if text:text+=b'\n'+indent.encode()
                if group[0] in boundaries:
                    boundary=boundaries[group[0]];name=boundary['name'];header=boundary_header(boundary)
                    if text and header:text+=b'\n'
                    text+=header+name.encode()+b':\n'
                    intents.append(('declare',name,[]))
                text+=directive
                for j,ident in enumerate(group):
                    if j:text+=b','
                    operand=model.node(ident);a,b=model.ranges[operand]
                    piece=operand_spelling(model,operand,formats.get(ident),next(iter(widths)))
                    copies.append((operand,lo,len(text),len(piece)))
                    text+=piece
            edits=[edit for edit in edits if not(edit in cleared and lo<=edit[0]<=edit[1]<=hi)]
            edits.append((lo,hi,text))
            removed.update(nodes)
    require(all(r in removed|replaced for r,d in model.bindings.items() if d in deleted),'SOURCE_EDIT_LIVE_DECLARATION')
    edits.extend((lo,lo,b''.join(parts)) for lo,parts in insertions.items())
    edits.sort()
    require(all(a[1]<=b[0] and not (a[0]==a[1]==b[0]) for a,b in zip(edits,edits[1:])), 'SOURCE_EDIT_OVERLAP')
    return {'edits':edits,'copies':copies,'removed':removed,'replaced':replaced,
            'intents':intents,'localized':localized,'additions':additions}


def reconcile(base, changed, operations, edits):
    p=plan(base,operations);by_span={}
    for n,(lo,hi) in changed.ranges.items():by_span.setdefault((lo,hi),[]).append(n)
    def relocate(n,lo,hi,kinds):
        candidates=[c for c in by_span.get((lo,hi),[]) if changed.facts[c]['kind'] in kinds]
        require(len(candidates)==1,'SOURCE_EDIT_IDENTITY')
        changed.ids[candidates[0]]=base.ids[n]
    for n in p['localized']:
        lo,hi=base.ranges[n]
        relocate(n,translated(lo,edits,True),translated(hi,edits,False),
                 {'LOCAL_LABEL_NODE'} if n in base.declaration_records else {'LOCAL_ID_NODE'})
    for operand,start,offset,length in p['copies']:
        dest=translated(start,edits,False)+offset
        for n in descendants(base,operand):
            lo,hi=base.ranges[n];old=base.ranges[operand][0]
            relocate(n,dest+lo-old,dest+length if n==operand else dest+hi-old,{base.facts[n]['kind']})
    require(len(set(changed.ids.values()))==len(changed.ids),'SOURCE_EDIT_IDENTITY')
    changed.nodes={i:n for n,i in changed.ids.items()}
    for kind,n,refs in p['intents']:
        if kind=='localize':
            require(changed.owners[changed.node(base.ids[n])]==changed.node(base.ids[refs]),'SOURCE_EDIT_SCOPE')
            requested=next(op['new_name'] for op in operations if op['kind']=='localize' and op['declaration_id']==base.ids[n])
            require(changed.name(changed.node(base.ids[n]))==requested and
                    all(changed.name(changed.node(base.ids[r]))==requested for r,d in base.bindings.items() if d==n),
                    'SOURCE_EDIT_IDENTITY')
            continue
        if kind=='declare':
            new=changed.declarations[n]
            require(changed.ids[new] not in base.nodes,'SOURCE_EDIT_IDENTITY')
        else:
            lo,hi=base.ranges[n];a=translated(lo,edits,True);b=translated(hi,edits,False)
            candidates=[c for c in by_span.get((a,b),[]) if c in changed.expression_records]
            require(len(candidates)==1,'SOURCE_EDIT_IDENTITY');new=candidates[0]
        actual=[changed.ids[changed.bindings[r]] for r in sorted(descendants(changed,new),key=lambda r:changed.ranges[r]) if r in changed.bindings]
        expected=[changed.ids[changed.declarations[p['additions'][i]]] if i in p['additions'] else i for i in refs]
        require(actual==expected,'SOURCE_EDIT_BINDING')
        request=next((op['expression'] for op in operations if
            kind=='declare' and op['kind']=='declare' and op['name']==n and 'expression' in op or
            kind=='expression' and op['kind']=='replace_expression' and op['expression_id']==base.ids[n]),None)
        if request is not None:
            root=new
            if kind=='declare':
                eid=changed.declaration_records[new]['expression_id']
                root=next(node for node,e in changed.expression_records.items() if e['id']==eid)
            verify_expression(changed,root,request,p['additions'])
    for n,loc in base.instructions.items():
        other=changed.instructions.get(changed.nodes.get(base.ids[n]))
        require(other is not None and all(other[k]==loc[k] for k in ('segment_id','output_offset','cpu_address','bytes','final_mode')), 'SOURCE_EDIT_LAYOUT')
    for n,fact in base.facts.items():
        if fact['kind'] in CONTEXTS|DECLS|{'END_NODE'} and n not in p['removed']:
            require(base.ids[n] in changed.nodes,'SOURCE_EDIT_IDENTITY')
    for n,loc in base.locations.items():
        if n in p['removed']:continue
        other=changed.locations.get(changed.nodes.get(base.ids[n]))
        require(other is not None and all(other[k]==loc[k] for k in
                ('segment_id','cpu_address','output_offset','byte_length')), 'SOURCE_EDIT_LAYOUT')
    def segments(model):
        return [{**segment,'start_syntax_id':model.ids[segment['start_syntax_id']] if segment['start_syntax_id'] else None}
                for segment in model.document['segments']]
    require(segments(base)==segments(changed),'SOURCE_EDIT_LAYOUT')
    def operands(model):
        return {o['expression_id']:(o['output_offset'],o['byte_length'],o['element_count'],d['element_width'],
                 model.locations[d['syntax_id']]['segment_id']) for d in model.document['data'] for o in d['operands']}
    old_data=operands(base);new_data=operands(changed)
    for operand,_,_,_ in p['copies']:
        n=changed.node(base.ids[operand])
        require(old_data[base.expression_records[operand]['id']]==new_data[changed.expression_records[n]['id']], 'SOURCE_EDIT_LAYOUT')
        if base.expression_records[operand]['kind']=='integer':
            require(changed.expression_records[n]['kind']=='integer' and
                    changed.expression_records[n]['value']==base.expression_records[operand]['value'],
                    'SOURCE_EDIT_EXPRESSION')
    (changed.capture/'stable-ids.json').write_text(json.dumps(changed.ids,sort_keys=True)+'\n')
    rows=[]
    for index,op in enumerate(operations):
        if op['kind'] in KINDS:
            rows.extend({'operation_index':index,**r} for r in review(base,changed,op,edits))
    (changed.capture/'source-edit-map.json').write_text(json.dumps({'schema':'source-edit-map-v1','changes':rows},sort_keys=True)+'\n')
    return p


def verify_expression(model,node,request,additions):
    e=model.expression_records[node]
    exprs={v['id']:n for n,v in model.expression_records.items()}
    children=[exprs[c] for c in e['children']]
    if 'integer' in request:
        value=request['integer']
        okay=e['kind']=='integer' and e['value']==value
        if value<0 and e.get('operator')=='negate' and len(children)==1:
            child=model.expression_records[children[0]]
            okay=child['kind']=='integer' and child['value']==-value
        require(okay,'SOURCE_EDIT_EXPRESSION')
    elif 'declaration_id' in request:
        ident=request['declaration_id']
        if ident in additions:ident=model.ids[model.declarations[additions[ident]]]
        require(node in model.bindings and model.ids[model.bindings[node]]==ident,'SOURCE_EDIT_BINDING')
    else:
        unary={'-':'negate','~':'complement','<':'low','>':'high'}
        binary={'+':'add','-':'subtract','*':'multiply','/':'divide','%':'remainder',
                '<<':'shift_left','>>':'shift_right','&':'bit_and','|':'bit_or','^':'bit_xor'}
        args=request['operands'];operators=unary if len(args)==1 else binary
        require(e.get('operator')==operators[request['operator']] and len(children)==len(args),'SOURCE_EDIT_EXPRESSION')
        for child,arg in zip(children,args):verify_expression(model,child,arg,additions)


def reference_inventory(base,changed,plan,edits):
    expected={base.ids[r] for r in base.bindings if r not in plan['removed']|plan['replaced']}
    selected=set()
    for kind,n,_ in plan['intents']:
        if kind=='declare':selected.update(descendants(changed,changed.declarations[n]))
        elif kind=='expression':
            lo,hi=base.ranges[n];lo=translated(lo,edits,True);hi=translated(hi,edits,False)
            selected.update(r for r in changed.bindings if lo<=changed.ranges[r][0] and changed.ranges[r][1]<=hi)
    actual={changed.ids[r] for r in changed.bindings if r not in selected}
    return expected==actual


def previews(model,operations):
    rows=[]
    for op in operations:
        if op['kind'] not in KINDS:continue
        if op['kind']=='reflow_data':
            for group_index,group in enumerate(op['groups']):
                for operand_index,ident in enumerate(group):
                    rows.append({'kind':'reflow_operand','record_id':ident,'group_index':group_index,
                        'operand_index':operand_index,'reason':op['reason'],
                        'format':op.get('formats',{}).get(ident,'preserve'),
                        'boundary':next((b for b in op.get('boundaries',[]) if b['operand_id']==ident),None)})
            continue
        ident=op.get('expression_id',op.get('declaration_id',op.get('anchor_id')))
        owner=model.owners[model.node(ident)] if ident else None
        rows.append({**op,'owner_id':model.ids[owner] if owner is not None else None})
    return rows


def review(before,after,op,edits):
    """One bounded identity row per copied operand; no raw source dump."""
    result=[]
    def record(model,ident):
        if ident not in model.nodes:return None
        n=model.node(ident);lo,hi=model.ranges[n]
        return {'record_id':ident,'kind':model.facts[n]['kind'],'name':model.name(n),
                'span':model.facts[n]['span'],'preimage':digest(model.source[lo:hi]),
                'expression_view':{'view':'expression','record_id':ident} if n in model.expression_records else None,
                'declaration_id':model.ids[model.bindings[n]] if n in model.bindings else None}
    if op['kind']=='reflow_data':ids=[i for g in op['groups'] for i in g]
    elif op['kind']=='declare':ids=[after.ids[after.declarations[op['name']]]]
    elif op['kind'] in ('unit_replace','comment_insert'):
        return [{'kind':'source_change','operation':op}]
    elif op['kind']=='localize':
        n=before.node(op['declaration_id'])
        ids=[op['declaration_id']]+[before.ids[r] for r,d in before.bindings.items() if d==n]
    else:ids=[op.get('declaration_id',op.get('expression_id'))]
    for index,ident in enumerate(ids):
        target=ident
        if op['kind']=='replace_expression':
            lo,hi=before.ranges[before.node(ident)]
            span=(translated(lo,edits,True),translated(hi,edits,False))
            target=next(after.ids[n] for n in after.expression_records if after.ranges[n]==span)
        result.append({'kind':'source_change','operation_kind':op['kind'],'reason':op['reason'],
                       'operand_index':index if op['kind']=='reflow_data' else None,
                       'before':record(before,ident),'after':record(after,target),
                       'request':op if op['kind']!='reflow_data' else
                       {'group_index':next(j for j,g in enumerate(op['groups']) if ident in g),
                        'group_operand_index':next(g.index(ident) for g in op['groups'] if ident in g),
                        'format':op.get('formats',{}).get(ident,'preserve')}})
    for boundary in op.get('boundaries',[]):
        result.append({'kind':'source_change','operation_kind':'data_boundary','reason':op['reason'],
                       'before':None,'after':record(after,after.ids[after.declarations[boundary['name']]]),
                       'operand_id':boundary['operand_id'],'header':boundary.get('header',[])})
    return result
