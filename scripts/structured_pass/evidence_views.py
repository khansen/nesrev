"""Paged evidence derived from native source-model joins, never source parsing."""
import base64
from collections import Counter

from .model import digest
from .producer import require
from . import review_pages

ERRORS=frozenset(('EVIDENCE_REQUEST_INVALID','EVIDENCE_RANGE_INVALID','EVIDENCE_UNAVAILABLE'))


def indices(model):
    if not hasattr(model,'_evidence_indices'):
        contexts={};declarations={}
        for ref,decl in model.bindings.items():
            contexts.setdefault(model.context(ref),[]).append((ref,decl))
            declarations.setdefault(decl,[]).append(ref)
        model._evidence_indices=(contexts,declarations)
    return model._evidence_indices


def page(rows,offset=0,limit=40):
    require(type(offset) is int and offset>=0 and type(limit) is int and 1<=limit<=40,'EVIDENCE_REQUEST_INVALID')
    result={'records':[],'offset':offset,'total_records':len(rows),'next_offset':None}
    for row in rows[offset:offset+limit]:
        trial={**result,'records':result['records']+[row]}
        if review_pages.wire_size(trial)>review_pages.BUDGET-4096:
            require(bool(result['records']),'RESPONSE_TOO_LARGE');break
        result['records'].append(row)
    end=offset+len(result['records']);result['next_offset']=end if end<len(rows) else None
    return result


def identity(model,n):
    lo,hi=model.ranges[n];loc=model.locations.get(n,{})
    owner=model.owners[n]
    return {'record_id':model.ids[n],'kind':model.facts[n]['kind'],
            'span':model.facts[n]['span'],'preimage':digest(model.source[lo:hi]),
            'owner_id':model.ids[owner] if owner is not None else None,
            **{k:loc.get(k) for k in ('segment_id','cpu_address','output_offset')}}


def chain(model,decl,seen=()):
    if decl in seen:return []
    result=[decl]
    for ref,target in indices(model)[0].get(decl,[]):
        result.extend(chain(model,target,(*seen,decl)))
    return list(dict.fromkeys(result))


def outgoing(model,record_id):
    node=model.node(record_id);rows=[]
    instruction=model.instructions.get(node,{})
    if instruction:
        rows.append({**identity(model,node),'kind':'instruction_effects','statement_id':record_id,
                     'reference_id':None,'declaration_id':None,'control_flow':instruction['control_flow'],
                     'memory_access':instruction['memory_access']})
    for ref,decl in indices(model)[0].get(node,[]):
        location={k:model.locations.get(node,{}).get(k) for k in ('segment_id','cpu_address','output_offset')}
        rows.append({**identity(model,ref),**location,'statement_id':record_id,'reference_id':model.ids[ref],
            'declaration_id':model.ids[decl],
            'through_equ_declaration_ids':[model.ids[d] for d in chain(model,decl)[1:]],
            'control_flow':instruction.get('control_flow'),'memory_access':instruction.get('memory_access')})
    return rows


def memory(model,address=None,record_id=None):
    require((address is None)!=(record_id is None),'EVIDENCE_REQUEST_INVALID')
    if record_id is not None:
        n=model.node(record_id);require(n in model.declaration_records,'EVIDENCE_REQUEST_INVALID')
        address=model.values.get(model.name(n),model.locations.get(n,{}).get('cpu_address'))
    require(type(address) is int and 0<=address<=65535,'EVIDENCE_REQUEST_INVALID')
    rows=[]
    for n,instruction in model.instructions.items():
        access=instruction['memory_access']
        if not access:continue
        data=access['data'];pointer=access['pointer']; categories=[]
        if data:
            base=data['address'];index=data['index_register']
            if data['via_pointer']:categories.append(('unresolved_indirect_destination',None))
            elif index:
                if base==address:categories.append(('indexed_exact_base',None))
                elif base is not None:
                    width=256 if instruction['final_mode'] in ('ZEROPAGE_X_MODE','ZEROPAGE_Y_MODE') else 65536
                    if address<width and (address-base)%width<=255:categories.append(('indexed_other_base_possible',None))
            elif base==address:categories.append(('direct',None))
        if pointer:
            for part,key in (('low','address'),('high','high_byte_address')):
                if pointer['index_register']:
                    categories.append(('indexed_pointer_byte',part))
                elif pointer[key]==address:categories.append(('pointer_byte',part))
        for category,part in categories:
            proofs=[]
            # Equal values alone never establish an alias. The native operand
            # must be a bound identifier used as an actual memory base.
            if category in ('direct','indexed_exact_base'):
                for ref,decl in indices(model)[0].get(n,[]):
                    expression=model.expression_records[ref]
                    value=model.values.get(model.name(decl),model.locations.get(decl,{}).get('cpu_address'))
                    if expression['id'] in {o['expression_id'] for o in instruction['operands']} and value==address:
                        proofs.append(model.ids[decl])
            rows.append({**identity(model,n),'category':category,'pointer_part':part,
                'access':data['kind'] if data and part is None else 'read',
                'mnemonic':instruction['mnemonic'],'memory_access':access,
                'alias_proof_declaration_ids':proofs,
                'requested_declaration_id':record_id,'selected_alias_proven':record_id in proofs,
                'exact_destination':category=='direct','requested_address':address})
    return rows


def data_rows(model,record_id):
    n=model.node(record_id);rows=[];exprs={e['id']:node for node,e in model.expression_records.items()}
    if n in model.declaration_records:
        start=model.ranges[n][0]
        location=model.locations.get(n)
        require(model.declaration_records[n]['kind'] in ('global','local') and location is not None,'EVIDENCE_RANGE_INVALID')
        aliases={d for d,loc in model.locations.items() if location is not None and
                 (loc['segment_id'],loc['output_offset'])==(location['segment_id'],location['output_offset'])}
        stops=[model.ranges[d][0] for d,r in model.declaration_records.items()
               if r['kind']=='global' and model.ranges[d][0]>start and d not in aliases]
        stops.extend(model.ranges[d][0] for d,r in model.facts.items() if r['kind'] in ('ORG_NODE','INSTRUCTION_NODE','END_NODE') and model.ranges[d][0]>start)
        end=min(stops,default=len(model.source))
        selected=[r for r in model.document['data'] if start<=model.ranges[r['syntax_id']][0]<end]
    else:selected=[r for r in model.document['data'] if r['syntax_id']==n]
    require(bool(selected),'EVIDENCE_RANGE_INVALID')
    for data in selected:
        owner=data['syntax_id'];loc=model.locations[owner]
        for operand in data['operands']:
            expr=exprs[operand['expression_id']]
            rows.append({**identity(model,expr),'statement_id':model.ids[owner],
                'operand_index':operand['index'],'element_width':data['element_width'],
                'segment_id':loc['segment_id'],'output_offset':operand['output_offset'],
                'cpu_address':loc['cpu_address']+operand['output_offset']-loc['output_offset'],
                'byte_length':operand['byte_length'],'element_count':operand['element_count'],
                'emission_ranges':operand['emission_ranges'],
                'references':[{'reference_id':model.ids[r],'declaration_id':model.ids[d]}
                    for r,d in indices(model)[0].get(owner,[]) if
                    model.ranges[expr][0]<=model.ranges[r][0]<model.ranges[expr][1]]})
    return rows


def decode(model,record_id,decoder,byte_offset=0,byte_count=256):
    require(decoder in ('bytes','words_le') and type(byte_offset) is int and byte_offset>=0
            and type(byte_count) is int and 0<byte_count<=4096,'EVIDENCE_REQUEST_INVALID')
    operands=data_rows(model,record_id);start=operands[0]['output_offset']
    end=operands[-1]['output_offset']+operands[-1]['byte_length']
    require(len({r['segment_id'] for r in operands})==1 and start+byte_offset+byte_count<=end
            and all(a['output_offset']+a['byte_length']==b['output_offset'] for a,b in zip(operands,operands[1:])), 'EVIDENCE_RANGE_INVALID')
    width=1 if decoder=='bytes' else 2
    require(byte_offset%width==0 and byte_count%width==0,'EVIDENCE_RANGE_INVALID')
    data=base64.b64decode(model.document['binary']['bytes_base64'])[start+byte_offset:start+byte_offset+byte_count]
    return [{'output_offset':start+byte_offset+i,'segment_id':operands[0]['segment_id'],
             'value':int.from_bytes(data[i:i+width],'little'),'width':width} for i in range(0,len(data),width)]


def scopes(model,record_id=None):
    selected=model.node(record_id) if record_id is not None else None
    rows=[]
    for n,declaration in model.declaration_records.items():
        if selected is not None and n!=selected and model.owners[n]!=selected:continue
        refs=indices(model)[1].get(n,[])
        owners=sorted({model.ids[model.owners[model.context(r)]] for r in refs if model.owners[model.context(r)] is not None})
        rows.append({**identity(model,n),'name':model.name(n),'declaration_kind':declaration['kind'],
            'direct_use_count':len(refs),'use_owner_ids':owners[:32],'total_owners':len(owners),
            'owners_omitted':max(0,len(owners)-32),'all_uses_view':'navigate uses with this record_id',
            'reachability':'unknown; fallthrough, computed and external entries are not disproved',
            'safe_to_localize':None,'semantic_verdict':None})
    return rows


def units(model):
    rows=[]
    for index,unit in enumerate(model.units):
        if unit['kind'] not in ('comment','whitespace','newline'):continue
        data=bytes.fromhex(unit['hex'])
        rows.append({'unit_id':'u'+str(index),'kind':unit['kind'],'line':unit['line'],
            'column':unit['column'],'preimage':digest(data),'byte_length':len(data),
            'bytes_hex':data[:2048].hex(),'truncated':len(data)>2048})
    return rows


def expression(model,record_id):
    n=model.node(record_id);require(n in model.expression_records,'EVIDENCE_REQUEST_INVALID')
    from .source_edits import descendants
    rows=[]
    for child in descendants(model,n):
        fact=model.facts[child]
        if child not in model.expression_records:continue
        string=bytes.fromhex(fact['string_hex']) if 'string_hex' in fact else None
        rows.append({**identity(model,child),'value':fact.get('value'),'operator':fact.get('operator_name'),
            'children':[model.ids[c] for c in model.children[child]],
            'declaration_id':model.ids[model.bindings[child]] if child in model.bindings else None,
            'string_byte_length':len(string) if string is not None else None,
            'string_sha256':digest(string) if string is not None else None})
    return rows


def query(model,view,offset=0,limit=40,**args):
    functions={'ram':memory,'outgoing':outgoing,'data':data_rows,'decode':decode,'scopes':scopes,'units':units,'expression':expression}
    require(view in functions,'EVIDENCE_REQUEST_INVALID')
    allowed={'ram':{'address','record_id'},'outgoing':{'record_id'},'data':{'record_id'},
             'decode':{'record_id','decoder','byte_offset','byte_count'},'scopes':{'record_id'},'units':set(),'expression':{'record_id'}}
    require(set(args)<=allowed[view],'EVIDENCE_REQUEST_INVALID')
    required={'outgoing':{'record_id'},'data':{'record_id'},'decode':{'record_id','decoder'},'expression':{'record_id'}}
    require(required.get(view,set())<=set(args),'EVIDENCE_REQUEST_INVALID')
    rows=functions[view](model,**args)
    result=page(rows,offset,limit)
    if view=='ram':result['category_counts']=dict(Counter(row['category'] for row in rows))
    return {'view':view,'model_id':model.document['identity']['model_id'],**result}
