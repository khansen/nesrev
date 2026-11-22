"""Operator-bounded workloads derived from the retained assembler model.

This enumerates facts, not semantics or a control-flow proof. Lexical routine
bounds and the memory map are operator choices. Producer/consumer contexts and
called interfaces are then derived rather than manually selected for the price.
"""
import json
from . import analogue_inputs, evidence_views, navigation, producer
from .model import digest


def identity(value):
    return digest(json.dumps(value,sort_keys=True,separators=(',',':')).encode())


def routine(model,choice):
    producer.require(set(choice)=={'symbol','through_return'} and
                     choice['through_return'] in ('RTS','RTI'),'EVIDENCE_REQUEST_INVALID')
    nav=navigation.Navigation(model);n=nav.select(choice['symbol'],None)
    selected=nav.selection(n,'segment')
    end=next((i for i,k in enumerate(selected)
              if model.instructions.get(k,{}).get('mnemonic')==choice['through_return']),None)
    producer.require(end is not None,'EVIDENCE_REQUEST_INVALID')
    return selected[:end+1]


def build(model,spec):
    producer.require(set(spec)=={'roots','vector','ram_ranges','analogues'},'EVIDENCE_REQUEST_INVALID')
    producer.require(isinstance(spec['roots'],list) and spec['roots'] and
                     isinstance(spec['analogues'],list),'EVIDENCE_REQUEST_INVALID')
    ranges=spec['ram_ranges']
    producer.require(isinstance(ranges,list) and ranges and all(isinstance(r,list) and len(r)==2 and
        all(type(v)is int for v in r) and 0<=r[0]<=r[1]<=65535 for r in ranges),'EVIDENCE_REQUEST_INVALID')
    nav=navigation.Navigation(model)
    roots=[routine(model,choice) for choice in spec['roots']]
    selected={n for nodes in roots for n in nodes}
    locations={(model.locations[n]['segment_id'],model.locations[n]['cpu_address'])
               for n in selected if n in model.locations}
    addresses=set();operands=[];transfers=[]
    for n in sorted(selected,key=lambda k:model.ranges[k]):
        ins=model.instructions.get(n)
        if ins is None:continue
        for part_name,part in (ins.get('memory_access') or {}).items():
            if not isinstance(part,dict):continue
            for field in ('address','high_byte_address'):
                address=part.get(field)
                if type(address)is int and any(lo<=address<=hi for lo,hi in ranges):
                    addresses.add(address)
                    operands.append({'record_id':model.ids[n],'part':part_name,'field':field,
                                     'address':address,'indexed':bool(part.get('index_register')),
                                     'via_pointer':bool(part.get('via_pointer'))})
        flow=ins['control_flow']
        if flow['kind']!='none':transfers.append({'record_id':model.ids[n],**flow})
    helpers=[];seen=set()
    for transfer in transfers:
        if transfer['kind']!='call' or transfer['target'] in seen:continue
        seen.add(transfer['target'])
        found=[n for n in nav.globals if model.locations.get(n,{}).get('cpu_address')==transfer['target']
               and model.locations.get(n,{}).get('segment_id')==model.locations[model.nodes[transfer['record_id']]]['segment_id']]
        producer.require(len(found)==1,'EVIDENCE_UNAVAILABLE')
        choice={'symbol':model.name(found[0]),'through_return':'RTS'}
        helpers.append({'choice':choice,'records':[model.ids[n] for n in routine(model,choice)]})
    counts={};owners=set()
    for address in sorted(addresses):
        rows=evidence_views.memory(model,address=address);counts[str(address)]={}
        for row in rows:
            category=row['category'];counts[str(address)][category]=counts[str(address)].get(category,0)+1
            if category in ('direct','indexed_exact_base','pointer_byte') and row['owner_id']:
                owners.add(model.nodes[row['owner_id']])
    analogues=[]
    for choice in spec['analogues']:
        producer.require(set(choice)=={'index','symbol','through_return'},'EVIDENCE_REQUEST_INVALID')
        other=analogue_inputs.project(model,choice['index'])
        nodes=routine(other,{k:v for k,v in choice.items() if k!='index'})
        analogues.append({'choice':choice,'model_id':other.document['identity']['model_id'],
                          'source_sha256':digest(other.source),'records':[other.ids[n] for n in nodes]})
    vector=nav.select(spec['vector'],None)
    open_transfers=[t for t in transfers if t['kind'] in ('branch','jump') and
        (model.locations[model.nodes[t['record_id']]]['segment_id'],t['target']) not in locations]
    value={'schema':'corridor-inventory-v1','model_id':model.document['identity']['model_id'],
        'source_sha256':digest(model.source),'spec':spec,
        'roots':[{'choice':choice,'records':[model.ids[n] for n in nodes]} for choice,nodes in zip(spec['roots'],roots)],
        'vector_records':[model.ids[n] for n in nav.selection(vector,'label')],
        'ram_addresses':sorted(addresses),'ram_operands':operands,'transfers':transfers,
        'open_root_transfers':open_transfers,
        'category_counts_by_address':counts,'helpers':helpers,'analogues':analogues,
        'access_owner_blocks':[{'owner_id':model.ids[n],
            'records':[model.ids[k] for k in nav.selection(n,'label')]}
            for n in sorted(owners,key=lambda k:model.ranges[k])],
        'coverage':'RAM set comes from every explicit native operand and pointer byte in the declared roots and memory ranges. Indexed/indirect destinations remain unknown in the complete RAM evidence. Every direct/exact-base/pointer-byte access owner block is priced. Each direct called helper interface is read through its first return; nested calls and access-owner context do not expand the semantic corridor. Operator routine bounds require review; this inventory is not control-flow or ownership proof.'}
    return {**value,'inventory_sha256':identity(value)}


def verify(model,inventory):
    producer.require(inventory==build(model,inventory['spec']),'CAPTURE_CHANGED')
    return inventory
