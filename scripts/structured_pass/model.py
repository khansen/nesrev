"""Service views over XORcyst's published source-model contract.

The compatibility-shaped dictionaries below are projections of native records,
not a second parser. Exact byte spans, bindings and lexical owners are producer
fields. Stable IDs across edits come only from recorded edit provenance.
"""
import base64
from bisect import bisect_right
from collections import defaultdict
import hashlib
import json
from pathlib import Path

from . import producer


def digest(data):
    return hashlib.sha256(data).hexdigest()


def translated(position, edits, right):
    delta = 0
    for lo, hi, replacement in edits:
        if lo == hi:
            if position > lo or (position == lo and right):
                delta += len(replacement)
        elif position >= hi:
            delta += len(replacement) - (hi-lo)
        elif position > lo:
            raise ValueError('RECORD_ALIGNMENT_FAILED')
    return position + delta


class Model:
    def __init__(self, capture, previous=None, edits=(), prefix='new'):
        self.capture = Path(capture)
        self.document, raw = producer.load(self.capture/'model.json')
        doc = self.document
        self.source = next(iter(raw.values()))
        self.lines = [0] + [i+1 for i,b in enumerate(self.source) if b == 10]
        self.facts = {s['id']:dict(s, parent=s['parent_id'], span=self.line_span(s['span'])) for s in doc['syntax']}
        self.children = defaultdict(list, {s['id']:s['children'] for s in doc['syntax']})
        self.ranges = {s['id']:(s['span']['byte_start'],s['span']['byte_end_exclusive']) for s in doc['syntax']}
        self.declaration_records = {d['syntax_id']:d for d in doc['declarations']}
        decls = {d['id']:d for d in doc['declarations']}
        exprs = {e['id']:e for e in doc['expressions']}
        values = {v['expression_id']:v for v in doc['evaluations']}
        self.bindings = {}
        self.reference_contexts = {}
        self.expression_records = {e['syntax_id']:e for e in doc['expressions']}
        self.values = {}
        self.declarations = {}
        for n,d in self.declaration_records.items():
            self.facts[n]['name'] = d['name']
            if d['kind'] == 'equ':
                self.facts[self.children[n][0]]['name'] = d['name']
                self.values[d['name']] = values[d['expression_id']]['value']['value']
            if d['kind'] in ('equ','global'):
                self.declarations[d['name']] = n
        for n,e in self.expression_records.items():
            for key in ('value','operator'):
                if key in e:
                    self.facts[n]['operator_name' if key == 'operator' else key] = e[key]
            if 'bytes_base64' in e:
                self.facts[n]['string_hex'] = base64.b64decode(e['bytes_base64']).hex()
        for r in doc['references']:
            n = exprs[r['expression_id']]['syntax_id']
            self.facts[n]['name'] = r['name']
            self.bindings[n] = decls[r['declaration_id']]['syntax_id']
            self.reference_contexts[n] = r['context_syntax_id']
        id_file = self.capture/'stable-ids.json'
        if previous is not None:
            old = {}
            for n,(lo,hi) in previous.ranges.items():
                try:
                    key = (previous.facts[n]['kind'],translated(lo,edits,True),translated(hi,edits,False))
                except ValueError:
                    continue
                producer.require(key not in old, 'RECORD_ALIGNMENT_FAILED')
                old[key] = previous.ids[n]
            self.ids = {n:old.get((s['kind'],*self.ranges[n]),prefix+'-'+n) for n,s in self.facts.items()}
            id_file.write_text(json.dumps(self.ids,sort_keys=True)+'\n')
        elif id_file.exists():
            self.ids = json.loads(id_file.read_text())
            producer.require(set(self.ids) == set(self.facts), 'RECORD_ALIGNMENT_FAILED')
        else:
            self.ids = {n:n for n in self.facts}
            id_file.write_text(json.dumps(self.ids,sort_keys=True)+'\n')
        producer.require(len(set(self.ids.values())) == len(self.ids), 'RECORD_ALIGNMENT_FAILED')
        self.nodes = {v:k for k,v in self.ids.items()}
        self.units = []
        for u in doc['units']:
            start = u['byte_start']; line = bisect_right(self.lines,start)
            self.units.append({**u,'line':line,'column':start-self.lines[line-1]+1,
                'hex':self.source[start:u['byte_end_exclusive']].hex()})
        binary = base64.b64decode(doc['binary']['bytes_base64'])
        self.locations = {}
        self.owners = {}
        scopes = {s['id']:s for s in doc['scopes']}
        for n,f in self.facts.items():
            owner = scopes[f['scope_id']]['anchor_declaration_id']
            self.owners[n] = decls[owner]['syntax_id'] if owner else None
        for row in doc['locations']:
            self.locations[row['syntax_id']] = {**row,'length':row['byte_length'],
                'bytes':list(binary[row['output_offset']:row['output_offset']+row['byte_length']])}
        self.instructions = {}
        for r in doc['instructions']:
            n=r['syntax_id'];loc=self.locations[n];owner=self.owners[n]
            operand=values[r['operands'][0]['expression_id']]['value'] if r['operands'] else None
            self.instructions[n] = {**r,**loc,'addressing_mode':r['final_mode'],
                'lexical_owner':self.name(owner) if owner is not None else None,
                'operand_value':operand['value'] if operand and operand['kind']=='integer' else None}

    def line_span(self,span):
        lo,hi = span['byte_start'],span['byte_end_exclusive']
        first,last = bisect_right(self.lines,lo),bisect_right(self.lines,hi)
        return [first,lo-self.lines[first-1]+1,last,hi-self.lines[last-1]+1]

    def node(self,stable):
        if not isinstance(stable,str) or stable not in self.nodes:
            raise ValueError('UNKNOWN_RECORD')
        return self.nodes[stable]

    def name(self,node):
        return self.facts[node].get('name')

    def context(self,node):
        if node in self.reference_contexts:
            return self.reference_contexts[node]
        e=self.expression_records.get(node)
        if e is not None:
            return e['context_syntax_id']
        while self.facts[node]['kind'] not in producer.CONTEXTS:
            node=self.facts[node]['parent']
            producer.require(node is not None,'SOURCE_MODEL_JOIN')
        return node

    def expression(self,node):
        f=self.facts[node]
        result={'record_id':self.ids[node],'kind':f['kind']}
        for key in ('name','value','operator_name','string_hex','datatype'):
            if key in f:result[key]=f[key]
        if node in self.bindings:result['declaration_id']=self.ids[self.bindings[node]]
        result['children']=[self.expression(n) for n in self.children[node]]
        return result

    def statement(self,node):
        f=self.facts[node]
        children=[] if node in self.declaration_records and f['kind']!='EQU_NODE' else self.children[node]
        result={'record_id':self.ids[node],'kind':f['kind'],'span':f['span'],
            'preimage_sha256':digest(self.source[slice(*self.ranges[node])]),
            'expressions':[self.expression(n) for n in children]}
        if node in self.instructions:
            rec=self.instructions[node]
            result.update({key:rec[key] for key in ('mnemonic','addressing_mode','lexical_owner','segment_id',
                'cpu_address','output_offset','operand_value','bytes','memory_access','control_flow')})
        else:
            result['name']=self.name(node)
            if f['kind']=='EQU_NODE':result['value']=self.values[self.name(node)]
            if node in self.locations:
                result.update({key:self.locations[node][key] for key in ('segment_id','cpu_address','output_offset','bytes')})
        return result

    def reaches(self,declaration,target,seen=None):
        if declaration==target:return True
        seen=set() if seen is None else seen
        if declaration in seen:return False
        seen.add(declaration)
        return any(self.reaches(bound,target,seen) for ref,bound in self.bindings.items() if self.context(ref)==declaration)


def certify(source,capture,reference,previous=None,edits=(),prefix='new'):
    producer.produce(source,capture,reference)
    model=Model(capture,previous,edits,prefix)
    return model,{'source_sha256':digest(model.source),'producer_sha256':producer.sha(producer.EXE),
        'reference_prg_parity':True,'roundtrip_exact':True,'model_id':model.document['identity']['model_id'],
        'coverage':model.document['coverage']}
