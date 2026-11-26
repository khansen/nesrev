"""Service-owned delivery journal and atomic investigation checkpoints.

Submission is staged, never accepted on the strength of a client's assertion.
The coordinator reconciles the finished native output before publishing a
checkpoint. Consumers repeat that reconciliation against the final audit.
"""
import io
import json
from pathlib import Path

from . import paging
from . import investigation as inv, service
from .durable_artifact import Store
from .producer import require
from .publication import immutable_file

ERRORS = inv.ERRORS


def input_page(value, input_id, generation, offset=0, limit=paging.INPUT_CHARS):
    from . import review_pages
    text=inv.canonical(value).decode()
    paging.validate(offset, limit, paging.INPUT_CHARS, len(text))
    count=min(limit,len(text)-offset)
    while True:
        end=offset+count
        answer={'generation':generation,'id':input_id,'sha256':inv.digest(text.encode()),
            'offset':offset,'limit':limit,'total_characters':len(text),'text':text[offset:end],
            'next_offset':end if end<len(text) else None}
        if review_pages.wire_size(answer)<=review_pages.BUDGET-4096:return answer
        require(count>1,'RESPONSE_TOO_LARGE');count//=2


def input_wire_bytes(value, input_id, generation):
    """Price the actual text/envelope codec, with a conservative request ID."""
    from . import bridge
    offset=0; total=0
    while True:
        answer=input_page(value,input_id,generation,offset)
        output=io.StringIO()
        bridge.emit(None,'0'*64,{'result':{'content':[{'type':'text','text':json.dumps(answer)}]}},output,'input')
        total+=len(output.getvalue().encode())
        offset=answer['next_offset']
        if offset is None:return total


def read(path):
    return json.loads(Path(path).read_bytes())


def output_text(value):
    """The native MCP result may be an object or its serialized JSON string."""
    if isinstance(value, list):
        require(len(value) == 2 and all(isinstance(v, dict) and v.get('type') == 'input_text'
                and isinstance(v.get('text'), str) for v in value) and
                value[0]['text'].startswith('Wall time: ') and value[0]['text'].endswith('\nOutput:'),
                'INVESTIGATION_AUDIT_MISMATCH')
        return value[1]['text']
    if isinstance(value, str):
        try: value = json.loads(value)
        except ValueError: raise ValueError('INVESTIGATION_AUDIT_MISMATCH') from None
    require(isinstance(value, dict) and isinstance(value.get('content'), list) and
            len(value['content']) == 1 and value['content'][0].get('type') == 'text' and
            isinstance(value['content'][0].get('text'), str), 'INVESTIGATION_AUDIT_MISMATCH')
    return value['content'][0]['text']


def reconcile(journal, audit):
    """Pair actual calls in order, checking arguments and full result bytes.

    Native call IDs and bridge request IDs are different namespaces. Repeated
    identical requests are therefore paired by order, never an ambiguous lookup.
    Only outputs after the last compaction contribute coverage.
    """
    require(set(audit) == {'session_id', 'last_compaction', 'calls'}, 'INVESTIGATION_AUDIT_MISMATCH')
    require(len(journal) == len(audit['calls']), 'INVESTIGATION_AUDIT_MISMATCH')
    require(isinstance(audit['session_id'], str) and audit['session_id'] and
            type(audit['last_compaction']) is int and audit['last_compaction'] >= -1,
            'INVESTIGATION_AUDIT_MISMATCH')
    receipts = []; deliveries = []; ids = set(); previous = -1
    for receipt, call in zip(journal, audit['calls']):
        require(set(call) == {'call_id', 'arguments', 'output', 'position'} and
                isinstance(call['call_id'], str) and call['call_id'] not in ids and
                type(call['position']) is int and call['position'] > previous,
                'INVESTIGATION_AUDIT_MISMATCH')
        previous = call['position']
        ids.add(call['call_id'])
        arguments = json.loads(call['arguments']) if isinstance(call['arguments'], str) else call['arguments']
        require(arguments == receipt['request'] and
                inv.digest(output_text(call['output']).encode()) == receipt['response_sha256'],
                'INVESTIGATION_AUDIT_MISMATCH')
        receipts.append({'session_id': audit['session_id'], 'call_id': call['call_id'],
            'catalog_sha256': receipt['catalog_sha256'], 'units': receipt['units'],
            'response_sha256': receipt['response_sha256'],'input_spans':receipt.get('input_spans',[])})
        if call['position'] > audit['last_compaction']:
            deliveries.append({'call_id': call['call_id'], 'position': call['position'],
                               'response_sha256': receipt['response_sha256']})
    return receipts, {'session_id': audit['session_id'], 'last_compaction': audit['last_compaction'],
                      'deliveries': deliveries}


class Workflow:
    def __init__(self, root, controller=None):
        from .launcher import Corridor
        self.root = Path(root).resolve()
        self.config = read(self.root/'plan.json')
        self.controller = controller or Corridor(self.config['corridor'])
        self.store = Store(self.controller.config['store'])

    @classmethod
    def prepare(cls, root, controller, inventory, assignments, *, checkpoint_bytes=65536, checkpoint_caps=None,
                handoff_dependencies=None):
        root = Path(root).resolve()
        require(not root.exists() and type(checkpoint_bytes) is int and 0 < checkpoint_bytes <= 65536,
                'INVESTIGATION_PLAN_INVALID')
        with controller.editor.transaction(write=True):
            state = controller.checked_editor(); generation = state['current']
            require('investigation_gate' not in state and not state['candidates'] and
                    generation == state['pass_start_generation'], 'INVESTIGATION_TRANSITION_INVALID')
            model = controller.editor.model(generation)
            catalog = inv.catalog(model, generation, inventory)
            plan = inv.partition_plan(catalog, assignments)
            ids=[e['id'] for e in plan['entries']]
            caps=checkpoint_caps if checkpoint_caps is not None else {
                ident:checkpoint_bytes//len(ids) for ident in ids}
            require(isinstance(caps,dict) and set(caps)==set(ids) and
                    all(type(v) is int and v>0 for v in caps.values()) and
                    sum(caps.values())<=checkpoint_bytes,'INVESTIGATION_PLAN_INVALID')
            dependencies=handoff_dependencies if handoff_dependencies is not None else {ident:[] for ident in ids}
            require(isinstance(dependencies,dict) and set(dependencies)==set(ids) and
                    all(isinstance(dependencies[ident],list) and len(set(dependencies[ident]))==len(dependencies[ident])
                        and set(dependencies[ident])<=set(ids[:index]) for index,ident in enumerate(ids)),
                    'INVESTIGATION_PLAN_INVALID')
            config = {'schema':'investigation-workflow-v1','corridor':str(controller.root),
                'run_id':controller.config['run_id'],'inventory':inventory,'catalog':catalog,
                'partitions':plan,'checkpoint_bytes':checkpoint_bytes,'checkpoint_caps':caps,
                'handoff_dependencies':dependencies,
                'edit_targets':inv.edit_targets(model,inventory)}
            root.mkdir(parents=True)
            immutable_file(root/'plan.json', inv.canonical(config))
            service.write_json(root/'state.json', {'active':None,'sessions':{},'editing':False})
            state['investigation_gate'] = {'root':str(root),'plan_sha256':service.producer.sha(root/'plan.json'),
                                           'editing_admitted':False}
            controller.editor.save()
        return cls(root, controller)

    def checked(self, *, historical=False):
        state = self.controller.checked_editor(); gate = state.get('investigation_gate', {})
        require(gate.get('root') == str(self.root) and gate.get('plan_sha256') ==
                service.producer.sha(self.root/'plan.json') and self.config == read(self.root/'plan.json') and
                self.config['run_id'] == self.controller.config['run_id'], 'INVESTIGATION_CHANGED')
        generation = self.config['catalog']['binding']['generation']
        require(state['current'] == generation or historical and gate.get('editing_admitted'), 'INVESTIGATION_CHANGED')
        model = self.controller.editor.model(generation)
        require(inv.catalog(model, generation, self.config['inventory']) == self.config['catalog'],
                'INVESTIGATION_CHANGED')
        require(inv.edit_targets(model,self.config['inventory'])==self.config['edit_targets'],'INVESTIGATION_CHANGED')
        return read(self.root/'state.json')

    def entry(self, ident):
        found = [e for e in self.config['partitions']['entries'] if e['id'] == ident]
        require(len(found) == 1, 'INVESTIGATION_TRANSITION_INVALID')
        return found[0]

    def journal(self, session):
        return [json.loads(self.store.get(sha)) for sha in session['journal']]

    def handoffs(self, state):
        result={}
        for entry in self.config['partitions']['entries']:
            session=state['sessions'].get(entry['id'],{})
            if not session.get('accepted'):continue
            envelope=json.loads(self.store.get(session['accepted']))
            require(envelope['plan_sha256']==inv.sha(self.root/'plan.json'), 'INVESTIGATION_CHANGED')
            result['investigation-handoff-'+entry['id']]=inv.handoff(envelope['checkpoint'],self.config['catalog'])
        return result

    def check_handoff_cap(self, state, additional=None):
        values=self.handoffs(state)
        if additional is not None:
            values['investigation-handoff-'+additional['partition_id']]=additional
        generation=self.config['catalog']['binding']['generation']
        sizes={value['partition_id']:input_wire_bytes(value,key,generation) for key,value in values.items()}
        require(all(size<=self.config['checkpoint_caps'][entry] for entry,size in sizes.items()),
                'INVESTIGATION_CHECKPOINT_TOO_LARGE')
        size=sum(sizes.values())
        require(size<=self.config['checkpoint_bytes'],'INVESTIGATION_CHECKPOINT_TOO_LARGE')
        return size

    def check_claim_links(self,state,entry_id,submission):
        known={(value['partition_id'],claim['id']) for value in self.handoffs(state).values()
               for claim in value['claims']}
        known.update((entry_id,claim['id']) for claim in submission['claims'])
        for claim in submission['claims']:
            for name in ('dependencies','conflicts'):
                require(all((ref['partition_id'],ref['claim_id']) in known and
                            (ref['partition_id'],ref['claim_id'])!=(entry_id,claim['id'])
                            for ref in claim.get(name,[])), 'INVESTIGATION_CITATION_INVALID')

    def begin(self, entry_id, session_id, parent_audits):
        """Coordinator action after native admission; no model chooses a session."""
        with self.controller.editor.transaction(write=True):
            state = self.checked()
            require(state['active'] is None and not state['editing'] and entry_id not in state['sessions'] and
                    isinstance(session_id, str) and session_id and
                    session_id not in {r['session_id'] for r in state['sessions'].values()},
                    'INVESTIGATION_TRANSITION_INVALID')
            index = self.config['partitions']['entries'].index(self.entry(entry_id))
            predecessors = [e['id'] for e in self.config['partitions']['entries'][:index]]
            require(set(state['sessions']) == set(predecessors) and set(parent_audits) == set(predecessors),
                    'INVESTIGATION_TRANSITION_INVALID')
            parents = {ident:self.check_saved(ident, parent_audits[ident], state)['sha256'] for ident in predecessors}
            self.check_handoff_cap(state)
            state['active'] = entry_id
            state['sessions'][entry_id] = {'session_id':session_id,'parents':parents,
                                          'native_session_id':None,'journal':[],'staged':None,'accepted':None}
            service.write_json(self.root/'state.json', state)
            return {'plan_sha256':service.producer.sha(self.root/'plan.json'), 'parents':parents,
                    'entry_id':entry_id,'session_id':session_id,'generation':self.config['catalog']['binding']['generation']}

    def units(self, operation, arguments, answer):
        """Coverage comes only from successful source/fact pages, never claims."""
        from . import corridor_capacity
        catalog = self.config['catalog']; reached = set()
        if answer.get('error'): return []
        if operation == 'navigate' and arguments.get('view') in ('source','records','records_compact','edit'):
            if arguments['view'] == 'edit':
                records = [dict(zip(answer['columns'], row)) for row in answer['records']]
            else: records = corridor_capacity.expand(answer)
            scope = 'analogue:'+str(arguments['analogue_index']) if 'analogue_index' in arguments else 'local'
            ids = {r['record_id'] for r in records}
            reached = {key for key,row in catalog['evidence'].items()
                       if row['kind'] == 'record' and row['scope'] == scope and row['record_id'] in ids}
        elif operation == 'evidence' and arguments.get('view') == 'ram_set':
            rows = []
            for values in answer['records']:
                row = {**answer['constants'], **dict(zip(answer['columns'], values))}
                for field, dictionary in answer.get('dictionaries', {}).items():
                    row[field] = dictionary[str(row[field])]
                rows.append(row)
            for row in rows:
                addresses = set(row['addresses'])
                fact = {k:v for k,v in row.items() if k != 'addresses'}
                matches = [(key,r['fact']) for key,r in catalog['evidence'].items()
                    if r['kind'] == 'ram' and {k:v for k,v in r['fact'].items() if k != 'addresses'} == fact]
                require(len(matches) == 1, 'INVESTIGATION_RECEIPT_INVALID')
                key, parent = matches[0]
                require(addresses <= set(parent['addresses']), 'INVESTIGATION_RECEIPT_INVALID')
                reached.update(key+':'+str(a) for a in addresses)
        return sorted(reached)

    def delivered(self, entry_id, request, result):
        """Record the final bridge text before emission; audit proves receipt."""
        text = output_text(result); answer = json.loads(text)
        with self.controller.editor.transaction(write=True):
            state = self.checked()
            require(state['active'] == entry_id, 'INVESTIGATION_TRANSITION_INVALID')
            record = {'request':request,'response_sha256':inv.digest(text.encode()),
                'catalog_sha256':self.config['catalog']['sha256'],
                'units':self.units(request['operation'],request['arguments'],answer),'input_spans':[]}
            if request['operation']=='input' and not answer.get('error'):
                key=request['arguments']['input_id']
                if key in self.config['catalog']['inputs']:
                    source=self.config['catalog']['inputs'][key]
                    require(answer['id']==key and answer['sha256']==source['sha256'] and
                            answer['total_characters']==source['characters'], 'INVESTIGATION_RECEIPT_INVALID')
                    record['input_spans']=[{'id':key,'sha256':source['sha256'],
                        'start':answer['offset'],'end':answer['offset']+len(answer['text'])}]
            state['sessions'][entry_id]['journal'].append(self.store.put(inv.canonical(record)))
            service.write_json(self.root/'state.json', state)

    def stage(self, entry_id, submission):
        with self.controller.editor.transaction(write=True):
            state = self.checked()
            require(state['active'] == entry_id, 'INVESTIGATION_TRANSITION_INVALID')
            require(isinstance(submission, dict) and set(submission) == {'claims','decisions'},
                    'INVESTIGATION_CHECKPOINT_INVALID')
            # Validate fixable submission mistakes now. The provisional receipt
            # window cannot publish coverage; finalize requires the native audit.
            session = state['sessions'][entry_id]
            journal = self.journal(session)
            receipts = [{**inv.receipt(self.config['catalog'], session['session_id'], str(i),
                row['units'], row['response_sha256']),'input_spans':row.get('input_spans',[])}
                for i,row in enumerate(journal)]
            provisional = {'session_id':session['session_id'],'last_compaction':-1,
                'deliveries':[{'call_id':str(i),'position':i,'response_sha256':r['response_sha256']}
                              for i,r in enumerate(journal)]}
            candidate=inv.checkpoint(self.config['catalog'], self.entry(entry_id), submission, receipts,
                                    provisional, maximum_bytes=self.config['checkpoint_bytes'])
            self.check_claim_links(state,entry_id,submission)
            self.check_handoff_cap(state,inv.handoff(candidate,self.config['catalog']))
            require(len(inv.canonical(submission)) <= self.config['checkpoint_bytes'],
                    'INVESTIGATION_CHECKPOINT_TOO_LARGE')
            blob = self.store.put(inv.canonical(submission))
            state['sessions'][entry_id]['staged'] = blob
            service.write_json(self.root/'state.json', state)
            return {'staged_sha256':blob,'completion':'pending_native_audit'}

    def finalize(self, entry_id, audit):
        with self.controller.editor.transaction(write=True):
            state = self.checked(); session = state['sessions'].get(entry_id)
            require(state['active'] == entry_id and session and session['staged'] and
                    isinstance(audit['session_id'],str) and audit['session_id'] and
                    audit['session_id'] not in {s['native_session_id'] for key,s in state['sessions'].items()
                                               if key != entry_id}, 'INVESTIGATION_TRANSITION_INVALID')
            receipts, checked = reconcile(self.journal(session), audit)
            submission = json.loads(self.store.get(session['staged']))
            accepted = inv.checkpoint(self.config['catalog'], self.entry(entry_id), submission, receipts,
                                     checked, maximum_bytes=self.config['checkpoint_bytes'])
            self.check_claim_links(state,entry_id,submission)
            self.check_handoff_cap(state,inv.handoff(accepted,self.config['catalog']))
            envelope = {'checkpoint':accepted,'parents':session['parents'],
                        'plan_sha256':service.producer.sha(self.root/'plan.json')}
            blob = self.store.put(inv.canonical(envelope))
            # An orphan immutable blob cannot satisfy a transition. This atomic
            # pointer is the single publication boundary under the editor lock.
            session['accepted'] = blob; session['native_session_id'] = audit['session_id']; state['active'] = None
            service.write_json(self.root/'state.json', state)
            return inv.handoff(accepted, self.config['catalog'])

    def check_saved(self, entry_id, audit, state):
        session = state['sessions'][entry_id]
        require(session['accepted'] is not None and session['native_session_id'] == audit['session_id'],
                'INVESTIGATION_TRANSITION_INVALID')
        envelope = json.loads(self.store.get(session['accepted']))
        require(envelope['plan_sha256'] == service.producer.sha(self.root/'plan.json') and
                envelope['parents'] == session['parents'], 'INVESTIGATION_CHANGED')
        for parent, digest in session['parents'].items():
            blob = json.loads(self.store.get(state['sessions'][parent]['accepted']))
            require(blob['checkpoint']['sha256'] == digest, 'INVESTIGATION_CHANGED')
        receipts, checked = reconcile(self.journal(session), audit)
        saved = envelope['checkpoint']
        inv.recheck(saved, self.config['catalog'], self.entry(entry_id), receipts, checked,
                    maximum_bytes=self.config['checkpoint_bytes'], allow_partial=True)
        return saved

    def admit_editor(self, audits):
        with self.controller.editor.transaction(write=True):
            state = self.checked()
            require(state['active'] is None and
                    set(audits) == {e['id'] for e in self.config['partitions']['entries']},
                    'INVESTIGATION_TRANSITION_INVALID')
            completed = set(); checkpoints = []
            for entry in self.config['partitions']['entries']:
                saved = self.check_saved(entry['id'], audits[entry['id']], state)
                require(not any(claim.get('conflicts') for claim in saved['claims']), 'INVESTIGATION_CONFLICT')
                completed.update(saved['coverage']['completed']); checkpoints.append(saved['sha256'])
            require(completed == set(self.config['catalog']['units']), 'INVESTIGATION_COVERAGE_INCOMPLETE')
            receipt = {'plan_sha256':service.producer.sha(self.root/'plan.json'),
                       'checkpoints':checkpoints,'coverage_sha256':inv.identity(sorted(completed))}
            self.check_handoff_cap(state)
            from .editor_admission import CAPS
            generation = self.config['catalog']['binding']['generation']
            require(self.transition_wire_bytes(receipt,self.handoffs(state)) <=
                    CAPS['transition-index-and-receipt-wire-cap'],
                    'INVESTIGATION_CHECKPOINT_TOO_LARGE')
            require(not state['editing'] or state['editing'] == receipt, 'INVESTIGATION_CHANGED')
            state['editing'] = receipt
            service.write_json(self.root/'state.json', state)
            self.controller.editor.state['investigation_gate']['editing_admitted'] = inv.identity(receipt)
            self.controller.editor.save()
            return receipt

    def editor_inputs(self):
        state=self.checked(historical=True)
        gate=self.controller.editor.state['investigation_gate']
        require(state['editing'] and gate['editing_admitted']==inv.identity(state['editing']),
                'INVESTIGATION_READ_ONLY')
        return {'investigation-transition':state['editing'],**self.handoffs(state),
                'investigation-edit-targets':self.edit_target_index(),
                'investigation-read-recipe':self.editor_recipe()}

    def editor_recipe(self):
        from . import read_recipe
        return read_recipe.editor_recipe(self.config['inventory'],self.config['edit_targets'])

    def transition_wire_bytes(self, receipt, handoffs):
        generation=self.config['catalog']['binding']['generation']
        values={'investigation-transition':receipt,**handoffs,
                'investigation-edit-targets':self.edit_target_index(),
                'investigation-read-recipe':self.editor_recipe()}
        index=[{'id':key,'kind':'investigation','generation':generation,'sha256':inv.identity(value)}
               for key,value in values.items()]
        return (input_wire_bytes(receipt,'investigation-transition',generation)+
                input_wire_bytes(index,'investigation-index',generation)+
                input_wire_bytes(self.editor_recipe(),'investigation-read-recipe',generation))

    def prepared_transition_wire_bytes(self):
        # Digest lengths and index entries are fixed before investigators run;
        # handoff bodies have their own separately charged aggregate cap.
        entries=self.config['partitions']['entries']
        receipt={'plan_sha256':'0'*64,'checkpoints':['0'*64 for _ in entries],'coverage_sha256':'0'*64}
        return self.transition_wire_bytes(receipt,{'investigation-handoff-'+e['id']:{} for e in entries})

    def edit_target_index(self):
        return {'encoding':'source-edit-v1','records':len(self.config['edit_targets']),
                'selection_sha256':inv.identity(self.config['edit_targets']),
                'paging':'Record offsets, default/max limit 40. Typed record pages, not text.'}

    def editor_records(self,offset=0,limit=40):
        self.editor_inputs()
        catalog=self.config['catalog']
        require(self.controller.editor.state['current']==catalog['binding']['generation'],'STALE_GENERATION')
        model=self.controller.editor.model(catalog['binding']['generation'])
        return inv.record_page(catalog,model,self.config['edit_targets'],offset=offset,limit=limit,view='edit')
