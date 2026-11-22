"""Fixed-entry, read-only client endpoint for a planned investigation context."""
import json
from pathlib import Path

from . import investigation as inv, operation_contract as contract, declared_inputs, evidence_views, review_pages
from .investigation_workflow import Workflow, read, input_page
from .producer import require


class Session:
    def __init__(self, root):
        self.config = read(Path(root)/'investigation-profile.json')
        require(set(self.config) == {'workflow','entry_id','plan_sha256'}, 'INVESTIGATION_CHANGED')
        self.workflow = Workflow(self.config['workflow'])
        self.entry = self.workflow.entry(self.config['entry_id'])
        require(inv.sha(self.workflow.root/'plan.json') == self.config['plan_sha256'], 'INVESTIGATION_CHANGED')

    def error_context(self, candidate=None):
        return {'generation':self.workflow.config['catalog']['binding']['generation']}

    def assignment(self):
        catalog = self.workflow.config['catalog']; inventory = self.workflow.config['inventory']
        model = self.workflow.controller.editor.model(catalog['binding']['generation'])
        reads = []; addresses = []; owners = []
        for name in self.entry['sets']:
            if name.startswith('ram:'):
                addresses.append(int(name.split(':')[1])); continue
            if name.startswith('access_owner_blocks:'):
                owners.append((name,inventory['access_owner_blocks'][int(name.split(':')[1])]))
                continue
            if name == 'declarations':
                ids = [catalog['evidence'][u]['record_id'] for u in catalog['sets'][name]]
                ids.sort(key=lambda r:model.ranges[model.node(r)])
                for offset in range(0,len(ids),128):
                    selected=ids[offset:offset+128]
                    reads.append({'sets':[name],'operation':'navigate',
                        'arguments':{'view':'edit','record_id':selected},'record_count':len(selected)})
                continue
            if name == 'vector':
                records = inventory['vector_records']; span = 'label'; analogue = {}
            else:
                kind,index = name.split(':'); row = inventory[kind][int(index)]
                records = row['records']; span = 'segment'
                analogue = {'analogue_index':row['choice']['index']} if kind == 'analogues' else {}
            if records:
                reads.append({'sets':[name],'operation':'navigate',
                    'arguments':{'view':'source','record_id':records[0],'span':span,**analogue},
                    'record_count':len(records),'stop_after_record_id':records[-1]})
        # Use the same bounded multi-owner read as corridor_capacity.plan. A
        # list of IDs describes this selection without repeating a read recipe
        # and an end record for every label block.
        for first in range(0,len(owners),128):
            part=owners[first:first+128]
            reads.append({'sets':[name for name,row in part],'operation':'navigate',
                'arguments':{'view':'source','record_id':[row['owner_id'] for name,row in part],'span':'label'},
                'record_count':len({r for name,row in part for r in row['records']})})
        if addresses:
            reads.append({'sets':['ram:'+str(a) for a in sorted(addresses)],'operation':'evidence',
                'arguments':{'view':'ram_set','address':sorted(addresses)}})
        return {'entry_id':self.entry['id'],'generation':catalog['binding']['generation'],
            'catalog_sha256':catalog['sha256'],
            'checkpoint_wire_cap':self.workflow.config['checkpoint_caps'][self.entry['id']],
            'sets':{name:{'coverage_units':len(catalog['sets'][name])} for name in self.entry['sets']},
            'reads':reads,
            'reading_rule':'Add generation and paging arguments. Source reads stop at the named last record; '
                'reduce the final limit to the remaining record count. These lexical boundaries are not proof of semantics.',
            'completion_rule':'Only delivered pages in the final context count. A staged checkpoint is not accepted coverage.'}

    def inputs(self,state):
        from . import edit_contract
        parents=state['sessions'][self.entry['id']]['parents']
        handoffs=self.workflow.handoffs(state)
        return {'investigation-assignment':self.assignment(),
                'investigation-contract':edit_contract.investigation_reference(),
                **{key:value for key,value in handoffs.items()
                   if key in {'investigation-handoff-'+p for p in parents}}}

    def citation(self, arguments, state):
        contract.value(arguments['kind'] in ('record','ram'),'kind',{'enum':['record','ram']})
        catalog=self.workflow.config['catalog']; session=state['sessions'][self.entry['id']]
        reached={catalog['units'][u]['evidence_id'] for receipt in self.workflow.journal(session) for u in receipt['units']}
        scope='analogue:'+str(arguments['analogue_index']) if 'analogue_index' in arguments else 'local'
        records=[]
        for key in sorted(reached):
            row=catalog['evidence'][key]
            if row['kind']!=arguments['kind']:continue
            if row['kind']=='record':
                if row['record_id']!=arguments['record_id'] or row['scope']!=scope:continue
            elif row['fact']['record_id']!=arguments['record_id']:continue
            records.append({'id':key,'sha256':row['content_sha256']})
        require(records,'INVESTIGATION_CITATION_INVALID')
        return {'generation':arguments['generation'],
            **evidence_views.page(records,arguments.get('offset',0),arguments.get('limit',40)),
            'coverage':'Provisional read citations; final native audit must confirm actual post-compaction delivery.'}

    def dispatch(self, operation, arguments, role):
        require(role=='implementer','INVESTIGATION_READ_ONLY')
        require(operation in contract.investigating(),'INVESTIGATION_READ_ONLY')
        contract.check(arguments,contract.investigating()[operation])
        flow=self.workflow
        with flow.controller.editor.transaction(write=True):
            state=flow.checked()
            require(state['active']==self.entry['id'],'INVESTIGATION_TRANSITION_INVALID')
            generation=flow.config['catalog']['binding']['generation']
            require(arguments.get('generation',generation)==generation,'STALE_GENERATION')
            if operation=='checkpoint':
                return flow.stage(self.entry['id'],{k:arguments[k] for k in ('claims','decisions')})
            if operation=='citation':return self.citation(arguments,state)
            if operation=='status':
                return {**flow.controller.status(role),'investigation':{
                    'entry_id':self.entry['id'],'assignment_input_id':'investigation-assignment',
                    'completion':'pending_native_audit','read_only':True}}
            if operation=='input' and arguments['input_id'].startswith('investigation-'):
                inputs=self.inputs(state);key=arguments['input_id']
                require(key in inputs,'INPUT_UNKNOWN')
                return input_page(inputs[key],key,generation,arguments.get('offset',0),arguments.get('limit',4096))
            if operation=='inputs':
                capture=flow.controller.editor.model(generation).capture
                items=[declared_inputs.metadata(i) for i in declared_inputs.load(capture)['items']]
                items.extend({'id':key,'kind':'investigation','generation':generation,
                              'sha256':inv.identity(value)} for key,value in self.inputs(state).items())
                return {'generation':generation,**evidence_views.page(items,arguments.get('offset',0),arguments.get('limit',12))}
            # No image allowance is priced for this phase. Text inputs and the
            # existing native evidence views use the normal generation checks.
            return flow.controller.dispatch(operation,arguments,'reviewer')

    def record_delivery(self, operation, arguments, response):
        self.workflow.delivered(self.entry['id'],{'operation':operation,'arguments':arguments},response)
