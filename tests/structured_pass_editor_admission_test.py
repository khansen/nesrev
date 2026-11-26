"""Final artifacts cannot borrow reserved bytes or a previous passing price."""
import copy
import json
import math
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from types import SimpleNamespace

from structured_pass import editor_admission as admission, corridor_capacity as capacity
from structured_pass import startup_inputs, read_recipe


class EditorAdmissionTests(unittest.TestCase):
    def test_candidate_matches_the_retained_native_investigation_schema(self):
        root=Path(__file__).resolve().parents[1]
        ordinary=json.loads((root/'tests/fixtures/codex_tool_declaration.json').read_bytes())
        captured=json.loads((root/'tests/fixtures/codex_investigation_tool_declaration.json').read_bytes())
        self.assertEqual(admission.native_candidate(ordinary,'investigation'),captured)

    def setUp(self):
        self.budget=startup_inputs.allowance({'window_tokens':258400,'startup_tokens':82000,
            'lifecycle_tokens':48000,'margin_tokens':25840,'bytes_per_1000_tokens':2580})
        calls=[]
        for job,size in [('startup-operation-reference',2000),('startup-guidance-startup',2000),
                         ('editor-lean-records',4000)]:
            calls.append({'job':job,'operation':'input','arguments':{'input_id':job.removeprefix('startup-')},
                          'wire_bytes':size})
        self.actual=copy.deepcopy(calls)
        for job,size in admission.CAPS.items():
            calls.append({'job':job,'operation':'input','arguments':{},'wire_bytes':size,'reservation':True})
        self.pricing={'initial_tokens':12678,'overhead_bytes':36751,'overhead_request_bytes':1088}
        self.baseline={'charges':admission.CAPS,'calls':calls,'pricing':self.pricing,
                      'price':capacity.price(calls,self.budget,**self.pricing)}
        self.basis={'initial_tokens':7800,'framing_tokens':2000,'declaration_bytes':256}
        self.previous={k:admission.stamp(b'a'*10000) for k in ('instructions','message','native_declaration')}
        self.current=copy.deepcopy(self.previous)

    def price(self,actual=None,current=None,baseline=None):
        return admission.bound_price(baseline or self.baseline,actual or self.actual,self.budget,
                                     self.basis,current or self.current,self.previous)

    def test_instruction_message_and_declaration_growth_are_all_charged(self):
        for key in self.current:
            changed=copy.deepcopy(self.current);changed[key]=admission.stamp(b'a'*30000)
            got=self.price(current=changed)
            size=20000 if key=='native_declaration' else 20256
            self.assertEqual(got['initial_tokens'],9800+math.ceil(size/2.58))
        shrunk={k:admission.stamp(b'') for k in self.current}
        self.assertEqual(self.price(current=shrunk)['initial_tokens'],12678)

    def test_reference_reservation_does_not_subsidize_other_inputs(self):
        changed=copy.deepcopy(self.actual);changed[0]['wire_bytes']+=8192
        self.assertEqual(self.price(actual=changed)['price'],self.price()['price'])
        changed[0]['wire_bytes']+=1
        with self.assertRaisesRegex(ValueError,'PAIR_INPUTS_CHANGED'):self.price(actual=changed)
        changed=copy.deepcopy(self.actual);changed[1]['wire_bytes']+=1000
        self.assertGreater(self.price(actual=changed)['price']['estimated_tokens'],self.price()['price']['estimated_tokens'])
        for key in admission.CAPS:
            reduced=copy.deepcopy(self.baseline);reduced['charges'][key]-=1
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,'PAIR_INPUTS_CHANGED'):
                self.price(baseline=reduced)

    def test_missing_startup_or_edit_job_and_false_price_refuse(self):
        for index in range(len(self.actual)):
            changed=copy.deepcopy(self.actual);changed.pop(index)
            with self.subTest(index=index),self.assertRaisesRegex(ValueError,'PAIR_INPUTS_CHANGED'):
                self.price(actual=changed)
        changed=copy.deepcopy(self.baseline);changed['price']['allowance_bytes']+=1
        with self.assertRaisesRegex(ValueError,'PAIR_INPUTS_CHANGED'):self.price(baseline=changed)

    def test_final_growth_can_exhaust_margin_without_changing_any_reserve(self):
        changed=copy.deepcopy(self.actual);changed[-1]['wire_bytes']=270000
        result=self.price(actual=changed)['price']
        self.assertFalse(result['passed'])
        self.assertEqual(result['margin_tokens'],25840)
        self.assertEqual(result['lifecycle_tokens'],48000)

    def test_launch_rechecks_artifacts_envelope_price_and_native_pin(self):
        for call in self.actual:
            if call['job']=='editor-lean-records':call['arguments']['input_id']='investigation-edit-targets'
            call['arguments'].update(generation='G-test',offset=0,
                limit=40 if call['job']=='editor-lean-records' else 8192)
            call['result']={'generation':'G-test','next_offset':None,'records':[{}]}
        self.actual.insert(0,{'job':'startup-status','operation':'status','arguments':{},'wire_bytes':100,
                             'result':{'generation':'G-test'}})
        self.baseline['calls']=copy.deepcopy(self.actual)+[c for c in self.baseline['calls'] if c.get('reservation')]
        self.baseline['price']=capacity.price(self.baseline['calls'],self.budget,**self.pricing)
        recipe={'reads':[{'operation':'input','arguments':{'input_id':'investigation-edit-targets','limit':40}}]}
        ids=['operation-reference','guidance-startup']
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder); (root/'plan.json').write_text('{}')
            profile=root/'profile';profile.mkdir()
            captured={**self.current,'budget':self.budget,'native_declaration_sha256':'new','startup_inputs':ids}
            totals=self.price()
            report={'schema':'editor-admission-v1','session':str(root),'profile':str(profile),
                'plan_sha256':admission.sha(root/'plan.json'),'generation':'G-test','edit_targets':['s1'],
                'artifacts':captured,'baseline':self.baseline,'initial_basis':self.basis,
                'previous_artifacts':self.previous,'actual_calls':self.actual,'native_envelope':[],
                'read_recipe':recipe,'argument_check':read_recipe.verify(self.actual,recipe,ids),
                'transition_wire_bytes':2000,**totals}
            config={'input_assembly':str(profile/'inputs/assembly.json'),'tool_declaration_sha256':'new'}
            controller=SimpleNamespace(root=root,checked_editor=lambda:{'investigation_gate':{'root':str(root)}},
                                       editor=SimpleNamespace(state={'pass_start_generation':'G-test'}))
            flow=SimpleNamespace(root=root,config={'edit_targets':['s1']},editor_recipe=lambda:recipe,
                                 prepared_transition_wire_bytes=lambda:2000)
            def save(value): (root/'editor-admission.json').write_text(json.dumps(value))
            save(report)
            with patch('structured_pass.investigation_workflow.Workflow',autospec=True,return_value=flow),\
                    patch.object(admission,'artifacts',return_value=captured):
                admission.verify(controller,config)
                for field in ('instructions','message','native_declaration','budget','edit_targets','price','argument_check','read_recipe','transition_wire_bytes'):
                    changed=copy.deepcopy(report)
                    if field=='edit_targets':changed[field]=['s2']
                    elif field=='price':changed[field]['passed']=False
                    elif field=='argument_check':changed[field]['passed']=False
                    elif field=='read_recipe':changed[field]['reads']=[]
                    elif field=='transition_wire_bytes':changed[field]+=1
                    elif field=='budget':changed['artifacts'][field]['response_bytes']+=1
                    else:changed['artifacts'][field]['sha256']='changed'
                    save(changed)
                    with self.subTest(field=field),self.assertRaisesRegex(ValueError,'PAIR_INPUTS_CHANGED'):
                        admission.verify(controller,config)
                save(report)
                with self.assertRaisesRegex(ValueError,'CODEX_TOOL_DECLARATION_CHANGED'):
                    admission.verify(controller,{**config,'tool_declaration_sha256':'old'})

    def test_pair_and_initial_native_launch_require_editor_gate(self):
        import structured_pair_launcher as pair
        import structured_codex_client as client
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder);(root/'editor').mkdir()
            state={'declared_inputs_sha256':'x','investigation_gate':{'root':str(root)}}
            (root/'editor/state.json').write_text(json.dumps(state))
            left={'role':'implementer','task':'Task','items':[],'manifest_sha256':'x','pass_id':1,
                  'objective':'Synthetic','historical_label':'Historical','startup':{'budget':self.budget}}
            right={**left,'role':'reviewer'}
            (root/'left.json').write_text(json.dumps(left));(root/'right.json').write_text(json.dumps(right))
            config={'session':str(root),'input_assembly':str(root/'left.json'),
                    'initial_editor_sha256':client.sha(root/'editor/state.json')}
            controller=SimpleNamespace(checked_editor=lambda:state,editor=SimpleNamespace(state=state))
            with patch.object(admission,'verify',side_effect=ValueError('PAIR_INPUTS_CHANGED')) as gate:
                with self.assertRaisesRegex(ValueError,'PAIR_INPUTS_CHANGED'):
                    pair.check_inputs(controller,config,{'roles':{'reviewer':{'input_assembly':str(root/'right.json')}}},b'Task')
                gate.assert_called_once()
                with patch('structured_pass.launcher.Corridor',return_value=controller):
                    with self.assertRaisesRegex(ValueError,'PAIR_INPUTS_CHANGED'):client.check_initial_editor(config)
                self.assertEqual(gate.call_count,2)


if __name__=='__main__':unittest.main()
