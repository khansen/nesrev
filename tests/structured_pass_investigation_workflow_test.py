"""Real service generations, crash boundaries and finalized native receipts."""
import copy
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from structured_pass import bridge, corridor_inventory, investigation as inv, service
from structured_pass.investigation_workflow import Workflow, reconcile, output_text
from structured_pass.investigation_service import Session
from structured_pass.publication import immutable_file
import structured_pass_fixture as fixture

ROOT = Path(__file__).resolve().parents[1]


class WorkflowTests(unittest.TestCase):
    def setUp(self):
        if not os.environ.get('STRUCTURED_PASS_XASM'): self.skipTest('Pinned producer required')
        (ROOT/'tmp').mkdir(exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(dir=ROOT/'tmp'); self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name); self.c = fixture.prepare(self.root)
        self.g = self.c.editor.state['current']; self.model = self.c.editor.model(self.g)
        spec = {'roots':[{'symbol':'Entry','through_return':'RTS'}], 'vector':'Cell',
                'ram_ranges':[[0,2047]],'analogues':[]}
        self.inventory = corridor_inventory.build(self.model, spec)
        catalog = inv.catalog(self.model, self.g, self.inventory)
        # Two authorized contexts can share a partition. A partial checkpoint
        # remains partial; only the final union admits editing.
        assignments = [{'id':name,'sets':list(catalog['sets'])} for name in ('first','second')]
        self.flow = Workflow.prepare(self.root/'workflow', self.c, self.inventory, assignments)
        self.audits = {}

    def begin(self, ident):
        receipt = self.flow.begin(ident, 'thread-'+ident, self.audits)
        self.audits[ident] = {'session_id':receipt['session_id'],'last_compaction':-1,'calls':[]}

    def deliver(self, ident, records):
        request = {'operation':'navigate','arguments':{'generation':self.g,'view':'edit','record_id':records}}
        answer = self.c.dispatch(request['operation'], request['arguments'], 'implementer')
        output = io.StringIO()
        bridge.emit(None, len(self.audits[ident]['calls'])+1,
            {'result':{'content':[{'type':'text','text':json.dumps(answer)}]}}, output, 'navigate')
        result = json.loads(output.getvalue())['result']
        self.flow.delivered(ident, request, result)
        calls = self.audits[ident]['calls']
        calls.append({'call_id':'call-'+str(len(calls)), 'position':2*len(calls)+1,
                      'arguments':json.dumps(request),'output':json.dumps(result)})

    def unknown(self):
        return {'claims':[{'id':'uncertain','kind':'unknown','statement':'Do not name without proof.',
            'subject':'Synthetic corridor',
            'confidence':'unknown','citations':[],'searched_sets':[],
            'unknowns':'Naming requires independent evidence.','contrary':[]}], 'decisions':[]}

    def records(self):
        return sorted({r['record_id'] for r in self.flow.config['catalog']['evidence'].values()
                       if r['kind']=='record'})

    def finish(self, ident):
        draft = self.flow.stage(ident, self.unknown())
        self.assertEqual(draft['completion'], 'pending_native_audit')
        return self.flow.finalize(ident, self.audits[ident])

    def test_partial_restart_checked_union_then_real_editor_preview(self):
        records = self.records(); cut = len(records)//2
        self.begin('first'); self.deliver('first', records[:cut])
        saved = self.finish('first'); self.assertEqual(saved['completion'],'partial')
        self.flow = Workflow(self.root/'workflow')
        self.begin('second'); self.deliver('second', records[cut:])
        self.finish('second')
        import structured_codex_client as client
        before=json.loads(self.c.editor.state_path.read_bytes())
        admission={'session':str(self.c.root),'service_profile':'corridor',
            'initial_editor_sha256':client.sha(self.c.editor.state_path),
            'initial_editor_identity':inv.identity(before)}
        receipt = self.flow.admit_editor(self.audits)
        client.check_initial_editor(admission)
        path=self.c.editor.state_path;raw=path.read_bytes();changed=json.loads(raw)
        changed['unexpected']='not the admission receipt'
        service.write_json(path,changed)
        try:
            with self.assertRaisesRegex(ValueError,'^CODEX_HANDOFF_CHANGED$'):
                client.check_initial_editor(admission)
        finally:path.write_bytes(raw)
        self.assertEqual(len(receipt['checkpoints']),2)
        from structured_pass.launcher import Corridor
        editor = Corridor(self.c.root)
        status=editor.dispatch('status',{},'implementer')
        self.assertEqual(status['investigation']['verification'],receipt)
        handoff=editor.dispatch('input',{'generation':self.g,'input_id':'investigation-handoff-first'},'implementer')
        self.assertEqual(json.loads(handoff['text'])['completion'],'partial')
        from structured_pass_edit_records_test import decode,full_inputs
        records=[];offset=0
        while offset is not None:
            page=editor.dispatch('input',{'generation':self.g,'input_id':'investigation-edit-targets',
                                         'offset':offset,'limit':2},'implementer')
            records.extend(decode(page));offset=page['next_offset']
        self.assertEqual(records,[full_inputs(self.model,r) for r in self.flow.config['edit_targets']])
        preview = editor.dispatch('preview',{'generation':self.g,
            'operations':fixture.rename_ops(editor,self.g)},'implementer')
        self.assertIn('preview_digest',preview)

    def test_no_mutation_during_investigation_or_missing_coverage(self):
        self.begin('first')
        for operation in ('preview','confirm','validate','publish','start_chain','closeout','request-changes'):
            with self.subTest(operation=operation), self.assertRaisesRegex(ValueError,'^INVESTIGATION_READ_ONLY$'):
                self.c.dispatch(operation,{},'implementer')
        self.finish('first'); self.begin('second'); self.finish('second')
        with self.assertRaisesRegex(ValueError,'^INVESTIGATION_COVERAGE_INCOMPLETE$'):
            self.flow.admit_editor(self.audits)

    def test_unreceived_changed_or_reordered_outputs_do_not_count(self):
        self.begin('first'); self.deliver('first', self.records()[:1]); self.deliver('first',self.records()[1:])
        self.flow.stage('first', self.unknown())
        for corruption in ('missing','output','arguments','repeat'):
            bad = copy.deepcopy(self.audits['first'])
            if corruption=='missing': bad['calls'].pop()
            elif corruption=='output': bad['calls'][0]['output']=json.dumps({'content':[{'type':'text','text':'{}'}]})
            elif corruption=='arguments': bad['calls'][0]['arguments']='{}'
            else: bad['calls'][1]['call_id']=bad['calls'][0]['call_id']
            with self.subTest(corruption=corruption), self.assertRaisesRegex(ValueError,'^INVESTIGATION_AUDIT_MISMATCH$'):
                self.flow.finalize('first',bad)
        self.assertIsNone(json.loads((self.flow.root/'state.json').read_text())['sessions']['first']['accepted'])

    def test_crash_after_blob_before_pointer_leaves_no_completion(self):
        self.begin('first'); self.deliver('first',self.records()); self.flow.stage('first',self.unknown())
        with patch.object(service,'write_json',side_effect=OSError('simulated atomic pointer failure')):
            with self.assertRaisesRegex(OSError,'pointer failure'):
                self.flow.finalize('first',self.audits['first'])
        restored=Workflow(self.flow.root)
        with self.assertRaisesRegex(ValueError,'^INVESTIGATION_TRANSITION_INVALID$'):
            restored.begin('second','thread-second',self.audits)
        self.assertEqual(restored.finalize('first',self.audits['first'])['completion'],'complete')

    def test_final_compaction_invalidates_accepted_handoff(self):
        self.begin('first'); self.deliver('first',self.records()); self.finish('first')
        changed=copy.deepcopy(self.audits);changed['first']['last_compaction']=99
        with self.assertRaisesRegex(ValueError,'^INVESTIGATION_CHANGED$'):
            self.flow.begin('second','thread-second',changed)
        self.assertIsNone(json.loads((self.flow.root/'state.json').read_text())['active'])

    def test_changed_generation_capture_and_parent_refuse(self):
        self.begin('first'); self.deliver('first',self.records()); self.finish('first')
        before=(self.flow.root/'plan.json').read_bytes()
        (self.flow.root/'plan.json').write_bytes(before+b' ')
        with self.assertRaisesRegex(ValueError,'^INVESTIGATION_CHANGED$'):
            self.flow.begin('second','thread-second',self.audits)

    def test_actual_bridge_assignment_journal_and_native_text_shape(self):
        self.begin('first')
        profile=self.root/'phase';profile.mkdir()
        immutable_file(profile/'investigation-profile.json',inv.canonical({
            'workflow':str(self.flow.root),'entry_id':'first',
            'plan_sha256':inv.sha(self.flow.root/'plan.json')}))
        client=Session(profile)
        self.assertNotIn('inventory',client.assignment())
        from structured_pass import edit_contract
        contract_request={'id':0,'method':'tools/call','params':{'name':'operation','arguments':{
            'operation':'input','arguments':{'generation':self.g,'input_id':'investigation-contract','limit':8192}}}}
        output=io.StringIO()
        bridge.mcp(profile,'implementer','investigation',io.StringIO(json.dumps(contract_request)+'\n'),output)
        delivered=json.loads(output.getvalue())['result'];page=json.loads(output_text(delivered))
        self.assertIsNone(page['next_offset'])
        self.assertEqual(json.loads(page['text']),edit_contract.investigation_reference())
        self.audits['first']['calls'].append({'call_id':'contract','position':0,
            'arguments':contract_request['params']['arguments'],'output':delivered})
        for read in client.assignment()['reads']:
            arguments={'generation':self.g,**read['arguments'],'limit':40}
            if 'record_count' in read:arguments['limit']=min(40,read['record_count'])
            request={'jsonrpc':'2.0','id':1,'method':'tools/call','params':{
                'name':'operation','arguments':{'operation':read['operation'],'arguments':arguments}}}
            output=io.StringIO()
            bridge.mcp(profile,'implementer','investigation',io.StringIO(json.dumps(request)+'\n'),output)
            result=json.loads(output.getvalue())['result']
            self.assertFalse(result.get('isError'),result)
            text=output_text(result)
            calls=self.audits['first']['calls']
            calls.append({'call_id':'native-'+str(len(calls)),'position':len(calls)+1,
                'arguments':json.dumps(request['params']['arguments']),
                'output':[{'type':'input_text','text':'Wall time: 0.1 seconds\nOutput:'},
                          {'type':'input_text','text':text}]})
        self.audits['first']['session_id']='actual-native-thread'
        saved=self.finish('first')
        self.assertEqual(saved['completion'],'complete')
        self.assertEqual(saved['session_id'],'actual-native-thread')
        for malformed in ([{'type':'input_text','text':'truncated'}],
                          [{'type':'input_text','text':'wrong envelope'},{'type':'input_text','text':'{}'}]):
            with self.assertRaisesRegex(ValueError,'^INVESTIGATION_AUDIT_MISMATCH$'):output_text(malformed)

    def test_stage_refuses_bad_claim_before_client_finishes(self):
        self.begin('first');submission=self.unknown()
        submission['claims'][0]['confidence']='proven'
        with self.assertRaisesRegex(ValueError,'^INVESTIGATION_CITATION_INVALID$'):
            self.flow.stage('first',submission)
        self.assertIsNone(json.loads((self.flow.root/'state.json').read_text())['sessions']['first']['staged'])
        self.assertEqual(self.flow.stage('first',self.unknown())['completion'],'pending_native_audit')

    def test_per_partition_wire_cap_cannot_borrow_the_aggregate(self):
        from structured_pass.investigation_workflow import input_wire_bytes
        self.begin('first');submission=self.unknown()
        submission['claims'][0]['statement']='Bounded uncertainty. '*1800
        # This body fits the aggregate but exceeds this partition's share.
        candidate=inv.checkpoint(self.flow.config['catalog'],self.flow.entry('first'),submission,[],
            {'session_id':'thread-first','last_compaction':-1,'deliveries':[]},maximum_bytes=65536)
        size=input_wire_bytes(inv.handoff(candidate,self.flow.config['catalog']),
                              'investigation-handoff-first',self.g)
        self.assertGreater(size,self.flow.config['checkpoint_caps']['first'])
        self.assertLess(size,self.flow.config['checkpoint_bytes'])
        with self.assertRaisesRegex(ValueError,'^INVESTIGATION_CHECKPOINT_TOO_LARGE$'):
            self.flow.stage('first',submission)
        state=json.loads((self.flow.root/'state.json').read_bytes())
        self.assertIsNone(state['sessions']['first']['staged'])

    def test_editor_admission_recovers_interrupted_second_pointer(self):
        self.begin('first');self.deliver('first',self.records());self.finish('first')
        self.begin('second');self.finish('second')
        with patch.object(self.flow.controller.editor,'save',side_effect=OSError('editor pointer interrupted')):
            with self.assertRaisesRegex(OSError,'pointer interrupted'):self.flow.admit_editor(self.audits)
        restored=Workflow(self.flow.root)
        result=restored.admit_editor(self.audits)
        self.assertEqual(restored.admit_editor(self.audits),result)

    def test_editor_transition_cannot_exceed_its_priced_cap(self):
        from structured_pass import investigation_workflow as workflow
        self.begin('first');self.deliver('first',self.records());self.finish('first')
        self.begin('second');self.finish('second')
        original=workflow.input_wire_bytes
        def oversized(value,ident,generation):
            return 8193 if ident=='investigation-transition' else original(value,ident,generation)
        with patch.object(workflow,'input_wire_bytes',side_effect=oversized):
            with self.assertRaisesRegex(ValueError,'^INVESTIGATION_CHECKPOINT_TOO_LARGE$'):
                self.flow.admit_editor(self.audits)
        self.assertFalse(json.loads((self.flow.root/'state.json').read_bytes())['editing'])
        self.assertFalse(self.flow.controller.editor.state['investigation_gate']['editing_admitted'])
        self.assertTrue(self.flow.admit_editor(self.audits))

    def test_declared_conflict_preserves_handoff_but_stops_editor(self):
        self.begin('first');self.deliver('first',self.records());self.finish('first')
        self.begin('second');submission=self.unknown()
        submission['claims'][0]['conflicts']=[{'partition_id':'first','claim_id':'uncertain'}]
        self.flow.stage('second',submission);self.flow.finalize('second',self.audits['second'])
        with self.assertRaisesRegex(ValueError,'^INVESTIGATION_CONFLICT$'):self.flow.admit_editor(self.audits)
        self.assertIsNotNone(json.loads((self.flow.root/'state.json').read_bytes())['sessions']['second']['accepted'])

    def test_unknown_dependency_refuses_before_publication(self):
        self.begin('first');submission=self.unknown()
        submission['claims'][0]['dependencies']=[{'partition_id':'unplanned','claim_id':'missing'}]
        with self.assertRaisesRegex(ValueError,'^INVESTIGATION_CITATION_INVALID$'):
            self.flow.stage('first',submission)


if __name__=='__main__': unittest.main()
