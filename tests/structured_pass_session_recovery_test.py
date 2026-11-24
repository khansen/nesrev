"""Recovery accepts only a finished native slot; checkpoints remain immutable."""
import copy
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import structured_pass_fixture as fixture
from structured_pass import bridge,corridor_inventory,investigation as inv,session_plan
from structured_pass.investigation_workflow import Workflow

class SessionRecoveryTests(unittest.TestCase):
    def setUp(self):
        if not os.environ.get('STRUCTURED_PASS_XASM'):self.skipTest('Pinned assembler required')
        temporary=tempfile.TemporaryDirectory(dir=ROOT/'tmp');self.addCleanup(temporary.cleanup)
        self.root=Path(temporary.name).resolve();self.c=fixture.prepare(self.root/'fixture')
        self.g=self.c.editor.state['current'];model=self.c.editor.model(self.g)
        inventory=corridor_inventory.build(model,{'roots':[{'symbol':'Entry','through_return':'RTS'}],
            'vector':'Cell','ram_ranges':[[0,2047]],'analogues':[]})
        catalog=inv.catalog(model,self.g,inventory)
        self.flow=Workflow.prepare(self.root/'flow',self.c,inventory,
            [{'id':name,'sets':list(catalog['sets'])} for name in ('first','second')],
            handoff_dependencies={'first':[],'second':['first']})
        self.flow.begin('first','slot',{})
        records=sorted({v['record_id'] for v in catalog['evidence'].values() if v['kind']=='record'})[:1]
        request={'operation':'navigate','arguments':{'generation':self.g,'view':'edit','record_id':records}}
        page=self.c.dispatch(request['operation'],request['arguments'],'implementer');stream=io.StringIO()
        bridge.emit(None,1,{'result':{'content':[{'type':'text','text':json.dumps(page)}]}},stream,'navigate')
        result=json.loads(stream.getvalue())['result'];self.flow.delivered('first',request,result)
        self.audit={'session_id':'native-first','last_compaction':-1,'calls':[
            {'call_id':'call-1','position':1,'arguments':request,'output':result}]}
        self.flow.stage('first',{'claims':[{'id':'unknown','kind':'unknown','subject':'Synthetic corridor',
            'statement':'Ownership is unresolved.','confidence':'unknown','citations':[],
            'searched_sets':[],'unknowns':'Further evidence required.','contrary':[]}],'decisions':[]})
        self.pair=self.root/'pair';folder=self.pair/'turns/slot';folder.mkdir(parents=True)
        self.process=folder/'process.json'
        self.process.write_text(json.dumps({'exit_code':0,'processes_reconciled':True,'processes':[]}))
        self.config={'session_plan':{'workflow':str(self.flow.root)}}
        self.row={'id':'slot','entry_id':'first','profile':'unused-native-profile','result':'running'}

    def complete(self):
        with patch.object(session_plan,'finished_audit',return_value=self.audit),\
                patch.object(session_plan.session_slots,'finish'),\
                patch('subprocess.Popen',side_effect=AssertionError('Recovery must not spawn')):
            return session_plan.complete(self.pair,self.config,self.row)

    def test_crash_after_finished_client_recovers_exactly_one_partial_checkpoint(self):
        self.assertEqual(self.complete()['completion'],'partial')
        original=(self.flow.root/'state.json').read_bytes()
        checkpoint=self.row['checkpoint_sha256']
        self.row['result']='running'
        self.assertEqual(self.complete()['checkpoint_sha256'],checkpoint)
        self.assertEqual((self.flow.root/'state.json').read_bytes(),original)
        self.flow.begin('second','second-slot',{'first':self.audit})
        self.assertIsNotNone(json.loads((self.flow.root/'state.json').read_bytes())['sessions']['first']['accepted'])

    def test_unfinished_process_or_client_cannot_be_recovered_as_success(self):
        raw=self.process.read_bytes()
        for change in ({'exit_code':1},{'processes_reconciled':False},{'cleanup_error':'unknown survivors'}):
            self.process.write_text(json.dumps({**json.loads(raw),**change}))
            with self.subTest(change=change),self.assertRaisesRegex(ValueError,'^PAIR_RECOVERY_REQUIRED$'):
                self.complete()
        self.process.write_bytes(raw)
        with patch.object(session_plan.session_slots,'finish'),\
                patch.object(session_plan,'finished_audit',side_effect=ValueError('PAIR_RECOVERY_REQUIRED')):
            with self.assertRaisesRegex(ValueError,'^PAIR_RECOVERY_REQUIRED$'):
                session_plan.complete(self.pair,self.config,self.row)
        self.assertIsNone(json.loads((self.flow.root/'state.json').read_bytes())['sessions']['first']['accepted'])

    def test_late_compaction_cannot_recover_old_coverage(self):
        self.complete();self.audit=copy.deepcopy(self.audit);self.audit['last_compaction']=10
        with self.assertRaisesRegex(ValueError,'^INVESTIGATION_CHANGED$'):self.complete()


if __name__=='__main__':unittest.main()
