"""Additional diagnostic, run-binding and repair-input review regressions."""
import fcntl
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from structured_pass import gate_diagnostics
import structured_pass_handoff_test as handoff
import structured_pass_review_fixes_test as previous


class DiagnosticVocabularyTests(unittest.TestCase):
    def test_redaction_does_not_rescan_placeholders_or_erase_diagnostic_vocabulary(self):
        # Keep a shorter candidate inside the replacement to catch recursive
        # redaction even after bare diagnostic words are excluded.
        snippet='LDA #$00 ; fixture comment'
        model=SimpleNamespace(source=(';\n'+snippet+'\nrecords\nstatus\nsource text\n').encode(),facts={})
        log=json.dumps({'status':'fail','detail':snippet+'; see above',
                        '/private/checkout/source.asm:2: '+snippet:'evidence'})+'\n'
        log+='FAIL: bad line '+snippet+' (in block); check records\n'
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'gate.log';path.write_text(log)
            result=gate_diagnostics.explanation(path,'/private/checkout','source.asm',model)
        marker='[source text omitted; use structured records]'
        self.assertEqual(result['report'].get('status'),'fail')
        self.assertEqual(result['report']['detail'],marker+'; see above')
        self.assertEqual(result['failure_lines'],['FAIL: bad line '+marker+' (in block); check records'])
        self.assertNotIn(snippet,json.dumps(result))
        self.assertNotIn('/private/checkout',json.dumps(result))
        self.assertIn('source.asm:2: '+marker,result['report'])


class RunBindingTests(unittest.TestCase):
    setUp=handoff.HandoffTests.setUp

    def test_bound_commands_refuse_ordinary_replacement_under_review_lock(self):
        path=self.root/'.agents/current.json';state=json.loads(path.read_text())
        state.pop('structured_review');state['run_id']='ordinary-run-1'
        path.write_text(json.dumps(state));before=path.read_bytes()
        response=self.root/'response.md';response.write_text('Repair response')
        operations=[('status','--json'),('reready','--head','HEAD','--response',str(response)),
                    ('archive','--pass-id','1')]
        for args in operations:
            with self.subTest(args=args):
                handoff.command(self.root,'--expected-run-id','fixture-pass',*args,error='BRIDGE_RUN_CHANGED')
                handoff.command(self.root,'--expected-run-id','ordinary-run-1',*args,error='STRUCTURED_MODE_REQUIRED')
                self.assertEqual(path.read_bytes(),before)
        with (self.root/'.agents/structured-review.lock').open('a+b') as lock:
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            handoff.command(self.root,'--expected-run-id','fixture-pass','status','--json',error='REVIEW_STATE_BUSY')
        ordinary=handoff.command(self.root,'status','--json')
        self.assertEqual(ordinary['run_id'],'ordinary-run-1')
        self.assertEqual(path.read_bytes(),before)


class RepairInputTests(unittest.TestCase):
    setUp=previous.ReviewWorkflowTests.setUp
    edit=previous.ReviewWorkflowTests.edit
    approved_target=previous.ReviewWorkflowTests.approved_target

    def test_reready_checks_bytes_cleans_refusals_and_retains_accepted_response(self):
        published,_=self.approved_target();c=self.c
        folder=c.root/'handoff/.agents/runs'/c.config['run_id']
        state_path=c.root/'handoff/.agents/current.json';before=state_path.read_bytes()
        initial=set(folder.rglob('*'))
        for response in ('  \n\t','é'*32769):
            with self.subTest(response_bytes=len(response.encode())):
                with self.assertRaisesRegex(ValueError,'^REQUEST_SCHEMA$'):
                    c.dispatch('reready',{'response':response},'implementer')
                self.assertEqual(set(folder.rglob('*')),initial)
        with self.assertRaisesRegex(ValueError,'^REVIEW_NOT_AWAITING_REPAIR$'):
            c.dispatch('reready',{'response':'Valid but premature'},'implementer')
        self.assertEqual(set(folder.rglob('*')),initial)
        self.assertEqual(state_path.read_bytes(),before)
        c.dispatch('request-changes',{'ticket':published['review']['artifact_id'],
            'report':'Verdict: CHANGES_REQUESTED\nClarify the response.'},'reviewer')
        state=json.loads(state_path.read_text());saved=state_path.read_bytes()
        state['max_rounds']=state['round'];state_path.write_text(json.dumps(state))
        before=state_path.read_bytes();initial=set(folder.rglob('*'))
        with self.assertRaisesRegex(ValueError,'^REVIEW_ROUNDS_EXHAUSTED$'):
            c.dispatch('reready',{'response':'Valid but exhausted'},'implementer')
        self.assertEqual(state_path.read_bytes(),before)
        self.assertEqual(set(folder.rglob('*')),initial)
        state_path.write_bytes(saved)
        response='é'*32768  # Exactly the 64 KiB UTF-8 boundary.
        answer=c.dispatch('reready',{'response':response},'implementer')
        self.assertEqual(answer['status'],'READY_FOR_REREVIEW')
        accepted=json.loads(state_path.read_text())['last_response']
        self.assertTrue((c.root/'handoff'/accepted).is_file())
        self.assertEqual((c.root/'handoff'/accepted).read_bytes(),response.encode())
        self.assertEqual(list(folder.glob('response-*.md')),[])


if __name__=='__main__':unittest.main()
