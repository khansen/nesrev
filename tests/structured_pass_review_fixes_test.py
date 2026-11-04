"""Regression cases for independent review findings; simulated gates, real producer."""
import io
import json
from contextlib import contextmanager
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from structured_pass import application, gate_diagnostics, paging, producer
from structured_pass.bridge import mcp
from structured_pass.launcher import Corridor
from structured_pass.model import certify
from structured_pass.navigation import Navigation
from structured_pass.retained_service import RetainedReviewService
from structured_pass_fixture import prepare, rename_ops, closeout_ops, git


class DiagnosticTests(unittest.TestCase):
    def test_source_snippets_are_redacted_in_every_text_channel(self):
        model=SimpleNamespace(source=b'Cell .EQU 16\nLDA #Cell\nRTS\n',facts={})
        prefix='FAIL: /private/checkout/projects/sample/asm/sample.asm:2: LDA #Cell'
        for log in (prefix+'\n',json.dumps({'summary':prefix,'nested':[prefix],prefix:'detail'})+'\n'):
            with self.subTest(log=log),tempfile.TemporaryDirectory() as tmp:
                path=Path(tmp)/'log';path.write_text(log)
                result=gate_diagnostics.explanation(path,'/private/checkout','projects/sample/asm/sample.asm',model)
                rendered=json.dumps(result)
                self.assertNotIn('LDA #Cell',rendered)
                self.assertNotIn('/private/checkout',rendered)
                self.assertIn('source text omitted',rendered)
                self.assertIn('projects/sample/asm/sample.asm',rendered)


class AnonymousNavigationTests(unittest.TestCase):
    def test_producer_anonymous_chains_are_navigable_by_record(self):
        if not os.environ.get('STRUCTURED_PASS_XASM'):self.skipTest('Pinned producer required')
        producer.EXE=Path(os.environ['STRUCTURED_PASS_XASM'])
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);source=root/'anonymous.asm';reference=root/'reference.nes'
            text=b'.ORG $8000\nJMP +\n++ NOP\n+ NOP\n- NOP\n-- NOP\nJMP -\nJMP --\nJMP +\n+ NOP\n'
            body=bytes.fromhex('4c0480eaeaeaea4c05804c06804c1080ea')
            source.write_bytes(text+b'.DB "'+b'A'*(16384-len(body))+b'"\n.END\n')
            reference.write_bytes(b'NES\x1a'+bytes([1])+bytes(11)+body+b'A'*(16384-len(body)))
            model,receipt=certify(source,root/'capture',reference)
            self.assertTrue(receipt['reference_prg_parity'])
            nav=Navigation(model)
            expected=[n for n,f in model.facts.items() if f['kind'] in
                      ('FORWARD_BRANCH_DECL_NODE','BACKWARD_BRANCH_DECL_NODE')]
            self.assertEqual(len(expected),5)
            listing=nav.query('symbols',limit=40)['records']
            self.assertEqual({r['record_id'] for r in listing},{model.ids[n] for n in expected})
            for n in expected:
                rid=model.ids[n]
                records=nav.query('records',record_id=rid)['records']
                self.assertEqual(records[0]['record_id'],rid)
                uses=nav.query('uses',record_id=rid)
                self.assertEqual(uses['total'],sum(d==n for d in model.bindings.values()))
                self.assertEqual({r['reference']['record_id'] for r in uses['records']},
                                 {model.ids[r] for r,d in model.bindings.items() if d==n})
            with self.assertRaisesRegex(ValueError,'^NAVIGATION_AMBIGUOUS_SYMBOL$'):
                nav.query('records',symbol='+')


class ReviewWorkflowTests(unittest.TestCase):
    def setUp(self):
        if not os.environ.get('STRUCTURED_PASS_XASM'):self.skipTest('Pinned producer required')
        (ROOT/'tmp').mkdir(exist_ok=True)
        self.temp=tempfile.TemporaryDirectory(prefix='review-fixes-',dir=ROOT/'tmp')
        self.addCleanup(self.temp.cleanup);self.root=Path(self.temp.name)
        self.c=prepare(self.root)

    def edit(self,ops):
        c=self.c;g=c.editor.state['current']
        preview=c.dispatch('preview',{'generation':g,'operations':ops},'implementer')
        cid=c.dispatch('confirm',{'generation':g,'preview_digest':preview['preview_digest']},'implementer')['candidate']
        answer=c.dispatch('validate',{'cid':cid},'implementer')
        self.assertEqual(answer['status'],'validated',answer)
        return c.dispatch('publish',{'cid':cid},'implementer')

    def bridge(self,operation,arguments,role='implementer',*,root=None,profile='corridor'):
        requests=[{'id':1,'method':'tools/list'}, {'id':2,'method':'tools/call',
            'params':{'name':'operation','arguments':{'operation':operation,'arguments':arguments}}}]
        output=io.StringIO()
        mcp(root or self.c.root,role,profile,io.StringIO('\n'.join(map(json.dumps,requests))),output)
        lines=output.getvalue().splitlines()
        for line in lines:self.assertLessEqual(len((line+'\n').encode()),paging.MAX_BYTES)
        listed,response=map(json.loads,lines)
        self.assertIn(operation,listed['result']['tools'][0]['inputSchema']['properties']['operation']['enum'])
        result=response['result'];answer=json.loads(result['content'][0]['text'])
        self.assertFalse(result.get('isError'),answer)
        return answer

    def approved_target(self):
        c=self.c;p=self.edit(rename_ops(c,c.editor.state['current']))
        c.dispatch('approve',{'ticket':p['review']['artifact_id'],'report':'Verdict: APPROVED\nSynthetic gates only.'},'reviewer')
        target=self.root/'target';git(self.root/'repo','clone','-q','--no-hardlinks',str(self.root/'repo'),str(target))
        ref=target/c.editor.reference;ref.parent.mkdir(parents=True,exist_ok=True)
        shutil.copy2(self.root/'repo'/c.editor.reference,ref)
        git(target,'checkout','-qb','projects')
        git(target,'config','user.name','Fixture');git(target,'config','user.email','fixture@example.invalid')
        return p,target

    def test_revocation_before_application_locks_refuses_before_writes(self):
        p,target=self.approved_target();original=Corridor.approved_state
        before=git(target,'rev-parse','HEAD')
        @contextmanager
        def revoked(controller):
            self.c.dispatch('request-changes',{'ticket':p['review']['artifact_id'],
                'report':'Verdict: CHANGES_REQUESTED\nRepair required.'},'reviewer')
            with original(controller) as approval:yield approval
        with patch.object(Corridor,'approved_state',revoked):
            with self.assertRaisesRegex(ValueError,'^REVIEW_COVERAGE_INCOMPLETE$'):
                application.apply(self.c.root,target,commit=True)
        self.assertEqual(git(target,'rev-parse','HEAD'),before)
        self.assertEqual(git(target,'status','--porcelain'),'')
        self.assertFalse((self.c.root/'application.json').exists())
        self.assertFalse(list((self.c.root/'handoff/projects').rglob('pass-*.md')))

    def test_revocation_is_locked_out_through_application_commit(self):
        p,target=self.approved_target();c=self.c;original=subprocess.run;attempts=[]
        report=c.root/'handoff/revoke.md';report.write_text('Verdict: CHANGES_REQUESTED\nRepair required.')
        state=c.root/'handoff/.agents/current.json';before=state.read_bytes()
        def run(command,*args,**kwargs):
            if isinstance(command,list) and ('project-inventory' in command or 'commit' in command):
                answer=original([sys.executable,'-B',str(ROOT/'scripts/agent_review.py'),'--repo',str(c.root/'handoff'),
                    '--expected-run-id',c.config['run_id'],'request-changes','--window',p['review']['artifact_id'],
                    '--review',str(report)],capture_output=True,text=True)
                attempts.append(answer)
                self.assertNotEqual(answer.returncode,0)
                self.assertIn('REVIEW_STATE_BUSY',answer.stderr)
                self.assertEqual(state.read_bytes(),before)
            return original(command,*args,**kwargs)
        with patch.object(application.subprocess,'run',run):
            answer=application.apply(c.root,target,commit=True)
        self.assertEqual(len(attempts),2);self.assertEqual(answer['status'],'committed')
        revoked=c.dispatch('request-changes',{'ticket':p['review']['artifact_id'],'report':report.read_text()},'reviewer')
        self.assertEqual(revoked['status'],'CHANGES_REQUESTED')

    def test_continued_window_preserves_current_scorecard_pass(self):
        c=self.c;self.edit(rename_ops(c,c.editor.state['current']))
        anchor=self.edit(closeout_ops(c,c.editor.state['current'],notes='Capacity anchor review.'))
        c.dispatch('start_chain',{'generation':anchor['generation']},'implementer')
        p=self.edit(closeout_ops(c,c.editor.state['current'],notes='Capacity continued review.'))
        reader=RetainedReviewService.from_publication(self.root/'reader',self.root/'store',p['review']['artifact_id'])
        self.assertEqual(len(reader.bodies),2)
        self.assertEqual(reader.document_pass_id(),'1')
        base,head=reader.config['artifacts']
        self.assertNotIn(reader.bodies[base]['base_artifact'],reader.bodies)
        for body in reader.bodies.values():self.assertEqual(body['review_pass_id'],'1')
        q=self.bridge('q09',{'generation':head,'names':['Capacity']},root=reader.root,profile='retained')
        rows=[m for m in q['mentions'] if m.get('path','').endswith('PROGRESS_SCORECARD.md')]
        self.assertEqual(len(rows),1);self.assertIn('Capacity continued review.',rows[0]['text'])
        page=self.bridge('review',{'generation':head,'base_generation':base,'offset':0},root=reader.root,profile='retained')
        self.assertGreater(page['total_changes'],0)
        live=self.bridge('review',{'ticket':head,'generation':head,'base_generation':base,'offset':0},role='reviewer')
        self.assertEqual(live,page)

    def test_long_report_status_and_paging_stay_readable(self):
        p=self.edit(rename_ops(self.c,self.c.editor.state['current']))
        report='Verdict: CHANGES_REQUESTED\n'+('Repair the \u2603 " \\ row.\n'*1800)
        verdict=self.bridge('request-changes',{'ticket':p['review']['artifact_id'],'report':report},role='reviewer')
        self.assertEqual(verdict['status'],'CHANGES_REQUESTED')
        status=self.bridge('status',{})
        latest=status['handoff']['latest_review']
        self.assertTrue(latest['truncated']);self.assertEqual(latest['operation'],'review_report')
        self.assertEqual(latest['sha256'],producer.digest(report.encode()))
        parts=[];offset=0
        while offset is not None:
            page=self.bridge('review_report',{'sequence':latest['sequence'],'offset':offset})
            self.assertEqual(page['offset'],offset);self.assertEqual(page['sha256'],latest['sha256'])
            parts.append(page['report']);offset=page['next_offset']
        self.assertEqual(''.join(parts),report)
        reviewer=self.bridge('review_report',{'sequence':latest['sequence']},role='reviewer')
        self.assertEqual(reviewer['report'],parts[0])
        # Reads keep the canonical report and verdict history unchanged.
        saved=json.loads((self.c.root/'handoff/.agents/current.json').read_text())
        event=saved['structured_review']['verdict_history'][-1]
        self.assertEqual((self.c.root/'handoff'/event['review_file']).read_text(),report)


if __name__=='__main__':unittest.main()
