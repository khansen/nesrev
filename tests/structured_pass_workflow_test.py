#!/usr/bin/env python3
"""Synthetic workflow, immutable review, bounded previews and budget regressions."""
import copy
import io
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from structured_pass import service, paging, producer, subscription_client
from structured_pass.rename_service import comments
from structured_pass.retained_service import RetainedReviewService
from structured_pass.usage_budget import Budget
from structured_pass.bridge import mcp
from structured_pass_fixture import prepare, rename_ops, closeout_ops, SOURCE


class WorkflowTests(unittest.TestCase):
    def setUp(self):
        if not os.environ.get('STRUCTURED_PASS_XASM'):self.skipTest('Pinned producer required')
        (ROOT/'tmp').mkdir(exist_ok=True)
        self.temp=tempfile.TemporaryDirectory(prefix='structured-test-',dir=ROOT/'tmp')
        self.addCleanup(self.temp.cleanup);self.root=Path(self.temp.name)
        self.controller=prepare(self.root)

    def edit(self,operations):
        c=self.controller;g=c.editor.state['current']
        p=c.dispatch('preview',{'generation':g,'operations':operations},'implementer')
        self.assertLessEqual(len(json.dumps(p).encode()),paging.MAX_BYTES)
        cid=c.dispatch('confirm',{'generation':g,'preview_digest':p['preview_digest']},'implementer')['candidate']
        v=c.dispatch('validate',{'cid':cid},'implementer')
        self.assertEqual(v['status'],'validated',v)
        self.assertTrue(v['reference_prg_parity']);self.assertTrue(v['semantic_properties']['passed'])
        return c.dispatch('publish',{'cid':cid},'implementer')

    def test_rename_comment_only_repair_and_reopened_review(self):
        c=self.controller;g=c.editor.state['current'];published=self.edit(rename_ops(c,g))
        g=published['generation'];model=c.editor.model(g);comment=comments(model)[0]
        repaired=self.edit([{'kind':'comment_replace','record_id':comment['record_id'],
            'preimage':comment['preimage_sha256'],'text':'; Padding bytes intentionally repeat.',
            'reason':'Synthetic comment-only repair'},*closeout_ops(c,g)])
        c.dispatch('approve',{'ticket':repaired['review']['artifact_id'],
            'report':'Verdict: APPROVED\n\nSynthetic lifecycle only; quality gates are simulated.'},'reviewer')
        closed=c.dispatch('closeout',{},'implementer')
        self.assertTrue((c.root/'handoff'/closed['archive']).is_file())
        from structured_pass.application import apply
        from structured_pass_fixture import git
        target=self.root/'target'
        git(self.root/'repo','clone','-q','--no-hardlinks',str(self.root/'repo'),str(target))
        reference=target/c.editor.reference;reference.parent.mkdir(parents=True,exist_ok=True)
        shutil.copy2(self.root/'repo'/c.editor.reference,reference)
        git(target,'checkout','-qb','projects')
        # The disposable application target has its own checkout. An unrelated intervening commit must survive application.
        (target/'unrelated.txt').write_text('Keep this work.\n')
        git(target,'add','unrelated.txt');git(target,'commit','-qm','Unrelated fixture change')
        parent=git(target,'rev-parse','HEAD')
        git(target,'config','user.name','Fixture');git(target,'config','user.email','fixture@example.invalid')
        planned=apply(c.root,target)
        self.assertEqual(planned['status'],'checked')
        applied=apply(c.root,target,commit=True)
        self.assertFalse(applied['pushed']);self.assertEqual(applied['head'],parent)
        self.assertEqual(apply(c.root,target,commit=True),applied)
        artifact=repaired['review']['artifact_id']
        # Remove every editable/certification input. Only the immutable store remains.
        for name in ('session','capture','repo','inputs','target'):shutil.rmtree(self.root/name)
        reader=RetainedReviewService.from_publication(self.root/'review',self.root/'store',artifact)
        edges=reader.config['artifacts'];self.assertEqual(len(edges),3)
        for before,after in zip(edges,edges[1:]):
            page=reader.review(after,before)
            self.assertEqual(page['generation'],after)
            self.assertNotIn('acceptance_fixture_check',page)
        for state in edges:
            result=reader.reassemble(state)
            self.assertTrue(result['reference_prg_parity'],result)
        requests=[{'jsonrpc':'2.0','id':i,'method':'tools/call','params':{'name':'operation','arguments':{
            'operation':op,'arguments':args}}} for i,(op,args) in enumerate((
                ('publish',{'cid':'C1'}),('status',{})),1)]
        output=io.StringIO();mcp(self.root/'review','reviewer','retained',
            input_stream=io.StringIO(''.join(json.dumps(r)+'\n' for r in requests)),output_stream=output)
        replies=output.getvalue();self.assertIn('REVIEW_READ_ONLY',replies);self.assertIn('"id": 2',replies)

    def test_named_forbidden_path_and_error_reset(self):
        c=self.controller;g=c.editor.state['current']
        preview=c.editor.preview(g,rename_ops(c,g));cid=c.editor.confirm(g,preview['preview_digest'])['candidate']
        with patch.object(type(c.editor),'inventory_result',side_effect=service.ServiceError('FORBIDDEN_PATH',paths=['projects/sample/protected.csv'])):
            failed=c.editor.validate(cid)
        self.assertEqual(failed['error'],'FORBIDDEN_PATH')
        self.assertEqual(failed['error_details']['paths'],['projects/sample/protected.csv'])
        preview=c.editor.preview(g,rename_ops(c,g),cid=cid);c.editor.confirm(g,preview['preview_digest'])
        repaired=c.editor.validate(cid)
        self.assertEqual(repaired['status'],'validated',repaired)
        self.assertIsNone(repaired['error_details']);self.assertEqual(repaired['revision'],1)

    def test_malformed_bridge_requests_do_not_kill_stream(self):
        calls=['not json\n',json.dumps({'jsonrpc':'2.0','id':1})+'\n']
        for i,operations in enumerate((['x'],{'kind':'rename'}),2):
            calls.append(json.dumps({'jsonrpc':'2.0','id':i,'method':'tools/call','params':{'name':'operation',
                'arguments':{'operation':'preview','arguments':{'generation':self.controller.editor.state['current'],'operations':operations}}}})+'\n')
        calls.append(json.dumps({'jsonrpc':'2.0','id':5,'method':'tools/call','params':{'name':'operation','arguments':{'operation':'status','arguments':{}}}})+'\n')
        output=io.StringIO();mcp(self.controller.root,'implementer','corridor',input_stream=io.StringIO(''.join(calls)),output_stream=output)
        lines=[json.loads(s) for s in output.getvalue().splitlines()]
        self.assertEqual(len(lines),5);self.assertEqual(lines[0]['error']['code'],-32700)
        self.assertEqual(lines[-1]['id'],5);self.assertIn('REQUEST_SCHEMA',output.getvalue())


class CheapRegressions(unittest.TestCase):
    def test_subscription_workspace_contains_only_pinned_reference_media(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);prompts=root/'prompts';prompts.mkdir()
            for role in ('implementer','reviewer'):(prompts/(role+'.md')).write_text('Use the bridge only.\n')
            media=root/'reference.png';media.write_bytes(b'\x89PNG\r\n\x1a\nfixture')
            workspaces=root/'workspaces';workspaces.mkdir()
            with patch.object(subscription_client,'Corridor') as corridor, patch.object(subscription_client.tempfile,'mkdtemp',return_value=str(workspaces)):
                corridor.return_value.editor.state={'candidates':{}}
                config=subscription_client.prepare(root/'launch',root/'session',prompts,
                    model='test-model',effort='test-effort',client=sys.executable,interpreter=sys.executable,
                    heavy_lock=root/'heavy.lock',media=[media])
                self.assertFalse(json.loads((root/'launch'/'budget.json').read_text())['authorized'])
                self.assertEqual(subscription_client.verify(root/'launch'),config)
                workspace=Path(config['roles']['implementer']['workspace'])
                (workspace/'source-model.json').write_text('Unexpected source capture')
                with self.assertRaisesRegex(ValueError,'CLIENT_WORKSPACE_NOT_EMPTY'):
                    subscription_client.verify(root/'launch')
                (workspace/'source-model.json').unlink()
                (workspace/'reference.png').write_bytes(b'changed')
                with self.assertRaisesRegex(ValueError,'LAUNCH_CONFIGURATION_CHANGED'):
                    subscription_client.verify(root/'launch')

    def test_large_preview_pages_preserve_every_use(self):
        records=[{'kind':'bound_use','reference_id':'r'+str(i),'record_id':'s'+str(i),'context':'x'*1200} for i in range(100)]
        offset=0;seen=[]
        while offset is not None:
            result=paging.page(records,offset,40)
            self.assertLess(len(json.dumps(result).encode()),paging.MAX_BYTES)
            seen+=result['records'];offset=result['next_offset']
        self.assertEqual(seen,records)
        with self.assertRaisesRegex(ValueError,'PREVIEW_ITEM_TOO_LARGE'):paging.page([{'text':'x'*paging.MAX_BYTES}])

    def test_actual_response_count_and_interrupted_resume(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);service.write_json(root/'budget.json',{'configuration_sha256':'pin','authorized':True,
                'max_responses':100,'max_seconds':100,'deadline':None,'runs':[]})
            budget=Budget(root,'pin');reservation=budget.reserve('implementer',30)
            events=[{'type':'assistant','message':{'id':'r'+str(i)}} for i in range(27)]
            events += [events[-1],{'type':'result','num_turns':76,'subtype':'success'}]
            result=budget.finish(reservation['id'],events)
            self.assertEqual(result['charged'],27);self.assertEqual(result['client_num_turns'],76)
            reservation=budget.reserve('reviewer',30)
            partial=[{'type':'assistant','message':{'id':'new-response'}}]
            budget.observe(reservation['id'],partial[0])
            # A fresh owner sees the persisted response even before finish.
            self.assertEqual(json.loads((root/'budget.json').read_text())['runs'][-1]['charged'],1)
            self.assertEqual(budget.finish(reservation['id'],partial)['charged'],1)
            with self.assertRaisesRegex(ValueError,'BUDGET_HALTED'):budget.reserve('reviewer',30)
            grant=budget.extend(1,0,'Owner resolves incomplete invocation')
            self.assertEqual(grant['charged_responses_preserved'],28)
            reservation=budget.reserve('reviewer',30)
            # Replayed stream messages from a resume are not charged twice.
            resumed=partial+[{'type':'assistant','message':{'id':'after-resume'}},{'type':'result','num_turns':62}]
            self.assertEqual(budget.finish(reservation['id'],resumed)['charged'],1)
            self.assertEqual(budget.reserve('implementer',30)['reserved'],30)


if __name__=='__main__':unittest.main()
