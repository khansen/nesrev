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

    def test_scorecard_only_repair_validates_and_publishes(self):
        c=self.controller;g=c.editor.state['current']
        first=self.edit(rename_ops(c,g));base=c.editor.state['generations'][first['generation']]
        result=self.edit(closeout_ops(c,first['generation'],notes='Corrected current-pass note.'))
        head=c.editor.state['generations'][result['generation']]
        self.assertEqual(head['manifest'][SOURCE],base['manifest'][SOURCE])
        self.assertEqual(head['manifest'][c.editor.ledger],base['manifest'][c.editor.ledger])
        self.assertNotEqual(head['manifest'][c.editor.project+'docs/reverse_engineering/PROGRESS_SCORECARD.md'],
                            base['manifest'][c.editor.project+'docs/reverse_engineering/PROGRESS_SCORECARD.md'])

    def test_interrupted_validation_recovers_without_stale_evidence(self):
        c=self.controller;g=c.editor.state['current'];p=c.editor.preview(g,rename_ops(c,g))
        cid=c.editor.confirm(g,p['preview_digest'])['candidate']
        with c.editor.transaction(write=True):
            candidate=c.editor.state['candidates'][cid]
            candidate.update(status='validating',gates=[{'exit_code':0}],error='obsolete')
            c.editor.save()
        reopened=type(c.editor)(c.editor.root)
        candidate=reopened.state['candidates'][cid]
        self.assertEqual(candidate['status'],'rejected')
        self.assertEqual(candidate['error'],'VALIDATION_INTERRUPTED')
        self.assertTrue(candidate['retryable']);self.assertFalse(candidate.get('gates'))
        self.assertEqual(reopened.validate(cid)['status'],'validated')

    def test_real_gate_write_names_forbidden_path(self):
        c=prepare(self.root/'gate-write',gate_extra="Path('projects/sample/docs/reverse_engineering/WORKING_NOTES.md').write_text('Unplanned gate edit.\\n')\n")
        g=c.editor.state['current'];p=c.editor.preview(g,rename_ops(c,g))
        cid=c.editor.confirm(g,p['preview_digest'])['candidate'];result=c.editor.validate(cid)
        self.assertEqual(result['status'],'rejected',result)
        self.assertEqual(result['error'],'FORBIDDEN_PATH',result)
        self.assertEqual(result['error_details']['paths'],['projects/sample/docs/reverse_engineering/WORKING_NOTES.md'])
        self.assertTrue(result['reference_prg_parity'])

    def test_oversized_late_preview_item_registers_no_digest(self):
        c=prepare(self.root/'large-preview',uses=35);g=c.editor.state['current']
        operations=rename_ops(c,g);comment=comments(c.editor.model(g))[0]
        operations.append({'kind':'comment_replace','record_id':comment['record_id'],
            'preimage':comment['preimage_sha256'],'text':'; '+('x'*paging.MAX_BYTES),'reason':'Oversized negative control'})
        before=c.editor.state_path.read_bytes()
        with self.assertRaisesRegex(ValueError,'PREVIEW_ITEM_TOO_LARGE'):c.editor.preview(g,operations)
        self.assertEqual(c.editor.state_path.read_bytes(),before)
        self.assertFalse(list((c.editor.root/'previews').glob('*.json')))

    def test_many_uses_are_bounded_and_complete_over_both_bridges(self):
        c=prepare(self.root/'many-uses',uses=35);g=c.editor.state['current'];m=c.editor.model(g)
        expected={m.ids[r] for r,d in m.bindings.items() if d==m.declarations['Cell']}
        self.assertEqual(len(expected),35)
        def call(root,profile,operation,args):
            request={'jsonrpc':'2.0','id':1,'method':'tools/call','params':{'name':'operation',
                'arguments':{'operation':operation,'arguments':args}}}
            output=io.StringIO();mcp(root,'reviewer',profile,input_stream=io.StringIO(json.dumps(request)+'\n'),output_stream=output)
            wire=output.getvalue();self.assertLessEqual(len(wire.encode()),paging.MAX_BYTES)
            envelope=json.loads(wire)['result'];self.assertFalse(envelope.get('isError'),wire)
            return json.loads(envelope['content'][0]['text'])
        info=call(c.root,'corridor','inspect',{'generation':g,'symbol':'Cell'})
        self.assertEqual(info['use_count'],35);self.assertNotIn('uses',info)
        offset=0;seen=[]
        while offset is not None:
            page=call(c.root,'corridor','navigate',{'generation':g,'view':'uses','symbol':'Cell','offset':offset,'limit':4})
            seen.extend(item['reference']['record_id'] for item in page['records']);offset=page['next_offset']
        self.assertEqual(set(seen),expected);self.assertEqual(len(seen),35)
        p=c.editor.preview(g,rename_ops(c,g));cid=c.editor.confirm(g,p['preview_digest'])['candidate']
        self.assertEqual(c.editor.validate(cid)['status'],'validated')
        published=c.editor.publish(cid);head=published['generation']
        reader=RetainedReviewService.from_publication(self.root/'many-review',self.root/'many-uses/store',published['review']['artifact_id'])
        for root,profile in ((c.root,'corridor'),(reader.root,'retained')):
            base,new=reader.config['artifacts'][0],reader.config['artifacts'][-1]
            offset=0;seen=[];pages=0
            while offset is not None:
                args={'generation':new,'base_generation':base,'offset':offset}
                if profile=='corridor':args['ticket']=published['review']['artifact_id']
                page=call(root,profile,'review',args)
                self.assertEqual('q09' in page,offset==0);self.assertEqual('changed_files' in page,offset==0)
                seen.extend(item['reference_id'] for item in page['changes'] if item['kind']=='rename_use')
                offset=page['next_offset'];pages+=1
            self.assertEqual(set(seen),expected);self.assertEqual(len(seen),35);self.assertGreater(pages,35)

    def test_every_bridge_operation_has_a_wire_size_guard(self):
        from structured_pass.launcher import Corridor
        requests=[]
        for i,op in enumerate(('review','inspect','q09','query','navigate')):
            requests.append({'jsonrpc':'2.0','id':i,'method':'tools/call','params':{'name':'operation',
                'arguments':{'operation':op,'arguments':{}}}})
        output=io.StringIO()
        # Quotes exercise the second encoding layer: the inner object fits, its wire representation does not.
        with patch.object(Corridor,'dispatch',return_value={'text':'"'*8000}):
            mcp(self.controller.root,'reviewer',input_stream=io.StringIO(''.join(json.dumps(r)+'\n' for r in requests)),output_stream=output)
        lines=output.getvalue().splitlines();self.assertEqual(len(lines),5)
        for line in lines:
            self.assertLessEqual(len(line.encode())+1,paging.MAX_BYTES)
            reply=json.loads(line)['result'];self.assertTrue(reply['isError'])
            self.assertEqual(json.loads(reply['content'][0]['text'])['error'],'RESPONSE_TOO_LARGE')

    def test_application_refuses_overlap_and_dirty_selected_path(self):
        from structured_pass.application import apply
        from structured_pass_fixture import git
        c=self.controller;g=c.editor.state['current'];published=self.edit(rename_ops(c,g))
        c.dispatch('approve',{'ticket':published['review']['artifact_id'],'report':'Verdict: APPROVED\n\nSynthetic lifecycle only; quality gates are simulated.'},'reviewer')
        c.dispatch('closeout',{},'implementer')
        for committed,code in ((False,'APPLICATION_DIRTY_PATH'),(True,'APPLICATION_OVERLAPPING_CHANGE')):
            target=self.root/('overlap' if committed else 'dirty')
            git(self.root/'repo','clone','-q','--no-hardlinks',str(self.root/'repo'),str(target))
            reference=target/c.editor.reference;reference.parent.mkdir(parents=True,exist_ok=True)
            shutil.copy2(self.root/'repo'/c.editor.reference,reference)
            git(target,'checkout','-qb','projects')
            source=target/SOURCE;source.write_bytes(source.read_bytes()+b'; Independent change\n')
            if committed:
                git(target,'add',SOURCE);git(target,'commit','-qm','Conflicting fixture change')
            before=source.read_bytes();status=git(target,'status','--porcelain');head=git(target,'rev-parse','HEAD')
            with self.subTest(code=code),self.assertRaisesRegex(ValueError,code):apply(c.root,target,commit=True)
            self.assertEqual(source.read_bytes(),before);self.assertEqual(git(target,'status','--porcelain'),status)
            self.assertEqual(git(target,'rev-parse','HEAD'),head)

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

    def test_prepare_refuses_bad_mixed_documents_before_gates(self):
        from structured_pass.prepare import prepare as prepare_current
        from structured_pass_fixture import git, REFERENCE
        from structured_pass import mixed_documents as mixed
        repo=self.root/'repo'
        (repo/'scripts/project_common.sh').write_text('load_project_conf() { ASM_FILE="'+SOURCE+'"; REF_NES="'+REFERENCE+'"; }\n')
        selection={k:'Synthetic preflight' for k in ('target','objective','why_now','boundaries','evidence','reference_scope','out_of_scope')}
        selection['project']='sample'
        for index,relative in enumerate((mixed.SCORECARD,mixed.DEFERRALS)):
            path=repo/'projects/sample'/relative;original=path.read_bytes();path.write_text('Invalid mixed document.\n')
            git(repo,'add','.');git(repo,'commit','-qm','Invalid document fixture')
            output=self.root/('bad-preparation-'+str(index))
            with self.subTest(path=relative),self.assertRaisesRegex(ValueError,'MIXED_DOCUMENT_SCHEMA'):
                prepare_current(repo,output,selection,producer.EXE,self.root/'store')
            self.assertFalse((output/'logs/next-pass.log').exists());self.assertFalse((output/'session').exists())
            path.write_bytes(original)

    def test_empty_ledger_append_refuses_before_validation(self):
        c=self.controller;g=c.editor.state['current'];ops=rename_ops(c,g);ops[1]['rows']=[]
        with self.assertRaisesRegex(ValueError,'LEDGER_SCHEMA'):c.editor.preview(g,ops)
        self.assertFalse(c.editor.state['candidates'])

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

    def test_interrupt_halts_next_reservation(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);service.write_json(root/'budget.json',{'configuration_sha256':'pin','authorized':True,
                'max_responses':100,'max_seconds':100,'deadline':None,'runs':[]})
            budget=Budget(root,'pin');run=budget.reserve('implementer',30)
            budget.interrupt(run['id'])
            with self.assertRaisesRegex(ValueError,'BUDGET_HALTED'):budget.reserve('reviewer',30)

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
