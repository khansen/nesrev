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
        for record in p['records']:
            if record['kind']=='document':self.assertNotIn('hunks',record)
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
                for item in page['changes']:
                    if item['kind']!='rename_use':continue
                    for side,model in (('before',m),('after',c.editor.model(head))):
                        ref=model.node(item['reference_id']);context=model.context(ref)
                        self.assertEqual(item[side]['record'],model.statement(context))
                        self.assertEqual(item[side]['reference'],model.expression(ref))
                        self.assertEqual(item[side]['reference']['declaration_id'],item['declaration_id'])
                        self.assertNotIn('before',item[side]);self.assertNotIn('after',item[side])
                    if not seen:
                        context=call(root,profile,'navigate',{'generation':new,'view':'records',
                            'record_id':item['after']['record']['record_id'],'limit':1})
                        self.assertEqual(context['records'][0]['record_id'],item['after']['record']['record_id'])
                seen.extend(item['reference_id'] for item in page['changes'] if item['kind']=='rename_use')
                offset=page['next_offset'];pages+=1
            self.assertEqual(set(seen),expected);self.assertEqual(len(seen),35)
            self.assertEqual(pages,page['total_pages']);self.assertLess(pages,15)

    def test_q09_pages_complete_inventory_in_both_sessions_and_preview_checks_all(self):
        from structured_pass.rename_service import RenameService
        from structured_pass_fixture import PROJECT
        notes=''.join('Cell prose '+str(i)+' '+('quoted " snow \u2603 '*35)+'\n' for i in range(83))
        c=prepare(self.root/'prose-pages',notes=notes);self.controller=c;g=c.editor.state['current']
        # The mutation guard must use the whole inventory, even if its public
        # read is replaced with an empty page.
        with patch.object(RenameService,'q09',return_value={'mentions':[]}):
            with self.assertRaisesRegex(service.ServiceError,'UNDISPOSED_STALE_PROSE') as caught:
                c.editor.preview(g,rename_ops(c,g))
            self.assertIn(PROJECT+'docs/reverse_engineering/WORKING_NOTES.md',caught.exception.details['paths'])
        published=self.edit(closeout_ops(c,g))
        reader=RetainedReviewService.from_publication(self.root/'prose-review',self.root/'prose-pages/store',published['review']['artifact_id'])
        head=reader.config['artifacts'][-1]
        for root,profile in ((c.root,'corridor'),(reader.root,'retained')):
            offered=self.bridge_request(root,profile)
            self.assertIn('q09',offered['tools'][0]['inputSchema']['properties']['operation']['enum'])
            offset=0;seen=[];page_count=0
            while offset is not None:
                page=self.bridge_request(root,profile,'q09',{'generation':head,'names':['Cell'],'offset':offset,'limit':40})
                self.assertEqual(page['total_mentions'],83);self.assertEqual(page['offset'],offset)
                seen.extend(page['mentions']);page_count+=1;offset=page['next_offset']
            self.assertGreater(page_count,3)
            self.assertEqual([hit['line'] for hit in seen],list(range(1,84)))
            self.assertEqual([hit['text'] for hit in seen],notes.splitlines())
            for bad in ({'offset':-1},{'offset':True},{'limit':0},{'limit':41},{'names':'Cell'}):
                with self.assertRaisesRegex(ValueError,'REQUEST_SCHEMA'):
                    (c if profile=='corridor' else reader).dispatch('q09',{'generation':head,'names':['Cell'],**bad},'reviewer')
        metadata=self.bridge_request(c.root,'corridor','review',{'ticket':published['review']['artifact_id'],
            'generation':head,'base_generation':reader.config['artifacts'][0]})
        query=metadata['q09']['read']
        self.assertEqual(query['operation'],'q09')
        # This scorecard-only publication has no old names, so its Q09 is empty.
        self.assertEqual(self.bridge_request(c.root,'corridor',query['operation'],query['arguments'])['total_mentions'],0)
        with self.assertRaisesRegex(ValueError,'UNKNOWN_GENERATION'):
            c.dispatch('q09',{'generation':'E-foreign','names':['Cell']},'reviewer')

    def test_failed_closeout_exposes_failures_before_success_summary_over_bridge(self):
        extra="import json\nprint('FAIL: '+str(Path.cwd())+'/projects/sample/docs/reverse_engineering/WORKING_NOTES.md: fix the required evidence')\nprint(json.dumps({'summary':'No stale old-symbol references found','residue':[]}))\nsys.exit(4)\n"
        c=prepare(self.root/'failing-closeout',gate_extra=extra);g=c.editor.state['current']
        preview=c.editor.preview(g,rename_ops(c,g));cid=c.editor.confirm(g,preview['preview_digest'])['candidate']
        request={'jsonrpc':'2.0','id':1,'method':'tools/call','params':{'name':'operation','arguments':{
            'operation':'validate','arguments':{'cid':cid}}}}
        output=io.StringIO();mcp(c.root,'implementer','corridor',input_stream=io.StringIO(json.dumps(request)+'\n'),output_stream=output)
        self.assertLessEqual(len(output.getvalue().encode()),paging.MAX_BYTES)
        response=json.loads(output.getvalue())['result'];self.assertFalse(response.get('isError'),response)
        value=json.loads(response['content'][0]['text'])
        self.assertEqual(value['error'],'NEW_GATE_FAILURE');self.assertTrue(value['reference_prg_parity'])
        diag=next(gate['diagnostic'] for gate in value['gates'] if gate['exit_code'])
        self.assertEqual(diag['report']['summary'],'No stale old-symbol references found')
        self.assertEqual(diag['failure_lines'],['FAIL: projects/sample/docs/reverse_engineering/WORKING_NOTES.md: fix the required evidence'])
        self.assertEqual(diag['failure_line_count_in_tail'],1);self.assertFalse(diag['failure_lines_truncated'])
        self.assertNotIn(str(self.root),json.dumps(diag))
        with self.assertRaisesRegex(ValueError,'CANDIDATE_NOT_PUBLISHABLE'):c.editor.publish(cid)

    def test_multiple_failing_gate_diagnostics_share_response_budget(self):
        c=self.controller;g=c.editor.state['current']
        preview=c.editor.preview(g,rename_ops(c,g));cid=c.editor.confirm(g,preview['preview_digest'])['candidate']
        def failing_gates(checkout,operations,folder,env):
            result=[]
            for target in ('project-inventory','project-verify','project-process-check','project-docs-check'):
                log=folder/(target+'.log')
                log.write_text(''.join('FAIL: '+target+' '+str(i)+' '+('"\u2603'*1000)+'\n' for i in range(12)))
                result.append({'target':target,'exit_code':4,'seconds':0,'log_sha256':producer.sha(log),'environment':dict(env)})
            return result
        with patch.object(c.editor,'run_gates',side_effect=failing_gates):value=c.editor.validate(cid)
        self.assertEqual(value['error'],'NEW_GATE_FAILURE')
        response=self.bridge_request(c.root,'corridor','candidate_status',{'cid':cid})
        self.assertEqual(response['error'],'NEW_GATE_FAILURE')
        self.assertEqual(len(response['gates']),4)
        for gate in response['gates']:
            self.assertTrue(gate['diagnostic']['failure_lines'])
            self.assertIn(gate['target'],gate['diagnostic']['failure_lines'][0])
            self.assertTrue(gate['diagnostic']['truncated'])

    def test_oversized_first_document_and_use_remain_reviewable(self):
        from structured_pass import authored_documents, review_pages
        from structured_pass_fixture import PROJECT
        c=self.controller;g=c.editor.state['current'];m=c.editor.model(g)
        n=m.declarations['Entry'];path=PROJECT+'docs/reverse_engineering/WORKING_NOTES.md'
        text='Long document line: '+('quoted " text \u2603 '*100)+'\n'
        text=text*70+'Actual new final line.\n'
        reason='Oversized document is the first authored change.'
        ops=[{'kind':'document_write','path':path,'preimage':c.editor.state['generations'][g]['manifest'][path],
              'text':text,'reason':reason},
             {'kind':'rename','declaration_id':m.ids[n],'old_name':'Entry','new_name':'Start',
              'preimage':m.statement(n)['preimage_sha256']},
             {'kind':'ledger_append','path':c.editor.ledger,'preimage':c.editor.state['generations'][g]['manifest'][c.editor.ledger],
              'rows':[{'old_name':'Entry','new_name':'Start','reason':'Fixture','confidence':'high','pass_id':'1'}]},
             *closeout_ops(c,g)]
        published=self.edit(ops)
        reader=RetainedReviewService.from_publication(self.root/'oversized-review',self.root/'store',published['review']['artifact_id'])
        base,head=reader.config['artifacts'];offset=0;changes=[];pages=[]
        while offset is not None:
            request={'jsonrpc':'2.0','id':1,'method':'tools/call','params':{'name':'operation','arguments':{
                'operation':'review','arguments':{'ticket':published['review']['artifact_id'],
                'generation':head,'base_generation':base,'offset':offset}}}}
            out=io.StringIO();mcp(c.root,'reviewer',input_stream=io.StringIO(json.dumps(request)+'\n'),output_stream=out)
            wire=out.getvalue();self.assertLessEqual(len(wire.encode()),paging.MAX_BYTES)
            response=json.loads(wire)['result'];self.assertFalse(response.get('isError'),wire)
            page=json.loads(response['content'][0]['text']);pages.append(page);changes.extend(page['changes']);offset=page['next_offset']
        self.assertEqual(pages[0]['page_kind'],'metadata');self.assertEqual(pages[0]['changes'],[])
        self.assertIn('changed_files',pages[0]);self.assertIn('q09',pages[0])
        self.assertEqual(len(changes),pages[0]['total_changes'])
        self.assertEqual(len(pages),pages[0]['total_pages'])
        document=next(ch for ch in changes if ch['kind']=='authored_document')
        self.assertEqual(document['path'],path);self.assertEqual(document['reason'],reason)
        self.assertEqual(document['after']['sha256'],authored_documents.sha(text.encode()))
        self.assertTrue(document['after']['truncated'])
        self.assertLess(sum(len(h['after_lines']) for h in document['hunks']),71)
        self.assertIsNotNone(document['after']['first_omitted_line'])
        use=next(ch for ch in changes if ch['kind']=='rename_use')
        self.assertTrue(use['neighbors_omitted'])
        self.assertEqual(use['before']['record']['record_id'],use['after']['record']['record_id'])
        self.assertEqual(use['reference_id'],next(m.ids[r] for r,d in m.bindings.items() if d==n))
        receipt=next(ch for ch in changes if ch['kind']=='wrapper_closeout')
        self.assertNotIn('wrapper_code_hashes',receipt['receipt'])
        original=Path(c.editor.state['generations'][published['generation']]['capture'])/'closeout.json'
        original_hashes=json.loads(original.read_text())['wrapper_code_hashes']
        self.assertEqual(receipt['receipt_sha256'],producer.sha(original))
        self.assertEqual(receipt['receipt']['wrapper_code_sha256'],service.digest(json.dumps(original_hashes,sort_keys=True,separators=(',',':')).encode()))
        # A large changed record itself cannot be discarded as context. The last
        # resort is a typed refusal with an explicit continuation, never a spill.
        oversized={'changes':[{'kind':'rename_use','before':{'record':{'record_id':'r1','value':'x'*paging.MAX_BYTES}}}],
                   'offset':3,'total_changes':5,'total_pages':6,'next_offset':4}
        with self.assertRaisesRegex(service.ServiceError,'RESPONSE_TOO_LARGE') as caught:review_pages.fit(oversized)
        self.assertEqual(caught.exception.details,{'offset':3,'total_changes':5,'total_pages':6,'next_offset':4})

    def test_oversized_document_first_change_keeps_metadata_readable(self):
        c=self.controller;g=c.editor.state['current']
        path=c.editor.project+'docs/reverse_engineering/WORKING_NOTES.md'
        op={'kind':'document_write','path':path,'preimage':c.editor.state['generations'][g]['manifest'][path],
            'text':('Long line '+('x'*3000)+'\n')*60,'reason':'First and oversized change.'}
        published=self.edit([op,*closeout_ops(c,g)])
        reader=RetainedReviewService.from_publication(self.root/'doc-review',self.root/'store',published['review']['artifact_id'])
        base,head=reader.config['artifacts'];pages=[];offset=0
        while offset is not None:
            request={'jsonrpc':'2.0','id':1,'method':'tools/call','params':{'name':'operation','arguments':{
                'operation':'review','arguments':{'generation':head,'base_generation':base,'offset':offset}}}}
            out=io.StringIO();mcp(reader.root,'reviewer','retained',input_stream=io.StringIO(json.dumps(request)+'\n'),output_stream=out)
            self.assertLessEqual(len(out.getvalue().encode()),paging.MAX_BYTES)
            response=json.loads(out.getvalue())['result'];self.assertFalse(response.get('isError'),response)
            page=json.loads(response['content'][0]['text']);pages.append(page);offset=page['next_offset']
        self.assertEqual(pages[0]['changes'],[]);self.assertEqual(pages[0]['total_changes'],3)
        self.assertIn('q09',pages[0]);self.assertIn('changed_files',pages[0])
        first=pages[1]['changes'][0];self.assertEqual(first['kind'],'authored_document')
        self.assertEqual(first['reason'],op['reason']);self.assertTrue(first['after']['truncated'])
        self.assertEqual(sum(len(p['changes']) for p in pages),3)

    def test_every_bridge_operation_has_a_wire_size_guard(self):
        from structured_pass.launcher import Corridor
        requests=[]
        for i,op in enumerate(('review','inspect','q09','query','navigate','document')):
            requests.append({'jsonrpc':'2.0','id':i,'method':'tools/call','params':{'name':'operation',
                'arguments':{'operation':op,'arguments':{}}}})
        output=io.StringIO()
        # Quotes exercise the second encoding layer: the inner object fits, its wire representation does not.
        with patch.object(Corridor,'dispatch',return_value={'text':'"'*8000,'offset':3,'total_changes':7,'next_offset':4}):
            mcp(self.controller.root,'reviewer',input_stream=io.StringIO(''.join(json.dumps(r)+'\n' for r in requests)),output_stream=output)
        lines=output.getvalue().splitlines();self.assertEqual(len(lines),6)
        for index,line in enumerate(lines):
            self.assertLessEqual(len(line.encode())+1,paging.MAX_BYTES)
            reply=json.loads(line)['result'];self.assertTrue(reply['isError'])
            value=json.loads(reply['content'][0]['text'])
            self.assertEqual(value['error'],'RESPONSE_TOO_LARGE')
            if index==0:self.assertEqual((value['offset'],value['total_changes'],value['next_offset']),(3,7,4))
            else:
                self.assertNotIn('next_offset',value)
                self.assertEqual(value['offset'],3)
                self.assertIn('retry the same offset',value['action'])

    def bridge_request(self,root,profile,operation=None,arguments=None):
        request={'jsonrpc':'2.0','id':1,'method':'tools/call' if operation else 'tools/list'}
        if operation:request['params']={'name':'operation','arguments':{'operation':operation,'arguments':arguments}}
        output=io.StringIO()
        mcp(root,'reviewer',profile,input_stream=io.StringIO(json.dumps(request)+'\n'),output_stream=output)
        self.assertLessEqual(len(output.getvalue().encode()),paging.MAX_BYTES)
        result=json.loads(output.getvalue())['result']
        self.assertFalse(result.get('isError'),result)
        return json.loads(result['content'][0]['text']) if operation else result

    def test_long_ledger_pages_cover_all_64_rows(self):
        self.controller=prepare(self.root/'large-ledger',declarations=64)
        c=self.controller;g=c.editor.state['current'];m=c.editor.model(g);ops=[];rows=[]
        for name in ['Cell']+['Cell'+str(i) for i in range(1,64)]:
            n=m.declarations[name];new=name+'Capacity'
            ops.append({'kind':'rename','declaration_id':m.ids[n],'old_name':name,'new_name':new,
                        'preimage':m.statement(n)['preimage_sha256']})
            rows.append({'old_name':name,'new_name':new,'reason':('Long fixture rationale for '+name+'. ').ljust(632,'x'),
                         'confidence':'high','pass_id':'1'})
        ops.append({'kind':'ledger_append','path':c.editor.ledger,
                    'preimage':c.editor.state['generations'][g]['manifest'][c.editor.ledger],'rows':rows})
        published=self.edit(ops+closeout_ops(c,g))
        reader=RetainedReviewService.from_publication(self.root/'ledger-review',self.root/'large-ledger/store',published['review']['artifact_id'])
        base,head=reader.config['artifacts']
        for root,profile in ((c.root,'corridor'),(reader.root,'retained')):
            offset=0;pages=[];seen=[];refs=[];ledger_offsets=[]
            while offset is not None:
                args={'generation':head,'base_generation':base,'offset':offset}
                if profile=='corridor':args['ticket']=published['review']['artifact_id']
                page=self.bridge_request(root,profile,'review',args);pages.append(page)
                self.assertEqual('review_code_hashes' in page,offset==0)
                self.assertEqual(page['review_code_sha256'],pages[0]['review_code_sha256'])
                for item in page['changes']:
                    if item['kind']=='authored_ledger':
                        self.assertEqual(item['row_offset'],len(seen));self.assertEqual(item['total_added_rows'],64)
                        self.assertEqual(item['unchanged_prefix_rows'],0);self.assertLessEqual(len(item['added_rows']),16)
                        ledger_offsets.append(item['row_offset']);seen.extend(item['added_rows'])
                    elif item['kind']=='rename_use':refs.append(item['reference_id'])
                offset=page['next_offset']
            self.assertEqual(seen,rows);self.assertEqual(ledger_offsets,[0,16,32,48])
            self.assertEqual(len(refs),64);self.assertEqual(len(set(refs)),64)
            self.assertEqual(pages[0]['total_changes'],134);self.assertEqual(pages[0]['total_pages'],135)
            self.assertEqual(len(pages),135)

    def test_appended_document_is_visible_and_page_ids_read_in_both_bridges(self):
        text=''.join('Unchanged line '+str(i)+' '+('x'*160)+'\n' for i in range(180))
        self.controller=prepare(self.root/'append-document',notes=text)
        c=self.controller;g=c.editor.state['current'];path=c.editor.project+'docs/reverse_engineering/WORKING_NOTES.md'
        appended='This appended change must be visible.\n'
        changed=text.splitlines(keepends=True);changed[4]='Changed near the beginning.\n'
        changed=''.join(changed)+appended
        published=self.edit([{'kind':'document_write','path':path,'reason':'Expose the actual appended edit.',
            'preimage':c.editor.state['generations'][g]['manifest'][path],'text':changed},*closeout_ops(c,g)])
        reader=RetainedReviewService.from_publication(self.root/'append-review',self.root/'append-document/store',published['review']['artifact_id'])
        base,head=reader.config['artifacts']
        for root,profile in ((c.root,'corridor'),(reader.root,'retained')):
            listing=self.bridge_request(root,profile)
            self.assertIn('document',listing['tools'][0]['inputSchema']['properties']['operation']['enum'])
            args={'generation':head,'base_generation':base,'offset':1}
            if profile=='corridor':args['ticket']=published['review']['artifact_id']
            page=self.bridge_request(root,profile,'review',args);document=page['changes'][0]
            self.assertEqual(document['hunks'],[
                {'before_line':5,'after_line':5,'before_lines':[text.splitlines()[4]],'after_lines':['Changed near the beginning.']},
                {'before_line':181,'after_line':181,'before_lines':[],'after_lines':[appended.rstrip()]}])
            self.assertEqual(document['total_hunks'],2);self.assertEqual(document['omitted_hunks'],0)
            for side in ('before','after'):
                self.assertFalse(document[side]['truncated'])
                self.assertIsNone(document[side]['first_omitted_line'])
            self.assertEqual(document['before']['changed_line_count'],1)
            self.assertEqual(document['after']['changed_line_count'],2)
            for generation,expected in ((page['base_generation'],text),(page['generation'],changed)):
                offset=0;lines=[]
                while offset is not None:
                    view=self.bridge_request(root,profile,'document',{'generation':generation,'path':path,'offset':offset,'limit':20})
                    self.assertEqual(view['generation'],generation)
                    lines.extend(view['lines']);offset=view['next_offset']
                self.assertEqual(lines,expected.splitlines())
        with self.assertRaisesRegex(ValueError,'UNKNOWN_GENERATION'):
            c.document({'generation':'E-'+'0'*64,'path':path})
        self.assertEqual(c.document({'generation':g,'path':path,'limit':1})['lines'],text.splitlines()[:1])

    def test_service_review_refusal_keeps_continuation_on_bridge(self):
        from structured_pass.launcher import Corridor
        details={'offset':3,'total_changes':7,'total_pages':8,'next_offset':4}
        request={'jsonrpc':'2.0','id':1,'method':'tools/call','params':{'name':'operation',
            'arguments':{'operation':'review','arguments':{}}}}
        output=io.StringIO()
        with patch.object(Corridor,'dispatch',side_effect=service.ServiceError('RESPONSE_TOO_LARGE',**details)):
            mcp(self.controller.root,'reviewer',input_stream=io.StringIO(json.dumps(request)+'\n'),output_stream=output)
        result=json.loads(output.getvalue())['result'];self.assertTrue(result['isError'])
        value=json.loads(result['content'][0]['text'])
        self.assertEqual(value['error'],'RESPONSE_TOO_LARGE')
        for key,val in details.items():self.assertEqual(value[key],val)
        request['params']['arguments']['operation']='navigate';output=io.StringIO()
        with patch.object(Corridor,'dispatch',side_effect=service.ServiceError('RESPONSE_TOO_LARGE',**details)):
            mcp(self.controller.root,'reviewer',input_stream=io.StringIO(json.dumps(request)+'\n'),output_stream=output)
        value=json.loads(json.loads(output.getvalue())['result']['content'][0]['text'])
        self.assertNotIn('next_offset',value)

    def test_unpaged_overflow_does_not_suggest_nonexistent_limit(self):
        from structured_pass.launcher import Corridor
        request={'jsonrpc':'2.0','id':1,'method':'tools/call','params':{'name':'operation',
            'arguments':{'operation':'q09','arguments':{}}}}
        output=io.StringIO()
        with patch.object(Corridor,'dispatch',return_value={'mentions':['"'*8000]}):
            mcp(self.controller.root,'reviewer',input_stream=io.StringIO(json.dumps(request)+'\n'),output_stream=output)
        value=json.loads(json.loads(output.getvalue())['result']['content'][0]['text'])
        self.assertEqual(value['error'],'RESPONSE_TOO_LARGE')
        self.assertNotIn('action',value);self.assertNotIn('offset',value);self.assertNotIn('next_offset',value)

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
