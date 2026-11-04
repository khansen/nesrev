"""Client completion and bounded reader regressions; no provider requests."""
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from structured_pass import service, producer, paging
from structured_pass.bridge import mcp
from structured_pass.rename_service import comments
from structured_pass.retained_service import RetainedReviewService
from structured_pass.usage_budget import Budget
import structured_pass_fixture as fixture


class ClientCompletionTests(unittest.TestCase):
    def run_client(self,root,finals,exit_code):
        from structured_pass.subscription_client import TOOL
        config={'heavy_lock':os.environ.get('NESREV_HEAVY_RUN_LOCK',str(root/'test.lock')),
                'model':'fixture-model','phase_response_cap':30,
                'roles':{'implementer':{'workspace':str(root)}}}
        service.write_json(root/'launch.json',config)
        service.write_json(root/'budget.json',{'configuration_sha256':producer.sha(root/'launch.json'),
            'authorized':True,'max_responses':100,'max_seconds':60,'deadline':None,'runs':[]})
        events=[{'type':'system','subtype':'init','tools':['Read',TOOL],
                 'additional_directories':[],'model':'fixture-model','permissionMode':'dontAsk'},
                {'type':'assistant','message':{'id':'one-response'}},
                {'type':'assistant','message':{'id':'one-response'}},*finals]
        client=root/'fake_client.py'
        client.write_text('import sys\nsys.stdout.write('+repr(''.join(json.dumps(e)+'\n' for e in events))+')\nsys.exit('+str(exit_code)+')\n')
        # Exercise the real CLI, stream reader and accounting with a local child.
        # Only authentication, pinned configuration and the external argv are faked.
        driver=root/'driver.py'
        driver.write_text('''import json,sys
from pathlib import Path
from unittest.mock import patch
from structured_pass import subscription_client as client
root=Path(sys.argv[1]);config=json.loads((root/'launch.json').read_text())
sys.argv=['subscription_client','--root',str(root),'run','implementer','--message','fixture']
with patch.object(client,'verify',return_value=config),patch.object(client,'authenticate',return_value={'fixture':True}),patch.object(client,'command',return_value=[sys.executable,str(root/'fake_client.py')]):
    client.main()
''')
        env=dict(os.environ,PYTHONPATH=str(ROOT/'scripts'),PYTHONDONTWRITEBYTECODE='1',
                 NESREV_HEAVY_RUN_LOCK=config['heavy_lock'])
        result=subprocess.run([sys.executable,'-B',str(driver),str(root)],env=env,
                              text=True,capture_output=True,timeout=15)
        budget=json.loads((root/'budget.json').read_text())
        row=budget['runs'][0]
        receipt=json.loads((root/'runs'/row['id']/'run.json').read_text())
        self.assertEqual(row['charged'],1)
        self.assertEqual(receipt['exit_code'],exit_code)
        self.assertEqual(receipt['accounting']['charged'],1)
        self.assertTrue((root/'runs'/row['id']/'stdout.jsonl').is_file())
        return result,budget,receipt

    def test_cli_propagates_failed_and_incomplete_client_runs(self):
        success={'type':'result','subtype':'success','is_error':False,'result':'done'}
        cases=[('nonzero',[success],7,'CLIENT_RUN_FAILED',False),
               ('nonzero-missing',[],7,'CLIENT_RUN_FAILED',True),
               ('missing',[],0,'CLIENT_STREAM_INCOMPLETE',True),
               ('duplicate',[success,success],0,'CLIENT_STREAM_INCOMPLETE',True),
               ('error-result',[dict(success,subtype='error_max_turns',is_error=True)],0,'CLIENT_RUN_FAILED',False),
               ('error-flag',[dict(success,is_error=True)],0,'CLIENT_RUN_FAILED',False)]
        for name,finals,exit_code,code,halted in cases:
            with self.subTest(case=name),tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);result,budget,receipt=self.run_client(root,finals,exit_code)
                self.assertNotEqual(result.returncode,0,result.stdout)
                self.assertIn(code,result.stderr)
                self.assertEqual(receipt['error'],code)
                self.assertEqual(bool(budget.get('halted')),halted)
                if halted:
                    with self.assertRaisesRegex(ValueError,'BUDGET_HALTED'):
                        Budget(root,producer.sha(root/'launch.json')).reserve('reviewer',30)

    def test_cli_success_keeps_exact_accounting(self):
        with tempfile.TemporaryDirectory() as tmp:
            result,budget,receipt=self.run_client(Path(tmp),[
                {'type':'result','subtype':'success','is_error':False,'result':'done','num_turns':76}],0)
            self.assertEqual(result.returncode,0,result.stderr)
            self.assertEqual(json.loads(result.stdout)['result'],'done')
            self.assertIsNone(receipt['error']);self.assertFalse(budget.get('halted'))
            self.assertEqual(budget['runs'][0]['client_num_turns'],76)


class ReaderBoundaryTests(unittest.TestCase):
    def setUp(self):
        if not os.environ.get('STRUCTURED_PASS_XASM'):self.skipTest('Pinned producer required')
        (ROOT/'tmp').mkdir(exist_ok=True)
        temp=tempfile.TemporaryDirectory(prefix='structured-readers-',dir=ROOT/'tmp')
        self.addCleanup(temp.cleanup);self.root=Path(temp.name)

    def prepare(self,transform,**kwargs):
        original=fixture.fixture
        def inputs(*args,**kw):
            source,reference=original(*args,**kw)
            source.write_bytes(transform(source.read_bytes()))
            return source,reference
        with patch.object(fixture,'fixture',side_effect=inputs):
            return fixture.prepare(self.root,**kwargs)

    def calls(self,root,profile,calls):
        requests=[{'jsonrpc':'2.0','id':i,'method':'tools/call','params':{'name':'operation',
            'arguments':{'operation':op,'arguments':args}}} for i,(op,args) in enumerate(calls,1)]
        output=io.StringIO();mcp(root,'reviewer',profile,
            input_stream=io.StringIO(''.join(json.dumps(r)+'\n' for r in requests)),output_stream=output)
        result=[]
        for wire in output.getvalue().splitlines():
            self.assertLessEqual(len((wire+'\n').encode()),paging.MAX_BYTES)
            envelope=json.loads(wire)['result'];self.assertFalse(envelope.get('isError'),wire)
            result.append(json.loads(envelope['content'][0]['text']))
        self.assertEqual(len(result),len(calls))
        return result

    def publish(self,c,operations):
        g=c.editor.state['current'];p=c.dispatch('preview',{'generation':g,'operations':operations},'implementer')
        cid=c.dispatch('confirm',{'generation':g,'preview_digest':p['preview_digest']},'implementer')['candidate']
        result=c.dispatch('validate',{'cid':cid},'implementer')
        self.assertEqual(result['status'],'validated',result);self.assertTrue(result['reference_prg_parity'])
        return c.dispatch('publish',{'cid':cid},'implementer')

    def test_constant_owners_follow_use_pages_in_both_sessions(self):
        aliases=[('Alias'+str(i)+'x'*90) for i in range(320)]
        added=''.join(name+' .EQU Cell\n' for name in aliases).encode()
        c=self.prepare(lambda data:data.replace(b'.END\n',added+b'.END\n'),uses=3)
        g=c.editor.state['current'];m=c.editor.model(g)
        expected={m.ids[r] for r,d in m.bindings.items() if d==m.declarations['Cell']}
        published=self.publish(c,fixture.closeout_ops(c,g))
        reader=RetainedReviewService.from_publication(self.root/'review',self.root/'store',published['review']['artifact_id'])
        for root,profile,generation in ((c.root,'corridor',g),(reader.root,'retained',reader.config['artifacts'][0])):
            seen=[];owners={}
            calls=[('query',{'generation':generation,'symbol':'Cell','offset':i,'limit':1}) for i in range(len(expected)+1)]
            pages=self.calls(root,profile,calls)
            for i,page in enumerate(pages):
                self.assertEqual(page['total'],len(expected))
                self.assertEqual(page['total_owner_count'],321)
                self.assertEqual(page['owners_scope'],'current_page')
                names={r['statement'].get('lexical_owner') or r['statement'].get('name') or r['statement']['kind'] for r in page['uses']}
                self.assertEqual(set(page['owners']),names)
                self.assertEqual(page['next_offset'],i+1 if i+1<len(expected) else None)
                seen.extend(r['reference_id'] for r in page['uses']);owners.update(page['owners'])
            self.assertEqual(set(seen),expected);self.assertEqual(len(seen),len(expected))
            self.assertEqual(owners,{'Entry':3,**dict.fromkeys(aliases,1)})

    def test_non_utf8_comments_remain_readable_and_repairable(self):
        raw=b'; caf\xe9 \xffCell';untouched=b'; preserve \xff bytes'
        c=self.prepare(lambda data:data.replace(b'; Private source comment',raw+b'\n'+untouched))
        g=c.editor.state['current'];model=c.editor.model(g);record=comments(model)[0]
        self.assertEqual(record['text_encoding'],'utf-8-replacement')
        self.assertEqual(record['text'],'; caf\ufffd \ufffdCell')
        self.assertEqual(bytes.fromhex(record['bytes_hex']),raw)
        self.assertEqual(record['preimage_sha256'],producer.digest(raw))
        base_reads=self.calls(c.root,'corridor',[
            ('q09',{'generation':g,'names':['Cell']}),
            ('navigate',{'generation':g,'view':'comments'})])
        self.assertEqual(base_reads[0]['total_mentions'],1)
        preview=c.editor.preview(g,fixture.rename_ops(c,g))
        cid=c.editor.confirm(g,preview['preview_digest'])['candidate']
        failed=c.editor.validate(cid)
        self.assertEqual(failed['error'],'SEMANTIC_CONTRACT',failed)
        self.assertFalse(failed['semantic_properties']['no_stale_source_prose'])
        repair={'kind':'comment_replace','record_id':record['record_id'],'preimage':record['preimage_sha256'],
                'text':'; Legacy byte encoding corrected.','reason':'Repair a legacy-encoded comment.'}
        with self.assertRaisesRegex(ValueError,'COMMENT_PREIMAGE_MISMATCH'):
            c.editor.preview(g,[dict(repair,preimage=producer.digest(record['text'].encode())),*fixture.closeout_ops(c,g)])
        published=self.publish(c,[*fixture.rename_ops(c,g),repair])
        after=c.editor.model(published['generation'])
        self.assertIn(untouched,after.source);self.assertNotIn(raw,after.source)
        reader=RetainedReviewService.from_publication(self.root/'review',self.root/'store',published['review']['artifact_id'])
        base,head=reader.config['artifacts']
        retained=self.calls(reader.root,'retained',[
            ('q09',{'generation':base,'names':['Cell']}),
            ('navigate',{'generation':base,'view':'comments'}),
            ('q09',{'generation':head,'names':['Cell']})])
        for a,b in zip(base_reads,retained):
            self.assertEqual({k:v for k,v in a.items() if k!='generation'},
                             {k:v for k,v in b.items() if k!='generation'})
        self.assertEqual(retained[2]['total_mentions'],0)


if __name__=='__main__':unittest.main()
