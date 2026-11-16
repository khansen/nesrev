"""Offline pair integration: real service/adapters, synthetic local client streams."""
import copy
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from argparse import Namespace
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import structured_pair_launcher as pair
import structured_client_workspace as workspace
import structured_codex_client as codex
from structured_pass import subscription_client as claude, bridge
import structured_pass_fixture as fixture


class WorkspaceTests(unittest.TestCase):
    def test_classification_requires_authoritative_progress(self):
        start={'handoff':None}
        ready={'handoff':{'run_id':'r','status':'READY_FOR_REVIEW','round':1,'coverage':{'pass_head':'h'}}}
        self.assertEqual(pair.classify(start,ready,'implementer',False),'handoff')
        self.assertEqual(pair.classify(ready,ready,'reviewer',False),'unfinished')
        self.assertEqual(pair.classify(start,start,'implementer',False),'unfinished')
        self.assertEqual(pair.classify(ready,ready,'implementer',True),'closed')

    def test_checkout_worktree_bare_and_symlink_ancestors_refuse(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary).resolve();child=root/'parent/child';child.mkdir(parents=True)
            workspace.require_source_free(child)
            marker=root/'parent/.git'
            for kind in ('directory','file','dangling'):
                if kind=='directory':marker.mkdir()
                elif kind=='file':marker.write_text('gitdir: elsewhere')
                else:marker.symlink_to(root/'missing')
                with self.assertRaisesRegex(ValueError,'CLIENT_WORKSPACE_GIT_ANCESTOR'):
                    workspace.require_source_free(child)
                if kind=='directory':marker.rmdir()
                else:marker.unlink()
            for name in ('objects','refs'):(root/name).mkdir()
            (root/'HEAD').write_text('ref: refs/heads/main')
            with self.assertRaisesRegex(ValueError,'CLIENT_WORKSPACE_GIT_ANCESTOR'):
                workspace.require_source_free(child)

    def test_deadline_starts_no_child_and_timeout_reaps_descendants(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary).resolve();marker=root/'started'
            argv=[sys.executable,'-c',f'from pathlib import Path;Path({str(marker)!r}).touch()']
            with self.assertRaisesRegex(ValueError,'RUN_TIME_LIMIT'):
                pair.supervise(argv,root,time.time()-1,root/'expired')
            self.assertFalse(marker.exists())
            self.assertNotIn('client_pgid',pair.read(root/'expired/process.json'))
            child=root/'child.py';child.write_text('import time\ntime.sleep(30)\n')
            parent=root/'parent.py';parent.write_text('import subprocess,sys,time\n'
                f'p=subprocess.Popen([sys.executable,{str(child)!r}],start_new_session=True)\n'
                'time.sleep(30)\n')
            with self.assertRaisesRegex(ValueError,'RUN_TIME_LIMIT'):
                pair.supervise([sys.executable,str(parent)],root,time.time()+1,root/'timeout')
            row=pair.read(root/'timeout/process.json')
            self.assertTrue(row['processes_reconciled']);self.assertGreaterEqual(len(row['processes']),2)
            pair.processes.require_quiescent({'runs':[row]})


class PairTests(unittest.TestCase):
    def setUp(self):
        if not os.environ.get('STRUCTURED_PASS_XASM'):self.skipTest('Pinned assembler required')
        temporary=tempfile.TemporaryDirectory(prefix='structured-pair-test-');self.addCleanup(temporary.cleanup)
        self.root=Path(temporary.name).resolve()
        retained=tempfile.TemporaryDirectory(prefix='pair-retained-',dir=ROOT/'tmp');self.addCleanup(retained.cleanup)
        self.c=fixture.prepare(Path(retained.name)/'fixture')
        self.task=self.root/'task.txt';self.task.write_text('Publish the synthetic fixture.\n')
        prompts=self.root/'prompts';prompts.mkdir()
        for role in pair.ROLES:(prompts/(role+'.md')).write_text('Synthetic offline client fixture.\n')
        declaration=json.loads((ROOT/'tests/fixtures/codex_tool_declaration.json').read_text())
        codex_path=self.root/'codex';claude_path=self.root/'claude'
        # These programs simulate provider output and explicitly exercise the
        # service in the test coordinator. They are not confinement evidence.
        common=('import json,os,sys\nfrom pathlib import Path\n'
            f'sys.path[:0]=[{str(ROOT/"scripts")!r},{str(ROOT/"tests")!r}]\n'
            'from structured_pass.launcher import Corridor\nimport structured_pass_fixture as fixture\n'
            f'session=Path({str(self.c.root)!r})\n'
            'def emit(x):print(json.dumps(x),flush=True)\n')
        codex_path.write_text('#!'+sys.executable+'\n'+common+'''
if sys.argv[-2:]==['login','status']:
 print('Logged in using ChatGPT');sys.exit(0)
message=sys.stdin.read()
home=Path(os.environ['CODEX_HOME']);folder=home/'sessions';folder.mkdir(exist_ok=True)
(folder/'rollout-fixture.jsonl').write_text(json.dumps({'type':'session_meta','payload':{'id':'fixture-thread'}})+'\\n'+json.dumps({'type':'response_item','payload':{'type':'additional_tools','id':'declaration','tools':DECLARATION}})+'\\n')
emit({'type':'thread.started','thread_id':'fixture-thread'});emit({'type':'turn.started'})
if message.startswith('Publish'):
 c=Corridor(session);g=c.editor.state['current'];p=c.dispatch('preview',{'generation':g,'operations':fixture.rename_ops(c,g)},'implementer')
 cid=c.dispatch('confirm',{'generation':g,'preview_digest':p['preview_digest']},'implementer')['candidate']
 assert c.dispatch('validate',{'cid':cid},'implementer')['status']=='validated'
 c.dispatch('publish',{'cid':cid},'implementer');c.status('implementer')
emit({'type':'turn.completed','usage':{'input_tokens':100,'cached_input_tokens':0,'output_tokens':10}})
'''.replace('DECLARATION',repr(declaration)))
        claude_path.write_text('#!'+sys.executable+'\n'+common+'''
if '--version' in sys.argv:print('offline-fixture');sys.exit(0)
if 'auth' in sys.argv:print(json.dumps({'loggedIn':True,'authMethod':'claude.ai'}));sys.exit(0)
emit({'type':'system','subtype':'init','tools':['Read','mcp__facts__operation'],'additional_directories':[],'model':'fixture','permissionMode':'dontAsk'})
c=Corridor(session);status=c.status('reviewer')
c.dispatch('request-changes',{'ticket':status['ticket'],'report':'Verdict: CHANGES_REQUESTED\\n\\nSynthetic review finding.\\n\\n## Learning Candidates\\n\\n_None._\\n'},'reviewer')
emit({'type':'assistant','message':{'id':'fixture-response'}})
emit({'type':'result','subtype':'success','is_error':False,'result':'Review delivered.','num_turns':1})
''')
        for path in (codex_path,claude_path):path.chmod(0o700)
        (self.root/'codex-code-mode-host').write_text('disabled fixture host')
        self.lock=Path(os.environ.get('NESREV_HEAVY_RUN_LOCK',str(self.root/'heavy.lock')))
        self.impl=self.root/'impl';self.rev=self.root/'rev'
        codex.prepare(self.impl,session=self.c.root,prompt=prompts/'implementer.md',model='fixture',effort='high',
            client=codex_path,interpreter=sys.executable,service_root=ROOT,heavy_lock=self.lock,message=self.task.read_text())
        config=claude.prepare(self.rev,self.c.root,prompts,model='fixture',effort='high',client=claude_path,
                             interpreter=sys.executable,heavy_lock=self.lock)
        self.addCleanup(shutil.rmtree,Path(config['roles']['reviewer']['workspace']).parent)
        self.pair=self.root/'pair'
        pair.prepare(self.pair,self.c.root,self.impl,self.rev,self.task)
        # The test suite already owns the shared heavy lock. Omit only the
        # nested acquisition; real admission exercises the unmodified wrapper.
        self.original_argv=pair.adapter_argv
        def under_existing_lock(*args):
            argv=self.original_argv(*args)
            return argv[argv.index('--')+1:]
        patched=patch.object(pair,'adapter_argv',side_effect=under_existing_lock)
        patched.start();self.addCleanup(patched.stop)
        notify=self.pair/'notify'
        notify.write_text('#!'+sys.executable+'\n'+
            f'import sys\nsys.path.insert(0,{str(ROOT/"scripts")!r})\n'+
            'import structured_pair_launcher as p\noriginal=p.adapter_argv\n'+
            'def inherited(*args):\n argv=original(*args);return argv[argv.index("--")+1:]\n'+
            'p.adapter_argv=inherited\n'+
            f'p.deliver({str(self.pair)!r},sys.argv[1],sys.argv[3],notified_status=sys.argv[2])\n')
        launch=pair.read(self.pair/'launch.json');launch['files'][str(notify)]=pair.sha(notify)
        pair.save(self.pair/'launch.json',launch)

    def authorize(self, **changes):
        return pair.authorize(self.pair,**{'owner_message':'Synthetic offline test only','deadline':time.time()+90,
            'invocations':4,'responses':5,'turn_seconds':30,'purpose':'access_preflight',**changes})

    def test_real_watch_notifier_adapter_handoff_and_same_thread(self):
        grant=self.authorize()
        first=pair.deliver(self.pair,'implementer',self.pair/'task.txt',kind='initial')
        self.assertEqual(first['result'],'handoff')
        saved=pair.review.read_state(self.c.root/'handoff')
        prompt=self.c.root/'handoff'/saved['prompts']['reviewer'];exact=prompt.read_bytes()
        argv=[sys.executable,'-B',str(ROOT/'scripts/agent_review.py'),'--repo',str(self.c.root/'handoff'),
              '--expected-run-id','sample-pass-1','watch','--role','reviewer','--once','--notify',str(self.pair/'notify')]
        result=subprocess.run(argv,capture_output=True,text=True,timeout=40)
        self.assertEqual(result.returncode,0,result.stderr)
        state=pair.read(self.pair/'state.json');second=state['turns'][1]
        self.assertEqual(Path(second['message']).read_bytes(),exact)
        self.assertEqual(second['result'],'handoff')
        budget=pair.read(self.rev/'budget.json');self.assertEqual(budget['deadline'],grant['deadline'])
        run=budget['runs'][0]
        self.assertEqual((self.rev/'runs'/run['id']/'message.txt').read_bytes(),exact)
        saved=pair.review.read_state(self.c.root/'handoff')
        third=pair.deliver(self.pair,'implementer',self.c.root/'handoff'/saved['prompts']['implementer'],notified_status=saved['status'])
        self.assertEqual(third['result'],'unfinished')
        state=pair.read(self.impl/'state.json');self.assertEqual(state['thread_id'],'fixture-thread')
        self.assertEqual([r['continuation'] for r in state['runs']],[False,True])
        self.assertNotEqual(state['runs'][0]['message_sha256'],state['runs'][1]['message_sha256'])
        with self.assertRaisesRegex(ValueError,'PAIR_RECOVERY_REQUIRED'):
            pair.deliver(self.pair,'implementer',self.task,kind='owner')
        steering=self.root/'steering.txt';steering.write_bytes(b'Record remaining gap.\r\n')
        fourth=pair.continue_turn(self.pair,'implementer',steering)
        self.assertEqual(Path(fourth['message']).read_bytes(),steering.read_bytes())
        self.assertEqual(fourth['result'],'unfinished')
        self.assertEqual(pair.read(self.rev/'budget.json')['deadline'],grant['deadline'])

    def test_no_authority_or_expired_window_starts_nothing(self):
        with self.assertRaisesRegex(ValueError,'INFERENCE_NOT_AUTHORIZED'):
            pair.deliver(self.pair,'implementer',self.task,kind='initial')
        self.assertEqual(pair.read(self.impl/'state.json')['runs'],[])
        self.authorize(deadline=time.time()+.05);time.sleep(.06)
        with self.assertRaisesRegex(ValueError,'RUN_TIME_LIMIT'):
            pair.deliver(self.pair,'implementer',self.task,kind='initial')
        self.assertEqual(pair.read(self.impl/'state.json')['runs'],[])

    def test_wrong_pairing_code_task_and_ancestry_refuse(self):
        path=self.pair/'launch.json';original=path.read_bytes();config=json.loads(original)
        for change in ({'clients':{'implementer':'claude','reviewer':'codex'}},
                       {'declarations':{}},{'handoff':str(self.root/'wrong')}):
            pair.save(path,{**config,**change})
            with self.assertRaises(ValueError):pair.verify(self.pair)
            path.write_bytes(original)
        (self.root/'.git').write_text('gitdir: elsewhere')
        with self.assertRaisesRegex(ValueError,'CLIENT_WORKSPACE_GIT_ANCESTOR'):pair.verify(self.pair)
        (self.root/'.git').unlink()
        (self.pair/'task.txt').write_text('changed')
        with self.assertRaisesRegex(ValueError,'PAIR_CONFIGURATION_CHANGED'):pair.verify(self.pair)

    def test_claude_workspace_ancestry_rechecked(self):
        config=pair.read(self.rev/'launch.json');workspace_root=Path(config['roles']['reviewer']['workspace']).parent
        (workspace_root/'.git').mkdir()
        with self.assertRaisesRegex(ValueError,'CLIENT_WORKSPACE_GIT_ANCESTOR'):claude.verify(self.rev)

    def test_nonzero_adapter_never_becomes_handoff_or_retry(self):
        self.authorize()
        with patch.object(pair,'adapter_argv',return_value=[sys.executable,'-c','raise SystemExit(7)']):
            with self.assertRaisesRegex(ValueError,'CLIENT_RUN_FAILED'):
                pair.deliver(self.pair,'implementer',self.task,kind='initial')
        state=pair.read(self.pair/'state.json');self.assertEqual(state['stop'],'recovery-required')
        self.assertEqual(len(state['turns']),1)
        with self.assertRaisesRegex(ValueError,'PAIR_RECOVERY_REQUIRED'):
            pair.continue_turn(self.pair,'implementer',self.task)
        with self.assertRaisesRegex(ValueError,'PAIR_RECOVERY_REQUIRED'):
            pair.extend(self.pair,owner_message='Synthetic extension',deadline=time.time()+180)

    def test_extension_is_explicit_shared_and_preserves_history(self):
        old=self.authorize()
        before=pair.read(self.pair/'state.json')
        updated=pair.extend(self.pair,owner_message='Synthetic extension only',deadline=old['deadline']+60,invocations=2,responses=3)
        self.assertEqual(pair.read(self.pair/'state.json'),before)
        self.assertEqual(updated['max_invocations'],6)
        self.assertEqual(pair.read(self.rev/'budget.json')['max_responses'],8)
        self.assertEqual(pair.read(self.rev/'budget.json')['deadline'],updated['deadline'])
        self.assertEqual(pair.read(self.impl/'authorization.json')['deadline'],updated['deadline'])
        self.assertEqual(len(list((self.pair/'extensions').glob('*.json'))),1)
        with self.assertRaisesRegex(ValueError,'PAIR_APPLICATION_NOT_AUTHORIZED'):pair.apply_closed(self.pair)

    def test_tmux_admission_check_and_expiry_before_worker_start(self):
        args=Namespace(prepared=self.pair,check=True,session='fixture',no_attach=True)
        with patch('builtins.print'),patch.object(pair,'authority',side_effect=AssertionError('check must remain offline')):
            pair.tmux_launch(args,lambda *a,**k:self.fail('tmux started'),lambda *a:self.fail('attached'))
        grant=self.authorize();args.check=False;calls=[]
        now=time.time()
        def tmux(*argv,**kwargs):
            nonlocal now
            calls.append(argv)
            if argv[0]=='new-session':return Namespace(stdout='$fixture\t%one\n')
            if argv[0]=='split-window':now=grant['deadline']+1;return Namespace(stdout='%two\n')
            return Namespace(stdout='')
        with patch.object(pair.time,'time',side_effect=lambda:now):
            with self.assertRaisesRegex(ValueError,'RUN_TIME_LIMIT'):pair.tmux_launch(args,tmux,lambda *a:None)
        self.assertFalse(any(c[0]=='respawn-pane' for c in calls))
        self.assertEqual(calls[-1],('kill-session','-t','$fixture'))
        self.assertEqual(pair.read(self.impl/'state.json')['runs'],[])

    def test_worker_watches_only_the_session_store(self):
        self.authorize()
        with patch.object(pair,'deliver'),patch.object(pair,'supervise',return_value=4) as supervise:
            self.assertEqual(pair.worker(self.pair,'implementer'),4)
        argv=supervise.call_args.args[0]
        self.assertEqual(argv[argv.index('--repo')+1],str(self.c.root/'handoff'))
        self.assertEqual(argv[argv.index('--expected-run-id')+1],'sample-pass-1')
        self.assertEqual(argv[argv.index('--interval')+1],'2')

    def test_exhausted_allowance_starts_no_client(self):
        grant=self.authorize(invocations=1)
        state=pair.read(self.pair/'state.json');state['turns']=[{'result':'handoff'}]
        pair.save(self.pair/'state.json',state)
        with patch.object(pair,'supervise',side_effect=AssertionError('client started')):
            with self.assertRaisesRegex(ValueError,'INVOCATION_LIMIT'):
                pair.deliver(self.pair,'reviewer',self.task)

    def test_notification_identity_survives_a_lost_seen_marker(self):
        self.authorize()
        g=self.c.editor.state['current'];p=self.c.dispatch('preview',{'generation':g,'operations':fixture.rename_ops(self.c,g)},'implementer')
        cid=self.c.dispatch('confirm',{'generation':g,'preview_digest':p['preview_digest']},'implementer')['candidate']
        self.assertEqual(self.c.dispatch('validate',{'cid':cid},'implementer')['status'],'validated')
        self.c.dispatch('publish',{'cid':cid},'implementer');self.c.status('implementer')
        saved=pair.review.read_state(self.c.root/'handoff');token=pair.review.notify_token(saved,'reviewer')
        state=pair.read(self.pair/'state.json');state['turns']=[{'result':'handoff','notification':token}]
        pair.save(self.pair/'state.json',state)
        with patch.object(pair,'supervise',side_effect=AssertionError('duplicate started')):
            with self.assertRaisesRegex(ValueError,'PAIR_DUPLICATE_NOTIFICATION'):
                pair.deliver(self.pair,'reviewer',self.c.root/'handoff'/saved['prompts']['reviewer'],notified_status=saved['status'])

    def test_both_role_assemblies_must_carry_the_same_task_and_catalog(self):
        controller=Namespace(checked_editor=lambda:{'declared_inputs_sha256':'present'})
        fields={'task':'Current task','items':['one'],'manifest_sha256':'hash','pass_id':'1',
                'objective':'corridor','historical_label':'historical'}
        left=self.root/'left.json';right=self.root/'right.json'
        pair.save(left,{**fields,'role':'implementer'});pair.save(right,{**fields,'role':'reviewer'})
        ci={'input_assembly':str(left)};cr={'roles':{'reviewer':{'input_assembly':str(right)}}}
        pair.check_inputs(controller,ci,cr,b'Current task')
        for change in ({'role':'implementer'},{'task':'old task'},{'items':[]}):
            pair.save(right,{**fields,'role':'reviewer',**change})
            with self.assertRaises(ValueError):pair.check_inputs(controller,ci,cr,b'Current task')

    def test_busy_public_error_is_not_internal_error(self):
        # Exercise the actual wire reduction; the dispatcher has separate lifecycle tests.
        output=io.StringIO()
        with patch.object(pair.Corridor,'dispatch',side_effect=ValueError('REVIEW_NOT_READY')):
            bridge.mcp(self.c.root,'reviewer',input_stream=io.StringIO(json.dumps({'id':1,'method':'tools/call',
                'params':{'name':'operation','arguments':{'operation':'approve','arguments':{}}}})+'\n'),output_stream=output)
        value=json.loads(json.loads(output.getvalue())['result']['content'][0]['text'])
        self.assertEqual(value['error'],'REVIEW_NOT_READY');self.assertFalse(value['retryable'])


if __name__=='__main__':unittest.main()
