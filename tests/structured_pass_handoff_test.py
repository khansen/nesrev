import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
"""Real handoff commands, immutable metadata, ordered history and fail-closed coverage."""
import copy
import fcntl
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
from structured_pass import structured_handoff as subject
from structured_pass.structured_handoff import canonical, digest, windows
from structured_pass.verdict_bridge import Bridge
from structured_pass_windows_test import WindowCoverage

SCRIPTS = str(Path(__import__('process_friction').__file__).resolve().parent)


def coordinator(root, store, base, head, project='demo', editor_state=None):
    root.mkdir()
    subprocess.run(['git', 'init', '-q', str(root)], check=True)
    subprocess.run(['git', '-C', str(root), '-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                    '-c', 'commit.gpgsign=false', 'commit', '-q', '--allow-empty', '-m', 'Coordinator fixture'], check=True)
    command(root, 'init-structured', '--project', project, '--run-id', 'fixture-pass', '--store', str(store),
            '--base-artifact', base, '--head-artifact', head, '--reviewer', 'fixture-reviewer',
            *(['--editor-state',str(editor_state)] if editor_state else []))


def command(root, *args, error=None):
    result = subprocess.run([sys.executable, '-B', str(HERE.parent/'scripts/agent_review.py'), '--repo', str(root), *args],
        env={**os.environ, 'PYTHONPATH': SCRIPTS, 'PYTHONDONTWRITEBYTECODE': '1'}, capture_output=True, text=True)
    if error:
        if result.returncode != 2 or error not in result.stderr:
            raise AssertionError((error, result.returncode, result.stdout, result.stderr))
        return result.stderr
    if result.returncode:
        raise AssertionError((result.returncode, result.stdout, result.stderr))
    return json.loads(result.stdout)


def verdict(root, ticket, name='APPROVED', error=None):
    path = root/'report.md'
    path.write_text(f'Verdict: {name}\n\nSynthetic permission/coverage fixture, not an actual project review.\n')
    return command(root, 'approve' if name=='APPROVED' else 'request-changes',
                   '--window', ticket, '--review', str(path), error=error)


class HandoffTests(unittest.TestCase):
    def setUp(self):
        self.fixture = WindowCoverage(); self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.store = self.fixture.root; self.ids = self.fixture.states
        self.root = self.store/'coordinator'
        coordinator(self.root, self.store, self.ids[0], self.ids[8])

    def state(self):
        return json.loads((self.root/'.agents/current.json').read_text())

    def test_commands_cover_every_edge_and_archive_reports(self):
        late = verdict(self.root, self.ids[8])
        self.assertNotEqual(late['status'], 'APPROVED')
        self.assertEqual(len(late['coverage']['uncovered_edges']), 7)
        command(self.root, 'archive', '--pass-id', '1', error='REVIEW_COVERAGE_INCOMPLETE')
        complete = verdict(self.root, self.ids[7])
        self.assertEqual(complete['status'], 'APPROVED')
        saved = command(self.root, 'archive', '--pass-id', '1')
        text = (self.root/saved['archive']).read_text()
        self.assertIn(self.ids[7], text);self.assertIn(self.ids[8], text)
        self.assertEqual([e['ticket'] for e in self.state()['structured_review']['verdict_history']],
                         [self.ids[8], self.ids[7]])
        extended = command(self.root, 'advance-structured', '--head-artifact', self.ids[9])
        self.assertEqual(extended['coverage']['uncovered_edges'], [[self.ids[8],self.ids[9]]])
        command(self.root, 'archive', '--pass-id', '2', error='REVIEW_COVERAGE_INCOMPLETE')
        self.assertEqual(verdict(self.root, self.ids[9])['status'], 'APPROVED')

    def test_later_request_changes_supersedes_and_requires_reready(self):
        verdict(self.root,self.ids[7]);verdict(self.root,self.ids[8])
        rejected = verdict(self.root,self.ids[7],'CHANGES_REQUESTED')
        self.assertEqual(rejected['status'],'CHANGES_REQUESTED')
        self.assertEqual(len(rejected['coverage']['uncovered_edges']),7)
        verdict(self.root,self.ids[7],error='REVIEW_NOT_READY')
        response=self.root/'response.md';response.write_text('Synthetic disposition.\n')
        command(self.root,'reready','--head',self.ids[8],'--response',str(response))
        repaired=verdict(self.root,self.ids[7]);self.assertEqual(repaired['round'],2)
        self.assertEqual(repaired['status'],'APPROVED')

    def test_history_order_and_reports_are_checked(self):
        verdict(self.root,self.ids[8]);verdict(self.root,self.ids[7])
        state=self.state();path=self.root/'.agents/current.json';original=path.read_bytes()
        state['structured_review']['verdict_history'].reverse();path.write_text(json.dumps(state))
        command(self.root,'status','--json',error='VERDICT_HISTORY_CHANGED')
        path.write_bytes(original);state=self.state()
        report=self.root/state['structured_review']['verdict_history'][0]['review_file']
        report.write_text('Changed report')
        command(self.root,'archive','--pass-id','1',error='REVIEW_REPORT_CHANGED')

    def test_cropped_ticket_wrong_head_and_extra_history_refuse(self):
        verdict(self.root,self.ids[9],error='VERDICT_OUTSIDE_PASS')
        ticket=self.store/'reviews'/f'{self.ids[8]}.json';body=json.loads(ticket.read_text())
        body['artifacts']=body['artifacts'][1:];ticket.write_bytes(canonical(body))
        verdict(self.root,self.ids[8],error='PUBLICATION_RECEIPT_MISMATCH')

    def test_all_writes_and_reads_reload_under_shared_lock(self):
        with (self.root/'.agents/structured-review.lock').open('a+b') as lock:
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            for args in [('status','--json'),('advance-structured','--head-artifact',self.ids[9]),
                         ('archive','--pass-id','1')]:
                command(self.root,*args,error='REVIEW_STATE_BUSY')
        verdict(self.root,self.ids[8]);verdict(self.root,self.ids[7])
        self.assertEqual(len(self.state()['structured_review']['verdict_history']),2)

    def test_fixed_role_bridge_and_request_schema(self):
        config=self.root/'bridge.json'
        config.write_text(json.dumps({'role':'implementer','root':str(self.root),'run_id':'fixture-pass','scripts':SCRIPTS}))
        bridge=Bridge(config);before=(self.root/'.agents/current.json').read_bytes()
        for request,code in [({'operation':'approve','arguments':{'ticket':self.ids[8],'report':'Verdict: APPROVED\n'}},'REVIEWER_ONLY'),
                ({'operation':'request-changes','arguments':{'ticket':self.ids[8],'report':'Verdict: CHANGES_REQUESTED\n'}},'REVIEWER_ONLY'),
                ({'operation':'status','arguments':{'role':'reviewer'}},'REQUEST_SCHEMA'),
                ({'operation':'status','arguments':{'history':[]}},'REQUEST_SCHEMA')]:
            with self.assertRaisesRegex(ValueError,code):bridge.dispatch(request)
        self.assertEqual(before,(self.root/'.agents/current.json').read_bytes())

    def test_live_publisher_invalidates_approval_without_a_caller_head_update(self):
        from structured_pass.service import Service
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);shutil.copytree(self.store/'artifacts',root/'store/artifacts');shutil.copytree(self.store/'reviews',root/'store/reviews')
            base,old,new,project=self.ids[0],self.ids[7],self.ids[8],'demo'
            publisher=Service.__new__(Service);publisher.root=root/'editor';publisher.root.mkdir()
            publisher.state_path=publisher.root/'state.json'
            legacy={artifact:windows.receipt(root/'store',artifact)['legacy_generation'] for artifact in (base,old,new)}
            # Metadata-only fixture uses the real editor's atomic save and lock.
            publisher.state={'current':legacy[old],'pass_start_generation':legacy[base],
                'candidates':{},'retention':{'root':str(root/'store')},
                'generations':{legacy[a]:{'artifact':{'artifact_id':a}} for a in (base,old,new)}}
            publisher._write_locked=True;publisher.save();publisher._write_locked=False
            with publisher.transaction(write=True):pass
            target=root/'coordinator';coordinator(target,root/'store',base,old,project,publisher.state_path)
            self.assertEqual(verdict(target,old)['status'],'APPROVED')
            with publisher.transaction(write=True):
                publisher.state['current']=legacy[new];publisher.save()
                command(target,'archive','--pass-id','1',error='VALIDATION_IN_PROGRESS')
            command(target,'archive','--pass-id','1',error='REVIEW_COVERAGE_INCOMPLETE')
            status=command(target,'status','--json')
            self.assertEqual(status['coverage']['uncovered_edges'],[[old,new]])
            command(target,'advance-structured','--head-artifact',old,error='HEAD_OWNED_BY_PUBLISHER')
            self.assertEqual(verdict(target,new)['status'],'APPROVED')
            publisher.state_path.unlink()
            command(target,'archive','--pass-id','1',error='PUBLISHER_STATE_UNAVAILABLE')


if __name__=='__main__':
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(HandoffTests)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    raise SystemExit(not result.wasSuccessful())
