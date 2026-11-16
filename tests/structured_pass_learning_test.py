"""Integrated observations, ordinary-import parity and journal recovery; simulated gates."""
import io
import json
from pathlib import Path
import shutil
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import agent_review as api
import process_friction as friction
from structured_pass import application, learning, service
from structured_pass.bridge import mcp
from structured_pass.launcher import Corridor
from structured_pass_fixture import closeout_ops, rename_ops, git
import structured_pass_review_fixes_test as previous


def section(body='_None._'):
    return '\n\n## Learning Candidates\n\n' + body + '\n'


class LearningTests(unittest.TestCase):
    setUp = previous.ReviewWorkflowTests.setUp
    bridge = previous.ReviewWorkflowTests.bridge
    a = '- Preserve the first implementation observation.'
    b = '- Preserve the requested-changes observation.'
    response_observation = '- Preserve the accepted response observation.'
    d = '- Preserve the replacement candidate observation.'
    e = '- Preserve the approving review observation.'
    manual = '- Keep the owner observation verbatim.'

    def edit(self, operations):
        self.c = Corridor(self.c.root)
        generation = self.c.editor.state['current']
        preview = self.bridge('preview', {'generation': generation, 'operations': operations})
        candidate = self.bridge('confirm', {'generation': generation,
                                            'preview_digest': preview['preview_digest']})['candidate']
        result = self.bridge('validate', {'cid': candidate})
        self.assertEqual(result['status'], 'validated', result)
        published = self.bridge('publish', {'cid': candidate})
        self.c = Corridor(self.c.root)
        return published

    def target(self):
        target = self.root / 'target'
        git(self.root / 'repo', 'clone', '-q', '--no-hardlinks', str(self.root / 'repo'), str(target))
        reference = target / self.c.editor.reference
        reference.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(self.root / 'repo' / self.c.editor.reference, reference)
        git(target, 'checkout', '-qb', 'projects')
        git(target, 'config', 'user.name', 'Fixture')
        git(target, 'config', 'user.email', 'fixture@example.invalid')
        return target

    def lifecycle(self, *, empty=False):
        ops = rename_ops(self.c, self.c.editor.state['current'])
        ops[-1]['learning'] = '_None._' if empty else self.a
        first = self.edit(ops)
        if not empty:
            self.bridge('request-changes', {'ticket': first['review']['artifact_id'],
                'report': 'Verdict: CHANGES_REQUESTED\nClarify the evidence.' + section(self.b)}, 'reviewer')
            ops = closeout_ops(self.c, self.c.editor.state['current'], 'Clarified fixture evidence.')
            ops[-1]['learning'] = self.d
            first = self.edit(ops)
            self.bridge('reready', {'response': ('Clarified the evidence.' + section(self.response_observation)).replace('\n', '\r\n')})
        self.bridge('approve', {'ticket': first['review']['artifact_id'],
            'report': 'Verdict: APPROVED\nSynthetic lifecycle only.' + section('_None._' if empty else self.e)}, 'reviewer')
        self.c = Corridor(self.c.root)
        closed = self.bridge('closeout', {})
        return closed, self.target()

    def commit_queue(self, target):
        queue, _ = friction.project_paths(target, 'sample')
        queue.write_text('# Process Friction\n\n' + self.a + '\n')
        git(target, 'add', '--', str(queue));git(target, 'commit', '-qm', 'Fixture queue')
        return queue

    def triage(self, target):
        queue = self.commit_queue(target)
        friction.triage(target, 'sample', [{'id': friction.candidate_id(self.a),
            'disposition': 'discarded', 'destinations': [],
            'rationale': 'Synthetic triage before application.'}], True)
        queue.write_text('# Process Friction\n\n' + self.manual + '\n')
        git(target, 'add', '--', 'projects/sample')
        git(target, 'commit', '-qm', 'Fixture committed triage')
        return queue

    def assert_sources(self, closed):
        bundle = learning.load(self.c, closed)
        self.assertEqual(len(bundle['sources']), 5)
        for text in (self.a, self.b, self.candidate_response, self.d, self.e):
            self.assertEqual(sum(text in item['text'] for item in bundle['sources']), 1)
        archive = (self.c.root / 'handoff' / closed['archive']).read_text()
        for item in bundle['sources']:
            self.assertIn('<a id="' + item['id'] + '"></a>', archive)
            self.assertIn(item['sha256'], archive)
            if item['id'].startswith('response-'):
                original = (self.c.root / 'handoff' / item['origin']['file']).read_bytes()
                self.assertIn(b'\r\n', original)
                self.assertEqual(item['text'].encode(), original)
                self.assertEqual(item['sha256'], item['origin']['sha256'])
        return bundle

    @property
    def candidate_response(self):
        return self.response_observation

    def oracle(self, target, closed, bundle):
        root = self.root / 'oracle'
        shutil.copytree(target / 'projects', root / 'projects')
        run = root / '.agents/runs' / bundle['run_id'];run.mkdir(parents=True)
        implementation = run / 'implementation.md'
        implementation.write_text('\n'.join(item['text'] for item in bundle['sources']
                                             if item['id'].startswith('implementer-')))
        for item in bundle['sources']:
            if not item['id'].startswith('implementer-'):
                (run / (item['id'] + '.md')).write_text(item['text'])
        state = {'project': 'sample', 'run_id': bundle['run_id'],
                 'review_head': closed['coverage']['pass_head'], 'implementation_note': str(implementation)}
        api.update_process_friction(root, state, '1', closed['archive'])
        queue, _ = friction.project_paths(root, 'sample')
        return friction.queue_candidates(queue.read_text(), str(queue.relative_to(root)))

    def test_integrated_sources_committed_triage_ordinary_oracle_and_retry(self):
        closed, target = self.lifecycle()
        bundle = self.assert_sources(closed)
        queue = self.triage(target)
        _, receipts = friction.project_paths(target, 'sample');receipt_bytes = receipts.read_bytes()
        expected = self.oracle(target, closed, bundle)
        parent = git(target, 'rev-parse', 'HEAD')
        result = application.apply(self.c.root, target, commit=True)
        self.assertEqual(result['head'], parent)
        actual = friction.queue_candidates(queue.read_text(), str(queue.relative_to(target)))
        self.assertEqual(set(actual), set(expected))
        self.assertEqual(set(actual), {friction.candidate_id(t) for t in
                                     (self.b, self.candidate_response, self.d, self.e, self.manual)})
        for key in actual:self.assertEqual(actual[key]['content'], expected[key]['content'])
        for key, item in actual.items():
            if key != friction.candidate_id(self.manual):
                self.assertTrue(all(s.startswith(closed['archive'] + '#') for s in item['sources']))
        self.assertEqual(receipts.read_bytes(), receipt_bytes)
        before = queue.read_bytes()
        self.assertEqual(application.apply(self.c.root, target, commit=True), result)
        self.assertEqual(queue.read_bytes(), before)
        self.assertEqual(git(target, 'rev-parse', 'HEAD'), result['commit'])
        self.assertEqual(self.bridge('closeout', {}), closed)
        queue.write_text('# Process Friction\n\n' + self.manual + '\n')
        git(target, 'add', '--', str(queue));git(target, 'commit', '-qm', 'Later fixture queue edit')
        later = queue.read_bytes()
        self.assertEqual(application.apply(self.c.root, target, commit=True), result)
        self.assertEqual(queue.read_bytes(), later)

    def test_empty_sources_never_create_queue_or_receipts(self):
        closed, target = self.lifecycle(empty=True)
        result = application.apply(self.c.root, target, commit=True)
        for path in friction.project_paths(target, 'sample'):
            self.assertFalse(path.exists());self.assertNotIn(str(path.relative_to(target)), result['paths'])
        self.assertEqual(len(learning.load(self.c, closed)['sources']), 2)

    def test_dirty_queue_refuses_then_commit_and_retry_rebuilds(self):
        closed, target = self.lifecycle()
        queue = self.commit_queue(target);queue.write_text(queue.read_text() + self.manual + '\n')
        before = queue.read_bytes();head = git(target, 'rev-parse', 'HEAD')
        with self.assertRaisesRegex(ValueError, '^APPLICATION_FRICTION_DIRTY$'):
            application.apply(self.c.root, target, commit=True)
        self.assertEqual(queue.read_bytes(), before);self.assertEqual(git(target, 'rev-parse', 'HEAD'), head)
        self.assertFalse((self.c.root / 'application.json').exists())
        error = io.StringIO()
        with patch.object(sys, 'stderr', error):
            self.assertEqual(application.main(['--session', str(self.c.root), '--repo', str(target), '--commit']), 2)
        self.assertIn('Commit intended queue/receipt edits or restore them, then retry.', error.getvalue())
        git(target, 'add', '--', str(queue));git(target, 'commit', '-qm', 'Fixture queue edit')
        application.apply(self.c.root, target, commit=True)
        self.assertIn(self.manual, queue.read_text());self.assertIn(self.a, queue.read_text())

    def test_partial_queue_write_and_post_commit_failure_recover_exactly_once(self):
        closed, target = self.lifecycle()
        queue = self.triage(target);before = queue.read_bytes()
        original_replace = Path.replace
        def fail_after_queue(path, dest):
            result = original_replace(path, dest)
            if Path(dest) == queue:raise OSError('injected queue persistence interruption')
            return result
        with patch.object(Path, 'replace', fail_after_queue):
            with self.assertRaisesRegex(OSError, 'queue persistence'):
                application.apply(self.c.root, target, commit=True)
        self.assertNotEqual(queue.read_bytes(), before)
        frozen = json.loads((self.c.root / 'application.json').read_text())
        output = queue.read_bytes();original_write = service.write_json
        def fail_receipt(path, value):
            if Path(path).name == 'application.json' and value.get('status') == 'committed':
                raise OSError('injected final receipt interruption')
            return original_write(path, value)
        with patch.object(learning, 'build', side_effect=AssertionError('retry rebuilt queue')):
            with patch.object(service, 'write_json', fail_receipt):
                with self.assertRaisesRegex(OSError, 'final receipt'):
                    application.apply(self.c.root, target, commit=True)
            committed = git(target, 'rev-parse', 'HEAD')
            result = application.apply(self.c.root, target, commit=True)
        self.assertEqual(result['commit'], committed)
        self.assertEqual(git(target, 'rev-list', '--count', frozen['head'] + '..HEAD'), '1')
        self.assertEqual(result['friction'], frozen['friction'])
        self.assertEqual(result['paths'], frozen['paths']);self.assertEqual(queue.read_bytes(), output)

    def test_bad_receipts_and_source_tampering_refuse_before_writes(self):
        closed, target = self.lifecycle();queue = self.triage(target)
        _, receipts = friction.project_paths(target, 'sample')
        saved = receipts.read_bytes();data = json.loads(saved);data['receipts'][0]['content'] = self.e
        for malformed in (b'{broken', json.dumps(data).encode()):
            receipts.write_bytes(malformed);git(target, 'add', '--', str(receipts))
            git(target, 'commit', '-qm', 'Fixture invalid receipts')
            before = queue.read_bytes()
            with self.assertRaisesRegex(ValueError, '^LEARNING_INPUT_INVALID$'):
                application.apply(self.c.root, target, commit=True)
            self.assertEqual(queue.read_bytes(), before);self.assertFalse((self.c.root / 'application.json').exists())
        receipts.write_bytes(saved);git(target, 'add', '--', str(receipts));git(target, 'commit', '-qm', 'Fixture receipts restored')
        pin = self.c.root / 'handoff' / closed['learning_sources']['path']
        raw = pin.read_bytes();bundle = json.loads(raw);bundle['sources'][0]['text'] += 'Changed'
        pin.write_text(json.dumps(bundle))
        with self.assertRaisesRegex(ValueError, '^LEARNING_SOURCE_CHANGED$'):
            learning.load(self.c, closed)
        with self.assertRaisesRegex(ValueError, '^PUBLICATION_RECEIPT_MISMATCH$'):
            application.apply(self.c.root, target, commit=True)
        pin.write_bytes(raw)
        state_path = self.c.root / 'handoff/.agents/current.json';state = json.loads(state_path.read_text())
        response = self.c.root / 'handoff' / state['last_response'];response.write_text('Changed' + section())
        with self.assertRaisesRegex(ValueError, '^LEARNING_SOURCE_CHANGED$'):
            application.apply(self.c.root, target, commit=True)

    def test_required_sections_size_and_role_instructions(self):
        for role in ('implementer', 'reviewer'):
            output = io.StringIO()
            mcp(self.c.root, role, 'corridor', io.StringIO('{"id":1,"method":"tools/list"}\n'), output)
            description = json.loads(output.getvalue())['result']['tools'][0]['description']
            self.assertIn(api.LEARNING_CANDIDATE_GUIDANCE, description)
            self.assertIn("Don't repeat observations from your earlier published candidates, rework "
                          "responses or reports in this pass.", description)
            self.assertIn("Carry forward any from a candidate that did not publish.", description)
        generation = self.c.editor.state['current'];ops = rename_ops(self.c, generation)
        for bad in ('', 'None.', 'x\0y', 'x'*4096):
            with self.subTest(body=bad[:40]):
                ops[-1]['learning'] = bad
                with self.assertRaises(ValueError):
                    self.c.dispatch('preview', {'generation': generation, 'operations': ops}, 'implementer')
        # An escaped body at the cap still survives preview, validation, review and archive.
        ops[-1]['learning'] = '- ' + '"'*2046
        self.assertEqual(len(json.dumps(ops[-1]['learning']).encode()), 4096)
        published = self.edit(ops)
        before = (self.c.root / 'handoff/.agents/current.json').read_bytes()
        for bad in ('Verdict: APPROVED', 'Verdict: APPROVED\n```md' + section() + '```',
                    'Verdict: APPROVED' + section('None.'),
                    'Verdict: APPROVED' + section(self.a) + section(self.b)):
            with self.subTest(report=bad):
                with self.assertRaises(ValueError):
                    learning.check_report(bad)
                with self.assertRaises(ValueError):
                    self.c.dispatch('approve', {'ticket': published['review']['artifact_id'], 'report': bad}, 'reviewer')
                self.assertEqual((self.c.root / 'handoff/.agents/current.json').read_bytes(), before)
        with self.assertRaisesRegex(ValueError, '^REVIEWER_ONLY$'):
            self.c.dispatch('approve', {'ticket': published['review']['artifact_id'],
                'report': 'Verdict: APPROVED' + section()}, 'implementer')
        ticket = published['review']['artifact_id']
        base = self.c.status('reviewer')['handoff']['coverage']['pass_base']
        offset = 0;receipts = []
        while offset is not None:
            page = self.bridge('review', {'ticket': ticket, 'generation': ticket,
                'base_generation': base, 'offset': offset}, 'reviewer')
            receipts.extend(row['receipt'] for row in page['changes'] if row['kind'] == 'wrapper_closeout')
            offset = page['next_offset']
        self.assertEqual([r['learning'] for r in receipts], [ops[-1]['learning']])
        self.bridge('approve', {'ticket': ticket, 'report': 'Verdict: APPROVED' + section()}, 'reviewer')
        closed = self.bridge('closeout', {})
        self.assertIn(ops[-1]['learning'], learning.load(self.c, closed)['sources'][0]['text'])

    def test_multiple_responses_retained_orphan_excluded_and_missing_response_refused(self):
        closed, _ = self.lifecycle()
        ticket = closed['coverage']['pass_head']
        self.bridge('request-changes', {'ticket': ticket,
            'report': 'Verdict: CHANGES_REQUESTED' + section()}, 'reviewer')
        state_path = self.c.root / 'handoff/.agents/current.json';before = state_path.read_bytes()
        for text in ('No section.', '```md' + section() + '```', section('')):
            with self.assertRaises(ValueError):
                self.c.dispatch('reready', {'response': text}, 'implementer')
            self.assertEqual(state_path.read_bytes(), before)
        second = '- Preserve the later response too.'
        self.bridge('reready', {'response': section(second)})
        self.bridge('approve', {'ticket': ticket, 'report': 'Verdict: APPROVED' + section()}, 'reviewer')
        folder = self.c.root / 'handoff/.agents/runs' / self.c.config['run_id']
        orphan = section('- Never accepted orphan.')
        (folder / 'responses' / (service.digest(orphan.encode()) + '.md')).write_text(orphan)
        closed = self.bridge('closeout', {});bundle = learning.load(self.c, closed)
        responses = [s['text'] for s in bundle['sources'] if s['id'].startswith('response-')]
        self.assertEqual(len(responses), 2)
        self.assertIn(self.response_observation, responses[0]);self.assertIn(second, responses[1])
        self.assertNotIn(orphan, responses)
        state = json.loads(state_path.read_text());state['structured_review']['response_history'].pop(0)
        state_path.write_text(json.dumps(state))
        with self.assertRaisesRegex(ValueError, '^LEARNING_HISTORY_CHANGED$'):
            application.apply(self.c.root, self.root / 'target', commit=True)


if __name__ == '__main__':
    unittest.main()
