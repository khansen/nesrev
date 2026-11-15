"""Naming eligibility and lifecycle tests; fixture gates are explicitly simulated."""
import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
from structured_pass import verification_policy as policy, gate_environment, producer, service
from structured_pass.model import certify
from structured_pass.launcher import Corridor
from structured_pass.application import apply
from structured_pass_fixture import prepare, git, closeout_ops, SOURCE


class AdmissionTests(unittest.TestCase):
    def setUp(self):
        if not os.environ.get('STRUCTURED_PASS_XASM'):
            self.skipTest('Pinned producer required')
        (ROOT/'tmp').mkdir(exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(dir=ROOT/'tmp', prefix='admission-test-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def fixture(self, early=True):
        original = prepare(self.root)
        repo = self.root/'repo'
        if early:
            source = repo/SOURCE
            source.write_bytes(source.read_bytes().replace(b'Cell', b'L1234'))
        # Simulated gate preserves the naming refusal's actual subprocess status.
        (repo/'scripts/project_verify.sh').write_text('''#!/bin/bash
set -eu
if [ -e defect ]; then exit 5; fi
if rg -q '\\bL[0-9A-F]{4,5}\\b' projects/sample/asm/sample.asm; then
    if [ "${ALLOW_UNRESOLVED_LXXXX:-0}" != 1 ]; then exit 3; fi
fi
if [ -e later-defect ]; then exit 7; fi
''')
        writer = repo/'scripts/project_pass_closeout.sh'
        writer.write_text(writer.read_text().replace('"$1" "$2"', '"$1" "$2" "$3"'))
        writer = repo/'scripts/fixture_closeout.py'
        writer.write_text(writer.read_text().replace("row[key]='pass'",
            "row[key]='pass (LXXXX allowed)' if key=='verify' and sys.argv[3]=='relaxed' else 'pass'"))
        git(repo, 'add', '.')
        git(repo, 'commit', '-qm', 'Configure simulated naming gate')
        profile = json.loads((self.root/'profile.json').read_text())
        source = (repo/SOURCE).read_bytes()
        folder = self.root/'baseline-gates'; folder.mkdir()
        env = gate_environment.environment(original.editor.state['gate_toolchain'], folder/'tmp')
        binding = policy.derive(git(repo, 'rev-parse', 'HEAD'), SOURCE, source, env)
        check = policy.run(repo, 'sample', folder, env, binding)
        self.assertEqual(check['exit_code'], 0)
        baseline = self.root/'baseline-v2.json'
        baseline.write_text(json.dumps({'checks': [check] + [
            {'target': t, 'exit_code': 0} for t in ('project-inventory','project-process-check','project-docs-check')]}))
        profile.update(schema='current-project-profile-v2', verification_policy=binding,
            base_commit=binding['base_commit'], source_sha256=binding['source_sha256'],
            baseline_path=str(baseline), baseline_sha256=producer.sha(baseline))
        service.write_json(self.root/'profile-v2.json', profile)
        certify(repo/SOURCE, self.root/'capture-v2', repo/original.editor.reference)
        return Corridor.initialize(self.root/'session-v2', repo, self.root/'capture-v2', self.root/'store',
            run_id='sample-pass-v2', objective='Exercise service-owned naming policy',
            project_profile=self.root/'profile-v2.json')

    def candidate(self, controller, operations):
        generation = controller.editor.state['current']
        preview = controller.dispatch('preview', {'generation':generation,'operations':operations}, 'implementer')
        cid = controller.dispatch('confirm', {'generation':generation,'preview_digest':preview['preview_digest']}, 'implementer')['candidate']
        return cid, controller.dispatch('validate', {'cid':cid}, 'implementer')

    def test_relaxed_lifecycle_application_and_archive_are_qualified(self):
        c = self.fixture()
        with patch.dict(os.environ, {'ALLOW_UNRESOLVED_LXXXX':'1','VERIFY_MODE':'relaxed'}):
            cid, result = self.candidate(c, closeout_ops(c, c.editor.state['current']))
        self.assertEqual(result['status'], 'validated', result)
        published = c.dispatch('publish', {'cid':cid}, 'implementer')
        c.dispatch('approve', {'ticket':published['review']['artifact_id'],
            'report':'Verdict: APPROVED\n\nSimulated gate lifecycle only.'}, 'reviewer')
        closed = c.closeout()
        archive = (c.root/'handoff'/closed['archive']).read_text()
        self.assertIn('pass (LXXXX allowed)', archive)
        self.assertIn('not a maturity assessment', archive)
        target = self.root/'target'
        git(self.root/'repo', 'clone', '-q', '--no-hardlinks', str(self.root/'repo'), str(target))
        ref = target/c.editor.reference; ref.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(self.root/'repo'/c.editor.reference, ref)
        git(target, 'checkout', '-qb', 'projects')
        git(target, 'config', 'user.name', 'Fixture'); git(target, 'config', 'user.email', 'fixture@example.invalid')
        result = apply(c.root, target, commit=True)
        check = next(g for g in result['gates'] if g['target']=='project-verify')
        self.assertFalse(check['verification']['strict_green'])
        self.assertEqual(check['verification']['mode'], 'naming-only')
        self.assertEqual(apply(c.root, target, commit=True), result)

    def test_clean_start_cannot_gain_generic_name_even_with_both_environment_switches(self):
        c = self.fixture(False); generation = c.editor.state['current']; m = c.editor.model(generation)
        n = m.declarations['Cell']
        operation = {'kind':'rename','declaration_id':m.ids[n], 'old_name':'Cell','new_name':'L1234',
                     'preimage':m.statement(n)['preimage_sha256']}
        ledger = {'kind':'ledger_append','path':c.editor.ledger,
                  'preimage':c.editor.state['generations'][generation]['manifest'][c.editor.ledger],
                  'rows':[{'old_name':'Cell','new_name':'L1234','reason':'Negative naming control',
                           'confidence':'high','pass_id':'1'}]}
        with patch.dict(os.environ, {'ALLOW_UNRESOLVED_LXXXX':'1','VERIFY_MODE':'relaxed'}):
            _, result = self.candidate(c, [operation, ledger, *closeout_ops(c, generation)])
        self.assertEqual(result['status'], 'rejected', result)
        gates = result['gates']
        self.assertEqual(gates[0]['exit_code'], 3)
        self.assertEqual(len(gates[0]['verification']['attempts']), 1)
        self.assertEqual(gates[0]['verification']['policy']['eligibility'], 'strict')

    def test_removing_last_name_requires_an_actual_strict_run(self):
        c = self.fixture(); generation = c.editor.state['current']; m = c.editor.model(generation)
        n = m.declarations['L1234']
        operations = [{'kind':'rename','declaration_id':m.ids[n], 'old_name':'L1234','new_name':'Capacity',
                       'preimage':m.statement(n)['preimage_sha256']},
                      {'kind':'ledger_append','path':c.editor.ledger,
                       'preimage':c.editor.state['generations'][generation]['manifest'][c.editor.ledger],
                       'rows':[{'old_name':'L1234','new_name':'Capacity','reason':'Complete synthetic naming',
                                'confidence':'high','pass_id':'1'}]}, *closeout_ops(c, generation)]
        cid, result = self.candidate(c, operations)
        self.assertEqual(result['status'], 'validated', result)
        check = result['gates'][0]['verification']
        self.assertTrue(check['strict_green'])
        self.assertEqual(check['after']['distinct_names'], 0)
        self.assertEqual([(a['mode'],a['exit_code']) for a in check['attempts']], [('strict',0)])

    def test_requests_cannot_select_mode_and_old_profiles_remain_strict(self):
        c = prepare(self.root)
        self.assertIsNone(c.editor.verification_policy)
        g = c.editor.state['current']
        with self.assertRaisesRegex(ValueError, 'REQUEST_SCHEMA'):
            c.dispatch('preview', {'generation':g,'operations':closeout_ops(c,g),
                                  'verification_policy':{'eligibility':'naming-only'}}, 'implementer')
        operations = closeout_ops(c,g); operations[-1]['VERIFY_MODE']='relaxed'
        with self.assertRaises(ValueError):
            self.candidate(c, operations)

    def test_override_environments_are_rejected_not_forwarded(self):
        c = self.fixture(False)
        folder = self.root/'override'; folder.mkdir()
        env = gate_environment.environment(c.editor.state['gate_toolchain'], folder/'tmp')
        for override in ({'ALLOW_UNRESOLVED_LXXXX':'1'}, {'VERIFY_MODE':'relaxed'},
                         {'ALLOW_UNRESOLVED_LXXXX':'1','VERIFY_MODE':'relaxed'}):
            with self.subTest(override=override):
                with self.assertRaisesRegex(ValueError, 'GATE_ENVIRONMENT_INVALID'):
                    policy.run(self.root/'repo','sample',folder, env|override, c.editor.verification_policy)
                with self.assertRaisesRegex(ValueError, 'GATE_ENVIRONMENT_INVALID'):
                    gate_environment.closeout_environment(env|override, {})

    def test_gate_eligibility_is_not_recomputed_from_candidate(self):
        c = self.fixture(False)
        source = self.root/'repo'/SOURCE
        source.write_bytes(source.read_bytes().replace(b'Cell', b'L1234'))
        folder = self.root/'new-name'; folder.mkdir()
        env = gate_environment.environment(c.editor.state['gate_toolchain'], folder/'tmp')
        result = policy.run(self.root/'repo','sample',folder,env,c.editor.verification_policy)
        self.assertEqual(result['exit_code'], 3)
        self.assertEqual(len(result['verification']['attempts']), 1)

    def test_resume_refuses_missing_changed_policy_or_base(self):
        c = self.fixture(); original = c.editor.state_path.read_bytes()
        for replacement in (None, dict(c.editor.verification_policy, eligibility='strict')):
            state = json.loads(original)
            if replacement is None: state.pop('verification_policy')
            else: state['verification_policy'] = replacement
            service.write_json(c.editor.state_path, state)
            with self.subTest(replacement=replacement):
                with self.assertRaisesRegex(ValueError, 'VERIFICATION_POLICY_CHANGED'):
                    Corridor(c.root)
            c.editor.state_path.write_bytes(original)
        source = self.root/'repo'/SOURCE
        source.write_bytes(source.read_bytes()+b'; changed starting source\n')
        with self.assertRaisesRegex(ValueError, 'VERIFICATION_POLICY_CHANGED'):
            Corridor(c.root)

    def test_missing_profile_policy_cannot_default_to_relaxed(self):
        c = self.fixture(); path = self.root/'profile-v2.json'
        profile = json.loads(path.read_text()); profile.pop('verification_policy')
        service.write_json(path, profile)
        with self.assertRaisesRegex(ValueError, 'PROJECT_PROFILE_CHANGED'):
            c.status('reviewer')
        from structured_pass.current_project import service_class
        with self.assertRaisesRegex(ValueError, 'PROJECT_PROFILE_INVALID'):
            service_class(path)
        profile['verification_policy'] = None
        service.write_json(path, profile)
        with self.assertRaisesRegex(ValueError, 'VERIFICATION_POLICY_INVALID'):
            service_class(path)

    def test_real_dependency_order_and_later_failures_are_not_waived(self):
        c = self.fixture(); folder = self.root/'failures'; folder.mkdir()
        env = gate_environment.environment(c.editor.state['gate_toolchain'], folder/'tmp')
        for marker, code, modes in (('defect',5,['strict']), ('later-defect',7,['strict','naming-only'])):
            with self.subTest(marker=marker):
                path = self.root/'repo'/marker; path.touch()
                result = policy.run(self.root/'repo','sample',folder,env,c.editor.verification_policy)
                self.assertEqual(result['exit_code'], code)
                self.assertEqual([x['mode'] for x in result['verification']['attempts']], modes)
                path.unlink()

    def test_naming_count_matches_canonical_lexical_rule(self):
        data = 'L1234: L1234\n; LABCDE and L12345\nXL1234 L123456 _L1234 l1234\n\u0301L2234 L2234\u0301\n'.encode()
        file = self.root/'lexical.txt'; file.write_bytes(data)
        names = subprocess.check_output(['rg','-o',r'\bL[0-9A-F]{4,5}\b', str(file)]).splitlines()
        lines = subprocess.check_output(['rg','-n',r'\bL[0-9A-F]{4,5}\b|^L[0-9A-F]{4,5}:', str(file)]).splitlines()
        config = gate_environment.configure(Path(os.environ['STRUCTURED_PASS_XASM']), self.root/'count-home')
        env = gate_environment.environment(config, self.root/'count-tmp')
        self.assertEqual(policy.counts(data, env), {'distinct_names':len(set(names)), 'matching_lines':len(lines)})


if __name__ == '__main__':
    unittest.main()
