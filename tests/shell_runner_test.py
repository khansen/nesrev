#!/usr/bin/env python3
"""Exercise runner selection, reporting and Bash failure behavior in small repos."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class RunnerTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='shell runner test ')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.shell = self.root / 'tests/shell'
        self.cases = self.shell / 'cases'
        self.cases.mkdir(parents=True)
        for name in ('run_all.sh', 'run_all.py', 'lib.sh'):
            shutil.copyfile(ROOT / 'tests/shell' / name, self.shell / name)
        shutil.copyfile(ROOT / 'Makefile', self.root / 'Makefile')
        self.report = self.root / 'reports with spaces/results.json'

    def suite(self, name, body):
        (self.cases / (name + '_test.sh')).write_text(body)

    def run_suite(self, *args, report=True):
        command = ['bash', str(self.shell / 'run_all.sh'), *args]
        if report:
            command += ['--json', str(self.report)]
        return subprocess.run(command, cwd=self.root, capture_output=True, text=True, timeout=30)

    def data(self):
        return json.loads(self.report.read_text())

    def test_default_runs_every_test_in_order_with_complete_timings(self):
        self.suite('beta', 'test_last() { true; }\n')
        self.suite('alpha', 'test_two() { true; }\ntest_one() { true; }\n')
        result = self.run_suite('--slowest', '2')
        self.assertEqual(result.returncode, 0, result.stderr)
        data = self.data()
        expected = ['alpha::test_one', 'alpha::test_two', 'beta::test_last']
        self.assertEqual(data['version'], 1)
        self.assertEqual(data['selected_tests'], expected)
        self.assertEqual([row['id'] for row in data['results']], expected)
        self.assertEqual(data['discovered_tests'], 3)
        self.assertEqual(data['counts'], {'total': 3, 'passed': 3, 'failed': 0})
        self.assertTrue(data['complete'])
        self.assertEqual(data['status'], 'passed')
        self.assertFalse(data['selection']['filtered'])
        for row in data['results']:
            self.assertEqual(row['exit_code'], 0)
            self.assertEqual(row['kind'], 'test')
            self.assertGreater(row['elapsed_seconds'], 0)
            self.assertLess(result.stdout.index('RUN   ' + row['id']),
                            result.stdout.index('PASS  ' + row['id']))
        self.assertGreater(data['discovery_seconds'], 0)
        self.assertGreaterEqual(data['elapsed_seconds'], data['discovery_seconds'] +
                                sum(row['elapsed_seconds'] for row in data['results']))
        ranking = result.stdout.split('Slowest entries', 1)[1].splitlines()[1:]
        self.assertEqual(len(ranking), 2)
        ordered = sorted(data['results'], key=lambda row: (-row['elapsed_seconds'], row['id']))
        self.assertEqual([line.split()[-1] for line in ranking], [row['id'] for row in ordered[:2]])

    def test_suite_filter_does_not_source_unselected_files(self):
        self.suite('chosen', 'test_ok() { true; }\n')
        self.suite('poison', 'touch "$REPO_ROOT/unexpected"\nfalse\n')
        result = self.run_suite('--suite', 'cho*')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse((self.root / 'unexpected').exists())
        self.assertIn('Selection: FILTERED', result.stdout)
        self.assertEqual(self.data()['selected_tests'], ['chosen::test_ok'])
        self.assertTrue(self.data()['selection']['filtered'])

    def test_test_filter_uses_full_identifier_and_intersects_suite_filter(self):
        self.suite('alpha', 'test_ok() { true; }\ntest_other() { false; }\n')
        self.suite('beta', 'test_ok() { false; }\n')
        result = self.run_suite('--suite', 'alpha', '--test', '*::test_ok')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.data()['selected_tests'], ['alpha::test_ok'])
        self.assertEqual(self.data()['selection']['test'], '*::test_ok')
        result = self.run_suite('--test', 'alpha::test_ok')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.data()['selected_tests'], ['alpha::test_ok'])

    def test_no_match_is_error_and_replaces_previous_success_report(self):
        self.suite('alpha', 'test_ok() { true; }\n')
        self.assertEqual(self.run_suite().returncode, 0)
        for args in (('--suite', 'missing'), ('--test', 'missing::*')):
            with self.subTest(args=args):
                result = self.run_suite(*args)
                self.assertEqual(result.returncode, 2)
                self.assertIn('matched no', result.stderr)
                self.assertEqual(self.data()['status'], 'error')
                self.assertFalse(self.data()['complete'])
                self.assertEqual(self.data()['counts']['total'], 0)
                self.assertNotIn('0 passed', result.stdout)

    def test_source_and_empty_suite_failures_cannot_be_hidden_by_test_filter(self):
        self.suite('good', 'test_ok() { true; }\n')
        self.suite('broken', 'false\ntest_ignored() { true; }\n')
        self.suite('empty', 'OTHER=1\n')
        result = self.run_suite('--test', 'good::*')
        self.assertEqual(result.returncode, 1)
        rows = {row['id']: row for row in self.data()['results']}
        self.assertEqual(rows['broken::<source>']['status'], 'failed')
        self.assertEqual(rows['empty::<no-tests>']['status'], 'failed')
        self.assertEqual(rows['good::test_ok']['status'], 'passed')
        self.assertEqual(self.data()['counts']['failed'], 2)
        self.assertIn('shell tests: 2 failed of 3', result.stdout)

    def test_early_successful_source_exit_is_still_a_suite_failure(self):
        self.suite('alpha', 'exit 0\ntest_unreachable() { true; }\n')
        result = self.run_suite()
        self.assertEqual(result.returncode, 1)
        self.assertEqual(self.data()['results'][0]['id'], 'alpha::<no-tests>')

    def test_nonfinal_failure_and_diagnostics_are_preserved_then_next_test_runs(self):
        self.suite('alpha', '''test_bad() {
  echo diagnostic-output
  echo diagnostic-error >&2
  false
  touch "$REPO_ROOT/incorrectly-continued"
}
test_next() { touch "$REPO_ROOT/next-ran"; }
''')
        result = self.run_suite()
        self.assertEqual(result.returncode, 1)
        self.assertFalse((self.root / 'incorrectly-continued').exists())
        self.assertTrue((self.root / 'next-ran').exists())
        self.assertIn('diagnostic-output', result.stdout)
        self.assertIn('diagnostic-error', result.stderr)
        data = self.data()
        self.assertEqual([row['exit_code'] for row in data['results']], [1, 0])
        self.assertEqual(data['status'], 'failed')
        self.assertTrue(data['complete'])

    def test_each_test_has_fresh_environment_and_cleaned_tmpdir(self):
        self.suite('alpha', '''test_first() {
  export LEAK_TEST_RUNNER=yes
  echo "$NESREV_TEST_TMPDIR" >> "$REPO_ROOT/directories"
  touch "$NESREV_TEST_TMPDIR/marker"
  trap 'echo first-cleanup >> "$REPO_ROOT/traps"' EXIT
}
test_second() {
  [[ -z "${LEAK_TEST_RUNNER:-}" ]]
  [[ ! -e "$NESREV_TEST_TMPDIR/marker" ]]
  echo "$NESREV_TEST_TMPDIR" >> "$REPO_ROOT/directories"
}
''')
        result = self.run_suite()
        self.assertEqual(result.returncode, 0, result.stderr)
        paths = (self.root / 'directories').read_text().splitlines()
        self.assertEqual(len(set(paths)), 2)
        self.assertTrue(all(not Path(path).exists() for path in paths))
        self.assertEqual((self.root / 'traps').read_text(), 'first-cleanup\n')

    def test_list_discovers_but_does_not_run_bodies(self):
        self.suite('alpha', 'test_body() { touch "$REPO_ROOT/body-ran"; }\n')
        result = self.run_suite('--list', report=False)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, 'alpha::test_body\n')
        self.assertFalse((self.root / 'body-ran').exists())
        self.assertIn('Selection: FULL', result.stderr)
        self.assertEqual(self.run_suite('--list').returncode, 2)

    def test_invalid_options_and_empty_tree_fail(self):
        for args in (('--suite', ''), ('--test', ''), ('--slowest', '-1'), ('--typo',)):
            with self.subTest(args=args):
                self.assertEqual(self.run_suite(*args, report=False).returncode, 2)
        result = self.run_suite()
        self.assertEqual(result.returncode, 2)
        self.assertFalse(self.data()['complete'])
        self.assertIn('no test files', result.stderr)

    def test_unwritable_report_prevents_execution(self):
        self.suite('alpha', 'test_body() { touch "$REPO_ROOT/body-ran"; }\n')
        self.report.parent.write_text('this is a file, not a directory')
        result = self.run_suite()
        self.assertEqual(result.returncode, 2)
        self.assertFalse((self.root / 'body-ran').exists())
        self.assertNotIn('Traceback', result.stderr)

    def test_signal_exit_is_reported_as_failure(self):
        self.suite('alpha', 'test_signal() { kill -TERM $$; }\n')
        result = self.run_suite()
        self.assertEqual(result.returncode, 1)
        self.assertEqual(self.data()['results'][0]['exit_code'], -15)
        self.assertEqual(self.data()['counts']['failed'], 1)

    def test_make_filters_are_quoted_and_full_target_refuses_them(self):
        self.suite('alpha', 'test_ok() { true; }\n')
        result = subprocess.run(['make', 'test-shell', 'TEST_SUITE=alpha',
                                 'TEST_CASE=alpha::*', 'TEST_JSON=' + str(self.report)],
                                cwd=self.root, capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.data()['selected_tests'], ['alpha::test_ok'])
        for variable in ('TEST_SUITE=alpha', 'TEST_CASE=alpha::*'):
            result = subprocess.run(['make', '-n', 'test', variable], cwd=self.root,
                                    capture_output=True, text=True, timeout=30)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('make test runs the full suite', result.stderr)
        payload = "literal'$(touch should-not-exist)`touch also-not-exist`"
        result = subprocess.run(['make', 'test-shell', 'TEST_CASE=' + payload], cwd=self.root,
                                capture_output=True, text=True, timeout=30)
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse((self.root / 'should-not-exist').exists())
        self.assertFalse((self.root / 'also-not-exist').exists())

    def test_outer_make_options_do_not_leak_into_fixture_invocations(self):
        (self.root / 'fixture.mk').write_text(
            "all:\n\ttest -z '$(TEST_SUITE)$(TEST_CASE)$(TEST_JSON)'\n")
        self.suite('alpha', 'test_make() { make -f fixture.mk; }\n')
        env = dict(os.environ, TEST_SUITE='bad', TEST_CASE='bad', TEST_JSON='bad',
                   MAKEFLAGS='-- TEST_SUITE=bad TEST_JSON=bad',
                   MAKEOVERRIDES='TEST_CASE=bad', MFLAGS='-n')
        result = subprocess.run(['bash', str(self.shell / 'run_all.sh')],
                                cwd=self.root, env=env, capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('shell tests: 1 passed', result.stdout)
        self.assertFalse((self.root / 'bad').exists())


if __name__ == '__main__':
    unittest.main()
