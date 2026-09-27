#!/usr/bin/env python3
"""Exercise the real spawned workers without private project inputs."""

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest


class IsolatedRunnerTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="nesrev-isolated-tests-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def launch(self, methods, module_setup=""):
        script = self.root / "cases.py"
        script.write_text(
            "import os, time, unittest, subprocess\nfrom pathlib import Path\nimport sys\n"
            f"sys.path.insert(0, {str(Path(__file__).resolve().parent)!r})\n"
            "from isolated_unittest import run\n"
            f"{module_setup}\n"
            f"ROOT = Path({str(self.root)!r})\n"
            "class Cases(unittest.TestCase):\n" + textwrap.indent(textwrap.dedent(methods), "    ") +
            "\nif __name__ == '__main__':\n    raise SystemExit(run(Cases))\n")
        return subprocess.run([sys.executable, str(script)], cwd=self.root,
                              capture_output=True, text=True, timeout=30)

    def test_all_cases_run_once_in_two_spawned_workers(self):
        methods = """
        def rendezvous(self, name, other):
            (ROOT / name).write_text(str(os.getpid()))
            deadline = time.monotonic() + 5
            while not (ROOT / other).exists() and time.monotonic() < deadline:
                time.sleep(0.01)
            self.assertTrue((ROOT / other).exists(), 'second worker never ran')
        def test_a(self):
            self.rendezvous('a', 'b')
        def test_b(self):
            self.rendezvous('b', 'a')
        """
        for name in ("c", "d", "e", "f"):
            methods += f"\n        def test_{name}(self):\n            with (ROOT / '{name}').open('x') as out:\n                out.write(str(os.getpid()))\n"
        result = self.launch(methods)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        pids = {(self.root / name).read_text() for name in "abcdef"}
        self.assertEqual(len(pids), 2)
        self.assertNotIn(str(os.getpid()), pids)
        self.assertIn("Isolated tests: 6 run, 0 failed", result.stderr)

    def test_assertion_failure_keeps_diagnostics_and_runs_other_cases(self):
        result = self.launch("""
        def test_a(self):
            print('failure stdout')
            print('failure stderr', file=sys.stderr)
            subprocess.run([sys.executable, '-c', "import os; os.write(1, b'child stdout'); os.write(2, b'child stderr')"], check=True)
            self.fail('deliberate failure')
        def test_b(self):
            (ROOT / 'survivor').write_text('ran')
        """)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        for text in ("failure stdout", "failure stderr", "child stdout", "child stderr", "deliberate failure",
                     "Isolated tests: 2 run, 1 failed"):
            self.assertIn(text, result.stderr)
        self.assertTrue((self.root / "survivor").exists())
        self.assertEqual(result.stdout, "")

    def test_fixture_errors_and_subtest_failures_refuse_success(self):
        for methods in (
            "def setUp(self):\n    raise RuntimeError('setup failed')\ndef test_a(self):\n    pass\n",
            "def tearDown(self):\n    raise RuntimeError('teardown failed')\ndef test_a(self):\n    pass\n",
            "def test_a(self):\n    with self.subTest(kind='broken'):\n        self.fail('subtest failed')\n",
            "@unittest.expectedFailure\ndef test_a(self):\n    pass\n",
        ):
            with self.subTest(methods=methods):
                result = self.launch(methods)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("Isolated tests: 1 run, 1 failed", result.stderr)

    def test_skip_and_expected_failure_remain_visible(self):
        result = self.launch("""
        @unittest.skip('fixture unavailable')
        def test_a(self):
            pass
        @unittest.expectedFailure
        def test_b(self):
            self.fail('expected failure')
        """)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("fixture unavailable", result.stderr)
        self.assertIn("expected failure", result.stderr)

    def test_worker_exit_is_a_failure(self):
        result = self.launch("""
        def test_a(self):
            os._exit(17)
        """)
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("BrokenProcessPool", result.stderr)

    def test_empty_case_is_a_failure(self):
        result = self.launch("pass\n")
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("no tests", result.stderr)

    def test_class_fixtures_cannot_silently_change_lifetime(self):
        result = self.launch("""
        @classmethod
        def setUpClass(cls):
            pass
        def test_a(self):
            pass
        """)
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("cannot use class fixtures", result.stderr)

    def test_module_fixtures_cannot_silently_change_lifetime(self):
        result = self.launch("def test_a(self):\n    pass\n",
                             "def setUpModule():\n    pass\n")
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("cannot use module fixtures", result.stderr)


if __name__ == "__main__":
    unittest.main()
