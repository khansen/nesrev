#!/usr/bin/env python3
"""Real subprocess coverage for scoped inspection, trace dispatch, and smoke input."""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))
import agent_review as review
import agent_review_smoke as smoke


class OperationsTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve() / "checkout with ' spaces"
        self.root.mkdir()
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        self.project = self.root / "projects/demo"
        (self.project / "tools/trace").mkdir(parents=True)
        (self.project / "project.conf").write_text('PROJECT="demo"\n')
        self.source = self.project / "source file.asm"
        self.source.write_text("Actor:\n    JSR Actor\nOtherActor:\n    JMP @@done\n@@done:\n")
        self.driver = self.project / "tools/trace/run_probe.py"
        self.driver.write_text(
            "import json, os, sys\nfrom pathlib import Path\n"
            "Path('invocations.jsonl').open('a').write(json.dumps(sys.argv[1:])+'\\n')\n"
            "print(json.dumps({'cwd':os.getcwd(),'args':sys.argv[1:]}))\n"
            "sys.exit(7 if '--fail' in sys.argv else 0)\n"
        )
        self.command = review.script_argv(self.root)
        self.spec = {"inspection": {"path": "projects/demo/source file.asm", "symbols": ["Actor", "@@done"]},
                     "trace": {"driver": "run_probe.py", "arguments": ["--scenario", "fixture with spaces"]}}

    def run_command(self, *args, expected=0):
        result = subprocess.run([*self.command, *args], cwd=self.temp.name, text=True, capture_output=True)
        self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
        return result

    def test_search_reads_whole_tokens_from_another_cwd_without_writes(self):
        before = {p.relative_to(self.root): p.read_bytes() for p in self.root.rglob('*') if p.is_file()}
        result = self.run_command("find-project-symbols", "demo", "projects/demo/source file.asm", "Actor", "@@done")
        matches = json.loads(result.stdout)["matches"]
        self.assertEqual([m["line"] for m in matches], [1, 2, 4, 5])
        self.assertEqual(before, {p.relative_to(self.root): p.read_bytes() for p in self.root.rglob('*') if p.is_file()})
        self.assertEqual(json.loads(self.run_command("find-project-symbols", "demo", "projects/demo/source file.asm", "Absent").stdout)["matches"], [])

    def test_search_refuses_other_projects_paths_symlinks_and_non_symbols(self):
        outside = self.root / "outside.asm"
        outside.write_text("Actor:\n")
        (self.project / "link.asm").symlink_to(outside)
        (self.project / "binary.asm").write_bytes(b'\xff')
        for path in (str(self.source), "projects/other/file.asm", "projects/demo/../demo/source file.asm",
                     "projects/demo/link.asm", "projects/demo/binary.asm", "projects/demo", "projects/demo/missing.asm"):
            with self.subTest(path=path):
                self.run_command("find-project-symbols", "demo", path, "Actor", expected=2)
        for symbol in (".*", "Actor; touch injected", "Actor\nOther", "--repo", "--pre=touch"):
            with self.subTest(symbol=symbol):
                self.run_command("find-project-symbols", "demo", "projects/demo/source file.asm", symbol, expected=2)
        self.assertFalse((self.root / "injected").exists())

    def test_trace_preserves_arguments_runs_from_root_repeats_and_propagates_failure(self):
        arguments = ["--scenario", "value with spaces", "$(touch injected)", "--repo", "/not-an-override"]
        for _ in range(2):
            result = self.run_command("trace-project", "demo", "run_probe.py", "--", *arguments)
            self.assertEqual(json.loads(result.stdout), {"cwd": str(self.root), "args": arguments})
        invocations = (self.root / "invocations.jsonl").read_text().splitlines()
        self.assertEqual([json.loads(line) for line in invocations], [arguments, arguments])
        self.assertFalse((self.root / "injected").exists())
        self.run_command("trace-project", "demo", "run_probe.py", "--", "--fail", expected=7)

    def test_trace_refuses_non_drivers_and_symlinked_files_or_directories_before_execution(self):
        outside = self.root / "run_outside.py"
        outside.write_bytes(self.driver.read_bytes())
        (self.driver.parent / "run_link.py").symlink_to(outside)
        for driver in (str(self.driver), "../run_probe.py", "run_link.py", "run_missing.py", "-c", "probe.py"):
            with self.subTest(driver=driver):
                self.run_command("trace-project", "demo", driver, "--", expected=2)
        # A directory symlink must not turn an approved project into a different one.
        other = self.root / "projects/alias"
        other.symlink_to(self.project, target_is_directory=True)
        self.run_command("trace-project", "alias", "run_link.py", "--", expected=2)
        self.assertFalse((self.root / "invocations.jsonl").exists())

    def test_smoke_spec_validates_real_inputs_and_generates_repeated_standalone_commands(self):
        path = self.root / "smoke.json"
        path.write_text(json.dumps(self.spec))
        self.assertEqual(smoke.load_spec(self.root, "demo", path), self.spec)
        for role, operation in (("reviewer", "find-project-symbols"), ("implementer", "trace-project")):
            prompt = smoke.prompt(self.root, "demo", role, self.spec)
            self.assertEqual(prompt.count(f" {operation} demo "), 2)
            self.assertIn("checkout-status", prompt)
            self.assertIn("Keep the launcher's permission mode unchanged", prompt)
            self.assertIn("No semantic pass starts", prompt)
            self.assertIn("does not certify absence of human intervention", prompt)
        for bad in ({}, [], {**self.spec, "command": "sh"},
                    {**self.spec, "inspection": {"path": "projects/demo/source file.asm", "symbols": ["Absent"]}},
                    {**self.spec, "trace": {"driver": "run_probe.py", "arguments": ["--help"]}},
                    {**self.spec, "trace": {"driver": "run_probe.py", "arguments": "--scenario bad"}}):
            path.write_text(json.dumps(bad))
            with self.subTest(bad=bad), self.assertRaises(review.UserError):
                smoke.load_spec(self.root, "demo", path)


if __name__ == "__main__":
    unittest.main()
