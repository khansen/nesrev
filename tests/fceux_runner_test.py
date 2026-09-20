"""Exercise the supervisor with real child processes; no emulator or ROM required."""

import json
import os
from pathlib import Path
import signal
import shutil
import subprocess
import sys
import tempfile
import time
import unittest


ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / "scripts/run_fceux_trace.py"

FAKE_EMULATOR = r'''
import json, os, signal, subprocess, sys, time
from pathlib import Path
lua = Path(sys.argv[sys.argv.index('--loadlua') + 1])
mode = lua.read_text()
out = Path(os.environ['TRACE_OUT'])
directory = Path(os.environ['TRACE_DIR'])
(directory / 'arguments.json').write_text(json.dumps({
    'argv': sys.argv[1:], 'out': str(out), 'directory': str(directory),
    'cwd': os.getcwd(), 'max_frames': os.environ['TRACE_MAX_FRAMES'],
}))
signal.signal(signal.SIGTERM, signal.SIG_IGN)
if mode in ('hang-child', 'orphan'):
    child = subprocess.Popen([sys.executable, '-c',
        'import signal,time; signal.signal(signal.SIGTERM, signal.SIG_IGN); time.sleep(60)'])
    (directory / 'child.pid').write_text(str(child.pid))
(directory / 'emulator.pid').write_text(str(os.getpid()))
if mode.startswith('hang'):
    print('simulated Lua failure leaves GUI running', flush=True)
    time.sleep(60)
if mode == 'missing':
    sys.exit(0)
if mode.startswith('json:'):
    out.write_text(mode[5:])
elif mode == 'no-marker':
    out.write_text('PARTIAL\n')
elif mode == 'after-marker':
    out.write_text('COMPLETE\nFAIL\n')
else:
    out.write_text('frame\tevent\n1\tready\nCOMPLETE\n')
if mode == 'nonzero':
    sys.exit(7)
if mode == 'complete-hang':
    time.sleep(60)
if mode == 'complete-late-failure':
    time.sleep(0.04)
    sys.exit(7)
if mode == 'complete-then-invalid':
    time.sleep(0.2)
    with out.open('a') as stream: stream.write('FAIL\n')
    time.sleep(60)
'''


class RunnerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fceux-supervisor-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.addCleanup(self.cleanup_emulators)
        self.inputs = self.root / "inputs with spaces"
        self.inputs.mkdir()
        self.rom = self.inputs / "fixture.nes"
        self.rom.write_bytes(b"synthetic fixture, not a game ROM")
        self.lua = self.inputs / "capture.lua"
        self.lua.write_text("complete")
        self.emulator = self.inputs / "fake fceux"
        self.emulator.write_text(f"#!{sys.executable}\n" + FAKE_EMULATOR)
        self.emulator.chmod(0o755)
        self.output = self.root / "captures with spaces"

    def cleanup_emulators(self):
        for path in self.root.rglob("emulator.pid"):
            try:
                os.killpg(int(path.read_text()), signal.SIGKILL)
            except ProcessLookupError:
                pass

    def command(self, checks=None, extra=()):
        return [sys.executable, str(RUNNER), "--rom", str(self.rom.relative_to(self.root)),
                "--lua", str(self.lua.relative_to(self.root)),
                "--fceux", str(self.emulator.relative_to(self.root)),
                "--output-dir", str(self.output.relative_to(self.root)),
                "--timeout", "3", "--shutdown-grace", "0.1",
                *(checks or ["--completion-line", "COMPLETE"]), *extra]

    def run_capture(self, mode="complete", checks=None, extra=()):
        self.lua.write_text(mode)
        before = set(self.output.glob("capture-*"))
        completed = subprocess.run(self.command(checks, extra), cwd=self.root,
                                   text=True, capture_output=True, timeout=8)
        fresh = set(self.output.glob("capture-*")) - before
        self.assertEqual(len(fresh), 1, completed.stdout + completed.stderr)
        self.run_dir = fresh.pop()
        self.result = json.loads((self.run_dir / "result.json").read_text())
        self.assertEqual(self.result["exit_code"], completed.returncode)
        return completed

    def test_relative_paths_are_absolute_and_completion_is_recorded(self):
        movie = self.inputs / "input movie.fm2"
        movie.write_text("synthetic movie")
        result = self.run_capture(extra=["--movie", str(movie.relative_to(self.root)),
                                         "--max-frames", "12", "--input2", "zapper", "--sound", "1"])
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("Capture complete", result.stdout)
        observed = json.loads((self.run_dir / "arguments.json").read_text())
        self.assertEqual(observed["out"], str(self.run_dir / "trace.log"))
        self.assertEqual(observed["directory"], str(self.run_dir))
        self.assertEqual(observed["cwd"], str(self.run_dir))
        self.assertEqual(observed["max_frames"], "12")
        for path in (self.rom, self.lua, movie):
            self.assertIn(str(path), observed["argv"])
        self.assertEqual(self.result["status"], "complete")
        self.assertEqual(len(self.result["rom"]["sha256"]), 64)
        self.assertEqual(self.result["emulator_exit"], 0)

    def test_stale_capture_cannot_supply_completion_or_be_overwritten(self):
        self.assertEqual(self.run_capture().returncode, 0)
        previous = self.run_dir
        before = (previous / "trace.log").read_bytes()
        result = self.run_capture("missing")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("missing fresh trace", result.stderr)
        self.assertNotEqual(previous, self.run_dir)
        self.assertEqual((previous / "trace.log").read_bytes(), before)
        self.assertNotIn("Capture complete", result.stdout)

    def test_zero_exit_without_terminal_marker_is_failure(self):
        for mode in ("no-marker", "after-marker"):
            with self.subTest(mode=mode):
                result = self.run_capture(mode)
                self.assertEqual(result.returncode, 1)
                self.assertIn("must end with the exact line", result.stderr)

    def test_marker_does_not_override_emulator_failure(self):
        for mode in ("nonzero", "complete-late-failure"):
            with self.subTest(mode=mode):
                result = self.run_capture(mode)
                self.assertEqual(result.returncode, 1)
                self.assertIn("status 7", result.stderr)
                self.assertEqual(self.result["emulator_exit"], 7)

    def test_completed_lua_does_not_wait_for_gui_to_exit(self):
        result = self.run_capture("complete-hang")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(self.result["stopped_after_completion"])
        self.assertEqual(self.result["emulator_exit"], -signal.SIGKILL)
        self.assert_capture_processes_dead()

    def test_completion_is_rechecked_after_shutdown(self):
        result = self.run_capture("complete-then-invalid", extra=["--shutdown-grace", "0.4"])
        self.assertNotEqual(result.returncode, 0)
        self.assertTrue(self.result["stopped_after_completion"])
        self.assertNotIn("Capture complete", result.stdout)
        self.assert_capture_processes_dead()

    def json_capture(self, rows):
        return self.run_capture("json:" + "\n".join(json.dumps(row) for row in rows),
                                ["--require-milestone", "entered", "--require-milestone", "resolved"])

    def rows(self):
        return [{"event": "start"}, {"event": "milestone", "name": "entered"},
                {"event": "milestone", "name": "resolved"},
                {"event": "done", "reason": "max_frames"}]

    def test_json_completion_and_all_milestones(self):
        result = self.json_capture(self.rows())
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_each_missing_milestone_refuses_completion(self):
        for name in ("entered", "resolved"):
            with self.subTest(name=name):
                result = self.json_capture([row for row in self.rows() if row.get("name") != name])
                self.assertEqual(result.returncode, 1)
                self.assertIn("missing required milestones: " + name, result.stderr)

    def test_early_exit_missing_done_and_post_completion_records_fail(self):
        cases = [self.rows()[:-1], self.rows()[:-1] + [{"event": "done", "reason": "exit"}],
                 self.rows() + [{"event": "watch"}], self.rows()[1:],
                 self.rows()[:2] + [{"event": "fail"}] + self.rows()[2:]]
        for rows in cases:
            with self.subTest(rows=rows):
                result = self.json_capture(rows)
                self.assertEqual(result.returncode, 1)
                self.assertNotIn("Capture complete", result.stdout)

    def test_malformed_json_fails(self):
        result = self.run_capture('json:{"event":"start"}\n{', ["--require-milestone", "entered"])
        self.assertEqual(result.returncode, 1)
        self.assertIn("invalid JSON", result.stderr)

    def assert_dead(self, pid):
        # A killed grandchild may briefly remain a zombie until init reaps it.
        result = subprocess.run(["ps", "-o", "stat=", "-p", str(pid)],
                                text=True, capture_output=True, check=False)
        self.assertIn(result.returncode, (0, 1), result.stderr)
        self.assertEqual(result.stderr, "")
        state = result.stdout.strip()
        self.assertTrue(not state or state.startswith("Z"), f"process {pid} still running: {state}")

    def assert_capture_processes_dead(self):
        for path in self.run_dir.glob("*.pid"):
            self.assert_dead(int(path.read_text()))

    def test_timeout_kills_own_group_without_touching_unrelated_process(self):
        unrelated = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(60)"])
        try:
            result = self.run_capture("hang-child", extra=["--timeout", "0.4"])
            self.assertEqual(result.returncode, 124, result.stderr)
            self.assertIn("timed out", result.stderr)
            self.assertIn("simulated Lua failure", (self.run_dir / "emulator.log").read_text())
            self.assertEqual(self.result["emulator_exit"], -signal.SIGKILL)
            self.assert_capture_processes_dead()
            self.assertIsNone(unrelated.poll())
        finally:
            unrelated.terminate()
            unrelated.wait(timeout=3)

    def test_normal_exit_also_cleans_descendants(self):
        result = self.run_capture("orphan")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assert_capture_processes_dead()

    def test_interrupts_cleanup_and_record_failure(self):
        for sig in (signal.SIGINT, signal.SIGTERM):
            with self.subTest(signal=sig):
                self.lua.write_text("hang-child")
                proc = subprocess.Popen(self.command(), cwd=self.root, text=True,
                                        stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                try:
                    first = proc.stdout.readline().strip()
                    self.assertTrue(first.startswith("Capture directory: "), first)
                    self.run_dir = Path(first.removeprefix("Capture directory: "))
                    deadline = time.monotonic() + 3
                    while not (self.run_dir / "emulator.pid").exists():
                        self.assertLess(time.monotonic(), deadline, "fake emulator did not start")
                        time.sleep(0.01)
                    proc.send_signal(sig)
                    stdout, stderr = proc.communicate(timeout=5)
                    self.assertEqual(proc.returncode, 128 + sig, stdout + stderr)
                    self.assertIn("interrupted", stderr)
                    self.assertNotIn("Capture complete", stdout)
                    self.result = json.loads((self.run_dir / "result.json").read_text())
                    self.assertEqual(self.result["status"], "failed")
                    self.assert_capture_processes_dead()
                finally:
                    if proc.poll() is None:
                        proc.kill()
                    proc.communicate(timeout=3)

    def test_invalid_limits_and_missing_inputs_do_not_launch(self):
        for extra in (["--timeout", "nan"], ["--timeout", "0"], ["--max-frames", "-1"],
                      ["--shutdown-grace", "inf"], ["--rom", "absent.nes"],
                      ["--fceux", "absent-fceux"], ["--completion-line", ""]):
            with self.subTest(extra=extra):
                result = subprocess.run(self.command(extra=extra), cwd=self.root,
                                        text=True, capture_output=True, timeout=3)
                self.assertEqual(result.returncode, 2)
                self.assertFalse(self.output.exists())

    def test_copied_project_wrapper_uses_supervisor_and_scenario_checks(self):
        project = self.root / "projects/demo"
        (project / "scripts").mkdir(parents=True)
        (project / "tools/trace").mkdir(parents=True)
        (project / "reference").mkdir()
        (self.root / "scripts").mkdir()
        shutil.copy2(RUNNER, self.root / "scripts/run_fceux_trace.py")
        wrapper = project / "scripts/run_trace_fceux.sh"
        shutil.copy2(ROOT / "agent_playbook/templates/trace/run_trace_fceux.sh", wrapper)
        shutil.copy2(self.rom, project / "reference/demo.nes")
        rows = self.rows()
        rows[1]["name"] = "scenario_started"
        rows[2]["name"] = "result_resolved"
        lua = project / "tools/trace/fceux_frame_poll_trace.lua"
        environment = dict(os.environ, PROJECT_SLUG="demo", FCEUX_BIN=str(self.emulator))
        for include_result in (True, False):
            with self.subTest(include_result=include_result):
                selected = rows if include_result else [row for row in rows if row.get("name") != "result_resolved"]
                lua.write_text("json:" + "\n".join(json.dumps(row) for row in selected))
                result = subprocess.run(["bash", str(wrapper)], cwd=self.root, env=environment,
                                        text=True, capture_output=True, timeout=8)
                self.assertEqual(result.returncode, 0 if include_result else 1, result.stderr)
                if not include_result:
                    self.assertIn("missing required milestones: result_resolved", result.stderr)


if __name__ == "__main__":
    unittest.main()
