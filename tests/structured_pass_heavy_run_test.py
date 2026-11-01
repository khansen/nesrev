"""Small real-process controls; no project checkouts, captures or model calls."""
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest


RUNNER = Path(os.environ.get("HEAVY_RUN_TEST_RUNNER", Path(__file__).resolve().parents[1]/"scripts/structured_pass_heavy_run.py")).resolve()
ENV = {k: v for k, v in os.environ.items() if not k.startswith("NESREV_HEAVY_RUN_")}
ENV["PYTHONDONTWRITEBYTECODE"] = "1"


def until(predicate):
    deadline = time.monotonic() + 12
    while time.monotonic() < deadline:
        value = predicate()
        if value:
            return value
        time.sleep(0.02)
    raise AssertionError("process control did not reach its expected state")


class HeavyRunTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="heavy-run-test-")
        self.root = Path(self.temporary.name).resolve()
        self.lock = self.root/"shared/heavy.lock"
        self.records = self.lock.with_name(self.lock.name + ".runs")
        self.children = []

    def tearDown(self):
        # Test failure must not leave a writer behind. First terminate CLI owners,
        # allowing their supervisors to stop the command groups.
        for child in self.children:
            if child.poll() is None:
                child.terminate()
        for child in self.children:
            try:
                child.communicate(timeout=8)
            except subprocess.TimeoutExpired:
                child.kill()
                child.communicate(timeout=4)
        for value in self.receipts():
            pgid = value.get("command_pgid")
            if pgid:
                try:
                    os.killpg(pgid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
        self.temporary.cleanup()

    def argv(self, code, *, runner=RUNNER, estimate=1):
        return [sys.executable, "-B", str(runner), "--lock", str(self.lock),
                "--agent", "fixture", "--session", self.id(), "--estimate-mib", str(estimate),
                "--reserve-mib", "0", "--volume", str(self.root), "--",
                sys.executable, "-B", "-c", code]

    def start(self, code, **kwargs):
        child = subprocess.Popen(self.argv(code, **kwargs), cwd=self.root, env=ENV,
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        self.children.append(child)
        return child

    def run_code(self, code, **kwargs):
        return subprocess.run(self.argv(code, **kwargs), cwd=self.root, env=ENV,
                              capture_output=True, text=True, timeout=15)

    def receipts(self):
        return [json.loads(p.read_text()) for p in sorted(self.records.glob("*.json"))]

    def running(self):
        return next((v for v in self.receipts() if v["status"] == "running"
                     and v.get("command_pgid")), None)

    def test_exit_status_and_space_measurements(self):
        result = self.run_code("import os;print(os.environ['NESREV_HEAVY_RUN_ID']);raise SystemExit(7)")
        self.assertEqual(result.returncode, 7, result.stderr)
        value, = self.receipts()
        self.assertEqual(value["status"], "finished")
        self.assertEqual(value["command_exit"], 7)
        self.assertEqual(result.stdout.strip(), value["run_id"])
        self.assertGreater(value["free_before"][0]["free_bytes"], 0)
        self.assertGreater(value["free_after"][0]["free_bytes"], 0)
        self.assertEqual(value["free_before"][0]["device"], value["free_after"][0]["device"])
        self.assertEqual(value["agent"], "fixture")
        self.assertTrue(value["started_at"] and value["finished_at"])

    def test_two_copies_contend_before_command_runs(self):
        owner = self.start("import time;from pathlib import Path;Path('started').touch();time.sleep(10)")
        until(lambda: (self.root/"started").exists())
        probe = subprocess.run([sys.executable, "-c", """
import fcntl,sys
with open(sys.argv[1],'a+b') as stream:
    try:fcntl.flock(stream,fcntl.LOCK_EX|fcntl.LOCK_NB)
    except BlockingIOError:raise SystemExit(75)
""", str(self.lock)], env=ENV)
        self.assertEqual(probe.returncode, 75, "the OS lock itself must exclude another process")
        copied = self.root/"copy/heavy_run.py"
        copied.parent.mkdir()
        shutil.copyfile(RUNNER, copied)
        result = self.run_code("from pathlib import Path;Path('contender-ran').touch()", runner=copied)
        self.assertEqual(result.returncode, 75, result.stderr)
        self.assertIn("HEAVY_RUN_IN_PROGRESS", result.stderr)
        self.assertFalse((self.root/"contender-ran").exists())
        owner.terminate()
        owner.communicate(timeout=8)
        self.assertEqual(self.run_code("pass", runner=copied).returncode, 0)

    def test_killed_cli_holds_lock_through_descendant_cleanup(self):
        grandchild = """
import signal,time
from pathlib import Path
def stop(*args):
    Path('grandchild-stopping').touch()
    time.sleep(.6)
    raise SystemExit(0)
signal.signal(signal.SIGTERM,stop)
Path('grandchild-ready').touch()
time.sleep(20)
"""
        command = """
import signal,subprocess,sys,time
from pathlib import Path
child=subprocess.Popen([sys.executable,'-c',%r])
def stop(*args):
    Path('parent-stopping').touch()
    child.wait(timeout=3)
    Path('cleanup-finished').touch()
    raise SystemExit(0)
signal.signal(signal.SIGTERM,stop)
Path('parent-ready').touch()
time.sleep(20)
""" % grandchild
        owner = self.start(command)
        until(lambda: (self.root/"grandchild-ready").exists() and (self.root/"parent-ready").exists())
        value = until(self.running)
        owner.kill()
        until(lambda: (self.root/"parent-stopping").exists())
        refused = self.run_code("from pathlib import Path;Path('overlap').touch()")
        self.assertIn("HEAVY_RUN_IN_PROGRESS", refused.stderr)
        self.assertFalse((self.root/"overlap").exists())
        owner.communicate(timeout=8)
        until(lambda: (self.root/"cleanup-finished").exists())
        interrupted = next(v for v in self.receipts() if v["run_id"] == value["run_id"])
        self.assertEqual(interrupted["status"], "interrupted")
        self.assertEqual(interrupted["error"], "OWNER_INTERRUPTED")
        self.assertTrue((self.root/"grandchild-stopping").exists())
        self.assertIsNotNone(interrupted["free_after"])
        with self.assertRaises(ProcessLookupError):
            os.killpg(value["command_pgid"], 0)
        self.assertEqual(self.run_code("pass").returncode, 0)

    def test_killed_supervisor_keeps_child_lock_and_recovers_missing_end(self):
        owner = self.start("import time;from pathlib import Path;Path('started').touch();\n"
                           "while not Path('release').exists():time.sleep(.025)")
        until(lambda: (self.root/"started").exists())
        value = until(self.running)
        os.kill(value["supervisor_pid"], signal.SIGKILL)
        until(lambda: owner.poll() is not None)
        refused = self.run_code("from pathlib import Path;Path('overlap').touch()")
        self.assertIn("HEAVY_RUN_IN_PROGRESS", refused.stderr)
        self.assertFalse((self.root/"overlap").exists())
        (self.root/"release").touch()
        owner.communicate(timeout=8)
        self.assertEqual(self.run_code("pass").returncode, 0)
        recovered = next(v for v in self.receipts() if v["run_id"] == value["run_id"])
        self.assertEqual(recovered["error"], "RUNNER_INTERRUPTED")
        self.assertIsNone(recovered["free_after"])
        self.assertIsNone(recovered["finished_at"])
        self.assertIn("recovered_at", recovered)

    def test_death_before_process_registration_never_starts_command(self):
        copied = self.root/"pause_before_registration.py"
        source = RUNNER.read_text()
        old = '                value["command_pgid"] = process.pid'
        self.assertEqual(source.count(old), 1)
        copied.write_text(source.replace(old,
            "                Path('registration-paused').touch()\n"
            "                time.sleep(10)\n" + old))
        owner = self.start("from pathlib import Path;Path('unregistered-work').touch()", runner=copied)
        until(lambda: (self.root/"registration-paused").exists())
        value, = self.receipts()
        os.kill(value["supervisor_pid"], signal.SIGKILL)
        owner.communicate(timeout=8)
        self.assertFalse((self.root/"unregistered-work").exists())
        self.assertEqual(self.run_code("pass").returncode, 0)
        recovered = next(v for v in self.receipts() if v["run_id"] == value["run_id"])
        self.assertEqual(recovered["status"], "interrupted")
        self.assertIsNone(recovered["free_after"])

    def test_nested_run_uses_same_receipt_and_requires_inherited_descriptor(self):
        nested = self.argv("import os;print(os.environ['NESREV_HEAVY_RUN_ID'])")
        code = """
import os,subprocess
fd=int(os.environ['NESREV_HEAVY_RUN_FD'])
result=subprocess.run(%r,pass_fds=(fd,))
raise SystemExit(result.returncode)
""" % nested
        good = self.run_code(code)
        self.assertEqual(good.returncode, 0, good.stderr)
        self.assertEqual(len(self.receipts()), 1)
        self.assertEqual(good.stdout.strip(), self.receipts()[0]["run_id"])
        broken = self.run_code("import subprocess;raise SystemExit(subprocess.run(%r).returncode)" % nested)
        self.assertEqual(broken.returncode, 75, broken.stderr)
        self.assertIn("HEAVY_RUN_CONTEXT_LOST", broken.stderr)
        for option, replacement, error in [
                ("--estimate-mib", "2", "HEAVY_RUN_NESTED_BUDGET"),
                ("--lock", str(self.root/"different.lock"), "HEAVY_RUN_LOCK_MISMATCH")]:
            changed = list(nested)
            changed[changed.index(option)+1] = replacement
            refused = self.run_code("import os,subprocess;raise SystemExit(subprocess.run(%r,"
                                    "pass_fds=(int(os.environ['NESREV_HEAVY_RUN_FD']),)).returncode)" % changed)
            self.assertEqual(refused.returncode, 75, refused.stderr)
            self.assertIn(error, refused.stderr)

    def test_insufficient_space_refuses_before_command(self):
        result = self.run_code("from pathlib import Path;Path('ran').touch()", estimate=10**12)
        self.assertEqual(result.returncode, 75, result.stderr)
        self.assertIn("INSUFFICIENT_DISK_SPACE", result.stderr)
        self.assertFalse((self.root/"ran").exists())
        value, = self.receipts()
        self.assertEqual(value["status"], "refused")
        self.assertIsNone(value["free_after"])

    def test_stale_receipt_with_live_group_fails_closed(self):
        child = subprocess.Popen([sys.executable, "-c", "import time;time.sleep(10)"], start_new_session=True)
        self.children.append(child)
        self.records.mkdir(parents=True)
        (self.records/"old.json").write_text(json.dumps({"status":"running", "command_pgid":child.pid}))
        result = self.run_code("from pathlib import Path;Path('ran').touch()")
        self.assertEqual(result.returncode, 75, result.stderr)
        self.assertIn("HEAVY_ORPHAN_REQUIRES_RECOVERY", result.stderr)
        self.assertFalse((self.root/"ran").exists())
        self.assertIsNone(child.poll())  # Recovery never kills an unverified old PID.

    def test_absolute_shared_lock_is_required(self):
        command = self.argv("pass")
        command[command.index("--lock")+1] = "per-copy.lock"
        result = subprocess.run(command, cwd=self.root, env=ENV, capture_output=True, text=True)
        self.assertEqual(result.returncode, 75)
        self.assertIn("HEAVY_RUN_ABSOLUTE_LOCK_REQUIRED", result.stderr)


if __name__ == "__main__":
    unittest.main(verbosity=2)
