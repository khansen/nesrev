#!/usr/bin/env python3
"""Check the optional profile without an emulator; --tmux also uses a private server."""

import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
import unittest

SOURCE = Path(__file__).resolve().parent
LIVE_TMUX = "--tmux" in sys.argv
if LIVE_TMUX:
    sys.argv.remove("--tmux")
KEYS = ("FCEUX_BIN", "FCEUX_CONFIG_DIR", "LUA_PATH", "AGENT_REVIEW_TMUX_BIN")


class ProfileTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="nesrev-fceux-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.install = self.root / "local install"
        (self.install / "current/bin").mkdir(parents=True)
        (self.install / "config").mkdir()
        self.binary = self.install / "current/bin/fceux"
        self.binary.write_text("fixture, never executed\n")
        self.adapter = self.install / "current/bin/tmux-local-fceux"
        shutil.copy2(SOURCE / "tmux-local-fceux", self.adapter)
        (self.install / "current/SHA256SUMS").write_text("".join(
            hashlib.sha256(p.read_bytes()).hexdigest() + "  bin/" + p.name + "\n"
            for p in (self.binary, self.adapter)))
        self.env = {k: v for k, v in os.environ.items() if k not in KEYS}
        self.env["NESREV_FCEUX_ROOT"] = str(self.install)

    def shells(self):
        found = [p for name in ("bash", "zsh") if (p := shutil.which(name))]
        if not found:
            self.skipTest("bash or zsh required")
        return found

    def activate(self, shell, code):
        return subprocess.run(
            [shell, "-c", '. "$1" && "$2" -c "$3"', "check",
             str(SOURCE / "activate.sh"), sys.executable, code],
            env=self.env, capture_output=True, text=True, timeout=10)

    def test_activation_exports_selected_paths(self):
        code = "import json,os; print(json.dumps({k:os.environ[k] for k in " + repr(KEYS) + "}))"
        for shell in self.shells():
            with self.subTest(shell=shell):
                result = self.activate(shell, code)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stderr, "")
                values = json.loads(result.stdout)
                self.assertEqual(values["FCEUX_BIN"], str(self.binary))
                self.assertEqual(values["FCEUX_CONFIG_DIR"], str(self.install / "config"))
                self.assertEqual(values["AGENT_REVIEW_TMUX_BIN"], str(self.adapter))
                self.assertEqual(values["LUA_PATH"], str(self.install / "current/share/luaScripts/?.lua") + ";;")

    def test_damaged_installation_blocks_dependent_command(self):
        targets = (self.binary, self.adapter, self.install / "current/SHA256SUMS")
        for target in targets:
            original = target.read_bytes()
            for state in ("changed", "missing"):
                if state == "changed":
                    target.write_text("changed\n")
                else:
                    target.unlink()
                for shell in self.shells():
                    with self.subTest(file=target.name, state=state, shell=shell):
                        marker = self.root / "launched"
                        result = self.activate(shell, "from pathlib import Path; Path(" + repr(str(marker)) + ").touch()")
                        self.assertNotEqual(result.returncode, 0)
                        self.assertFalse(marker.exists())
                target.write_bytes(original)

    @unittest.skipUnless(LIVE_TMUX, "use --tmux to exercise a disposable server")
    def test_existing_tmux_server_and_split_receive_environment(self):
        real = shutil.which("tmux")
        if not real:
            self.skipTest("tmux is not installed")
        socket = self.root / "server.sock"
        stub = self.root / "commands"
        stub.mkdir()
        (stub / "tmux").write_text("#!/bin/sh\nexec " + shlex.join([real, "-S", str(socket)]) + ' "$@"\n')
        (stub / "tmux").chmod(0o755)
        clean = dict(self.env, PATH=str(stub) + os.pathsep + self.env["PATH"])
        chosen = {"FCEUX_BIN": "/fixture with spaces/fceux;",
                  "FCEUX_CONFIG_DIR": "/fixture with spaces/config;",
                  "LUA_PATH": "/fixture with spaces/?.lua;;"}
        selected = dict(clean, **chosen)

        def tmux(*args, env=clean):
            return subprocess.run([real, "-S", str(socket), *args], env=env,
                                  capture_output=True, text=True, timeout=10)

        def command(label):
            code = ("import json,os,time;from pathlib import Path;Path(" +
                    repr(str(self.root / (label + ".json"))) +
                    ").write_text(json.dumps({k:os.environ.get(k) for k in " +
                    repr(tuple(chosen)) + "}));time.sleep(30)")
            return shlex.join([sys.executable, "-c", code])

        def observed(label):
            path = self.root / (label + ".json")
            deadline = time.monotonic() + 5
            while time.monotonic() < deadline:
                if path.exists():
                    try:
                        return json.loads(path.read_text())
                    except json.JSONDecodeError:
                        pass
                time.sleep(0.02)
            self.fail("pane did not report its environment: " + label)

        try:
            started = tmux("-f", os.devnull, "new-session", "-d", "-s", "keeper", "sleep 30")
            self.assertEqual(started.returncode, 0, started.stderr)
            control = tmux("new-session", "-d", "-s", "control", command("control"), env=selected)
            self.assertEqual(control.returncode, 0, control.stderr)
            self.assertEqual(observed("control"), {key: None for key in chosen})
            for args, label in [
                (["new-session", "-d", "-s", "candidate"], "candidate"),
                (["split-window", "-d", "-h", "-t", "candidate"], "split"),
            ]:
                result = subprocess.run([str(self.adapter), *args, command(label)],
                                        env=selected, capture_output=True, text=True, timeout=10)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(observed(label), chosen)
            for key in chosen:
                missing = dict(selected)
                missing.pop(key)
                result = subprocess.run([str(self.adapter), "new-session", "-d", "-s", "missing"],
                                        env=missing, capture_output=True, text=True, timeout=10)
                self.assertNotEqual(result.returncode, 0)
                self.assertNotEqual(tmux("has-session", "-t", "missing").returncode, 0)
        finally:
            tmux("kill-server")


if __name__ == "__main__":
    unittest.main()
