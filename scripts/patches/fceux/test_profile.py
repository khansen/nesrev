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
        self.root = Path(self.temp.name).resolve()
        self.install = self.root / "local install"
        self.release = self.install / "releases/one"
        (self.release / "bin").mkdir(parents=True)
        (self.install / "current").symlink_to(self.release)
        (self.install / "config").mkdir()
        self.binary = self.release / "bin/fceux"
        self.binary.write_text("#!/bin/sh\nprintf 'release one\\n'\n")
        self.binary.chmod(0o755)
        self.adapter = self.release / "bin/tmux-local-fceux"
        shutil.copy2(SOURCE / "tmux-local-fceux", self.adapter)
        (self.release / "SHA256SUMS").write_text("".join(
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
                self.assertEqual(values["LUA_PATH"], str(self.release / "share/luaScripts/?.lua") + ";;")

    def test_current_switch_keeps_checked_release(self):
        other = self.install / "releases/two"
        shutil.copytree(self.release, other)
        (other / "bin/fceux").write_text("#!/bin/sh\nprintf 'release two\\n'\n")
        current = self.install / "current"
        code = (
            "import json,os,subprocess;from pathlib import Path;"
            "current=Path(" + repr(str(current)) + ");current.unlink();"
            "current.symlink_to(" + repr(str(other)) + ");"
            "print(json.dumps({'paths':{k:os.environ[k] for k in " + repr(KEYS) + "},"
            "'ran':subprocess.check_output([os.environ['FCEUX_BIN']],text=True).strip()}))")
        for shell in self.shells():
            with self.subTest(shell=shell):
                result = self.activate(shell, code)
                self.assertEqual(result.returncode, 0, result.stderr)
                values = json.loads(result.stdout)
                self.assertEqual(values["ran"], "release one")
                self.assertEqual(values["paths"]["FCEUX_BIN"], str(self.binary))
                self.assertEqual(values["paths"]["AGENT_REVIEW_TMUX_BIN"], str(self.adapter))
                self.assertEqual(values["paths"]["LUA_PATH"], str(self.release / "share/luaScripts/?.lua") + ";;")
                rejected = self.activate(shell, "print('should not launch')")
                self.assertNotEqual(rejected.returncode, 0)
                self.assertEqual(rejected.stdout, "")
            current.unlink()
            current.symlink_to(self.release)

    def test_missing_config_blocks_dependent_command(self):
        (self.install / "config").rmdir()
        for shell in self.shells():
            with self.subTest(shell=shell):
                result = self.activate(shell, "print('should not launch')")
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")

    def test_checksum_manifest_requires_both_executables(self):
        manifest = self.release / "SHA256SUMS"
        original = manifest.read_text()
        for omitted in (self.binary, self.adapter):
            for present in (True, False):
                content = omitted.read_bytes()
                mode = omitted.stat().st_mode
                manifest.write_text(''.join(line for line in original.splitlines(keepends=True)
                                            if not line.endswith("  bin/" + omitted.name + "\n")))
                if not present:
                    omitted.unlink()
                for shell in self.shells():
                    with self.subTest(file=omitted.name, present=present, shell=shell):
                        result = self.activate(shell, "print('should not launch')")
                        self.assertNotEqual(result.returncode, 0)
                        self.assertEqual(result.stdout, "")
                omitted.write_bytes(content)
                omitted.chmod(mode)
        manifest.write_text(original)

    def test_damaged_installation_blocks_dependent_command(self):
        targets = (self.binary, self.adapter, self.release / "SHA256SUMS")
        for target in targets:
            original = target.read_bytes()
            mode = target.stat().st_mode
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
                target.chmod(mode)

    @unittest.skipUnless(LIVE_TMUX, "use --tmux to exercise a disposable server")
    def test_existing_tmux_server_and_panes_receive_environment(self):
        real = shutil.which("tmux")
        if not real:
            self.skipTest("tmux is not installed")
        socket = self.root / "server.sock"
        stub = self.root / "commands"
        stub.mkdir()
        (stub / "tmux").write_text("#!/bin/sh\nexec " + shlex.join([real, "-S", str(socket)]) + ' "$@"\n')
        (stub / "tmux").chmod(0o755)
        clean = dict(self.env, PATH=str(stub) + os.pathsep + self.env["PATH"])
        clean.pop("TMUX", None)
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
                (["respawn-pane", "-k", "-t", "candidate:0.0"], "respawn"),
                (["new-window", "-d", "-t", "candidate"], "window"),
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
