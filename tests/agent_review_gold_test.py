#!/usr/bin/env python3
"""Final-review protocol against a real Git checkout and synthetic gates."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

REPO = Path(__file__).resolve().parents[1]
SCRIPT = REPO / "scripts/agent_review.py"


class GoldReviewTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.git("init", "-q")
        self.git("config", "user.name", "Test")
        self.git("config", "user.email", "test@example.invalid")
        self.git("config", "commit.gpgsign", "false")
        self.source = self.root / "projects/demo/asm/demo.asm"
        self.source.parent.mkdir(parents=True)
        self.source.write_text("Start:\n  RTS\n")
        self.commit()
        self.source.write_text("RunGame:\n  RTS\n")
        self.commit()
        binary = self.root / "bin"
        binary.mkdir()
        make = binary / "make"
        make.write_text(f"#!{sys.executable}\n" + f"import sys\nsys.dont_write_bytecode = True\nsys.path.insert(0, {str(REPO / 'tests')!r})\n" + '''
import json, os, subprocess
from pathlib import Path
from review_packet_fixture import packet
keys = ("ALLOW_UNRESOLVED_LXXXX", "MAKEFLAGS", "MFLAGS", "MAKEOVERRIDES")
with open(".agents/make-calls.jsonl", "a") as output:
    output.write(json.dumps({"argv": sys.argv[1:], "env": {k: os.getenv(k) for k in keys}}) + "\\n")
mode_file = Path(".agents/gate-mode")
mode = mode_file.read_text() if mode_file.exists() else "ok"
if sys.argv[1] == "project-ci":
    print("Synthetic CI output: " + mode)
    if mode == "fail": sys.exit(7)
    if mode == "dirty": Path("projects/demo/asm/demo.asm").write_text("changed during CI")
    if mode == "head":
        subprocess.run(["git", "commit", "-q", "--allow-empty", "-m", "Concurrent change"], check=True)
    sys.exit(0)
values = dict(arg.split("=", 1) for arg in sys.argv[2:])
relaxed = values.get("ALLOW_UNRESOLVED_LXXXX") == "1"
failed = mode == "lxxxx" and not relaxed
Path(values["OUT"]).write_text(packet(values["HEAD"],
    statuses={"project-verify": 2 if failed else 0},
    verify_output="FAIL: 4 distinct LXXXX/LXXXXX labels (4 refs)" if failed else "Verified",
    verify_command=("ALLOW_UNRESOLVED_LXXXX=1 " if relaxed else "") + "make project-verify PROJECT=demo"))
''')
        make.chmod(0o755)
        self.env = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"])
        self.run_path = self.root / ".agents/runs/demo-pass-1"

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root, text=True).strip()

    def commit(self):
        self.git("add", "projects")
        self.git("commit", "-qm", "Project change")

    def command(self, *args, expected=0, env=None):
        result = subprocess.run([sys.executable, str(SCRIPT), *args], cwd=self.root,
                                env=env or self.env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        self.assertEqual(result.returncode, expected, result.stdout)
        return result.stdout

    def start(self, **kwargs):
        return self.command("start-pass", "--project", "demo", "--pass-id", "1", "--gold", **kwargs)

    def state(self):
        return json.loads((self.root / ".agents/current.json").read_text())

    def mode(self, value):
        (self.root / ".agents").mkdir(exist_ok=True)
        (self.root / ".agents/gate-mode").write_text(value)

    def calls(self):
        return [json.loads(line) for line in (self.root / ".agents/make-calls.jsonl").read_text().splitlines()]

    def approve(self, text=None, round_number=1, **kwargs):
        path = self.run_path / f"review-{round_number:02d}.md"
        path.write_text(text or "Verdict: APPROVED\nGold assessment: APPROVED\n\n"
                        "## Gold-Standard Assessment\nSynthetic checklist evidence.\n\n## Learning Candidates\n_None._\n")
        return self.command("approve", "--review", str(path), **kwargs)

    def test_gold_rejects_explicit_relaxation_before_state_creation(self):
        result = self.command("start-pass", "--project", "demo", "--pass-id", "1", "--gold",
                              "--allow-unresolved-lxxxx", expected=2)
        self.assertIn("--gold cannot allow", result)
        self.assertFalse((self.root / ".agents/current.json").exists())

    def test_gold_does_not_fallback_to_relaxed_packet(self):
        self.mode("lxxxx")
        self.start(expected=2)
        self.assertEqual(len(self.calls()), 1)
        self.assertEqual(self.state()["status"], "IMPLEMENTING")
        self.assertFalse(self.state()["allow_unresolved_lxxxx"])
        output = self.command("ready", "--note", str(self.run_path / "implementation.md"),
                              "--packet", str(self.run_path / "packet-round-01.md"), expected=2)
        self.assertIn("gold review requires --generate-packet", output)

    def test_gold_rejects_ordinary_approval_or_missing_assessment(self):
        self.start()
        for text, diagnostic in (("Verdict: APPROVED\n", "Gold assessment: APPROVED"),
                                 ("Verdict: APPROVED\nGold assessment: APPROVED\n", "## Gold-Standard Assessment")):
            with self.subTest(text=text):
                self.assertIn(diagnostic, self.approve(text, expected=2))
                self.assertEqual(self.state()["status"], "READY_FOR_REVIEW")
        self.assertEqual(len(self.calls()), 1)

    def test_gold_ci_failure_preserves_review_turn(self):
        self.start()
        self.mode("fail")
        self.assertIn("gold approval blocked: project-ci exited 7", self.approve(expected=2))
        self.assertEqual(self.state()["status"], "READY_FOR_REVIEW")
        self.assertNotIn("gold_ci", self.state())
        self.assertIn("Synthetic CI output: fail", (self.run_path / "gold-ci-round-01.log").read_text())

    def test_gold_approval_refuses_dirty_tree_before_ci(self):
        self.start()
        self.source.write_text("uncommitted change")
        self.assertIn("tracked working tree changes", self.approve(expected=2))
        self.assertEqual(len(self.calls()), 1)
        self.assertEqual(self.state()["status"], "READY_FOR_REVIEW")

    def test_gold_approval_refuses_changed_head_before_ci(self):
        self.start()
        self.git("commit", "-qm", "Later commit", "--allow-empty")
        self.assertIn("review head must be checked out", self.approve(expected=2))
        self.assertEqual(len(self.calls()), 1)

    def test_gold_ci_cannot_change_reviewed_source(self):
        self.start()
        self.mode("dirty")
        self.assertIn("tracked working tree changes", self.approve(expected=2))
        self.assertEqual(self.state()["status"], "READY_FOR_REVIEW")

    def test_gold_ci_cannot_change_reviewed_head(self):
        self.start()
        self.mode("head")
        self.assertIn("review head must be checked out", self.approve(expected=2))
        self.assertEqual(self.state()["status"], "READY_FOR_REVIEW")

    def test_gold_rereview_strict_ci_and_durable_archive(self):
        inherited = dict(self.env, ALLOW_UNRESOLVED_LXXXX="1", MAKEFLAGS="n", MFLAGS="-n", MAKEOVERRIDES="ALLOW_UNRESOLVED_LXXXX=1")
        self.start(env=inherited)
        prompt = (self.root / self.state()["prompts"]["reviewer"]).read_text()
        self.assertIn("Assess the WHOLE project", prompt)
        review = self.run_path / "review-01.md"
        review.write_text("Verdict: CHANGES_REQUESTED\nClose remaining gap.\n")
        self.command("request-changes", "--review", str(review))
        self.source.write_text("RunGameFrame:\n  RTS\n")
        self.commit()
        response = self.run_path / "response-01.md"
        response.write_text("Gap closed.\n")
        self.command("reready", "--response", str(response), "--head", "HEAD", "--generate-packet", env=inherited)
        self.approve(round_number=2, env=inherited)
        state = self.state()
        self.assertTrue(state["gold"])
        self.assertEqual(state["round"], 2)
        self.assertEqual(state["gold_ci"]["head"], self.git("rev-parse", "HEAD"))
        self.assertEqual(state["gold_ci"]["exit_status"], 0)
        self.assertEqual(self.calls()[-1]["argv"], ["project-ci", "PROJECT=demo"])
        for call in self.calls():
            self.assertTrue(all(value is None for value in call["env"].values()), call)
        prompt = (self.root / state["prompts"]["implementer"]).read_text()
        self.assertIn("GOLD STANDARD APPROVED", prompt)
        self.assertNotIn("A new pass may start", prompt)
        self.command("archive", "--pass-id", "1")
        archive = (self.root / "projects/demo/docs/reverse_engineering/reviews/pass-1.md").read_text()
        self.assertIn("## Gold Completion Evidence", archive)
        self.assertIn("make project-ci PROJECT=demo", archive)
        self.assertIn("## Gold-Standard Assessment", archive)
        self.assertIn(state["review_head"], archive)

    def test_gold_archive_refuses_later_commits(self):
        self.start()
        self.approve()
        self.git("commit", "-qm", "Later commit", "--allow-empty")
        self.assertIn("review head must be checked out", self.command("archive", "--pass-id", "1", expected=2))


if __name__ == "__main__":
    unittest.main()
