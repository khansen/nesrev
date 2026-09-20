#!/usr/bin/env python3
"""Exercise guarded staging and commits against a real disposable Git index."""

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))
import agent_review as review
import agent_review_permissions as permissions


class ProjectGitTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve() / "checkout with spaces"
        self.root.mkdir()
        self.git("init", "-q")
        for key, value in (("user.name", "Test"), ("user.email", "test@example.invalid"),
                           ("commit.gpgsign", "false")):
            self.git("config", key, value)
        self.project = self.root / "projects/demo"
        self.project.mkdir(parents=True)
        for name, content in {
            "projects/demo/project.conf": 'PROJECT_NAME="demo"\n',
            "projects/demo/source.asm": "Entry:\n  RTS\n",
            "projects/demo/old file.asm": "Old:\n  RTS\n",
            "projects/other/source.asm": "Other:\n  RTS\n",
            ".gitignore": "projects/*/tmp/\n",
            "README.md": "Unrelated\n",
        }.items():
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
        self.git("add", "--", ".")
        self.git("commit", "-qm", "Initial fixture")
        (self.project / "tmp").mkdir()
        (self.project / "tmp/commit-message.txt").write_text("Document project\n")
        (self.project / "source.asm").write_text("RunGame:\n  RTS\n")
        self.stage, self.commit = permissions.grants(self.root, "demo", "implementer")[1:3]

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.root), *args], text=True)

    def command(self, argv, expected=0):
        result = subprocess.run(argv, cwd=Path(self.temp.name), text=True, capture_output=True)
        self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
        return result

    def index(self):
        return (self.root / ".git/index").read_bytes()

    def test_exact_add_modify_delete_and_rename_commit_leave_unrelated_work_unstaged(self):
        (self.project / "new file.asm").write_text("New:\n RTS\n")
        (self.project / "old file.asm").rename(self.project / "renamed file.asm")
        (self.root / "README.md").write_text("Keep me unstaged\n")
        paths = ["projects/demo/" + name for name in
                 ("source.asm", "new file.asm", "old file.asm", "renamed file.asm")]
        self.command([*self.stage, *paths])
        self.assertEqual(set(self.git("diff", "--cached", "--name-only", "--no-renames").splitlines()), set(paths))
        self.command(self.commit)
        self.assertEqual(self.git("log", "-1", "--format=%s").strip(), "Document project")
        self.assertEqual(self.git("diff", "--name-only").strip(), "README.md")
        self.assertFalse(self.git("diff", "--cached", "--name-only"))

    def test_broad_pathspecs_and_outside_paths_refused_before_any_staging(self):
        for name in (".", "*", "-A", ":(top)*", "projects/demo", "projects/demo/",
                     "projects/demo/*", "projects/demo/*.asm", "projects/demo/[so]*",
                     "projects/demo/../other/source.asm", "projects//demo/source.asm",
                     "projects/demo/./source.asm", "projects/other/source.asm", "README.md",
                     str(self.project / "source.asm"), "projects/demo/missing.asm",
                     "--project", "projects/demo/tmp", "projects/demo/.git/config"):
            with self.subTest(name=name):
                before = self.index()
                self.command([*self.stage, "projects/demo/source.asm", name], expected=2)
                self.assertEqual(self.index(), before)

    def test_symlink_file_and_directory_refused_without_index_changes(self):
        (self.project / "link.asm").symlink_to(self.root / "README.md")
        (self.project / "linkdir").symlink_to(self.root / "projects/other", target_is_directory=True)
        for name in ("link.asm", "linkdir/source.asm"):
            before = self.index()
            self.command([*self.stage, f"projects/demo/{name}"], expected=2)
            self.assertEqual(self.index(), before)

    def test_commit_rejects_paths_flags_and_project_override_suffixes(self):
        self.command([*self.stage, "projects/demo/source.asm"])
        for suffix in (["."], ["--", "."], ["--amend"], ["--project", "other"], ["other"]):
            with self.subTest(suffix=suffix):
                head, index = self.git("rev-parse", "HEAD"), self.index()
                self.command([*self.commit, *suffix], expected=2)
                self.assertEqual(self.git("rev-parse", "HEAD"), head)
                self.assertEqual(self.index(), index)

    def test_commit_refuses_preexisting_unrelated_staged_files_and_deletions(self):
        for name, deletion in (("README.md", False), ("projects/other/source.asm", True)):
            with self.subTest(name=name):
                if deletion:
                    (self.root / name).unlink()
                else:
                    (self.root / name).write_text("Unrelated staged work\n")
                self.git("add", "--", name)
                self.command([*self.stage, "projects/demo/source.asm"])
                head, index = self.git("rev-parse", "HEAD"), self.index()
                self.command(self.commit, expected=2)
                self.assertEqual(self.git("rev-parse", "HEAD"), head)
                self.assertEqual(self.index(), index)
                self.git("reset", "-q", "HEAD", "--", name)

    def test_missing_or_symlinked_commit_message_is_refused(self):
        self.command([*self.stage, "projects/demo/source.asm"])
        message = self.project / "tmp/commit-message.txt"
        message.unlink()
        self.command(self.commit, expected=2)
        message.symlink_to(self.root / "README.md")
        self.command(self.commit, expected=2)
        self.assertEqual(self.git("log", "-1", "--format=%s").strip(), "Initial fixture")

    def test_other_project_grants_work_only_for_their_selected_project(self):
        other = self.root / "projects/other"
        (other / "project.conf").write_text('PROJECT_NAME="other"\n')
        (other / "tmp").mkdir()
        (other / "tmp/commit-message.txt").write_text("Other project\n")
        stage, commit = permissions.grants(self.root, "other", "implementer")[1:3]
        self.command([*stage, "projects/demo/source.asm"], expected=2)
        self.command([*stage, "projects/other/project.conf"])
        self.command(commit)
        self.assertEqual(self.git("log", "-1", "--format=%s").strip(), "Other project")


if __name__ == "__main__":
    unittest.main()
