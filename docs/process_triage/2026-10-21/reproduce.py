#!/usr/bin/env python3
"""Triage probes against unchanged tools; all fixture writes are temporary."""

import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True


def run(argv, cwd, **kwargs):
    return subprocess.run(argv, cwd=cwd, text=True, capture_output=True,
                          timeout=30, **kwargs)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = args.repo.resolve()
    sys.path.insert(0, str(repo / "scripts"))
    import agent_review as review
    import process_friction as friction
    import policy_baseline_audit_check as policy

    files = ["scripts/agent_review.py", "scripts/process_friction.py",
             "scripts/project_pass_review_packet.sh", "scripts/policy_baseline_audit_check.py",
             "tests/shell/cases/pass_review_packet_test.sh"]
    result = {"tool_head": run(["git", "rev-parse", "HEAD"], repo).stdout.strip(),
              "python": sys.version.split()[0],
              "input_sha256": {f: hashlib.sha256((repo / f).read_bytes()).hexdigest() for f in files}}
    with tempfile.TemporaryDirectory(prefix="friction-probes-") as tmp:
        root = Path(tmp).resolve() / "checkout with ' spaces"
        stub = Path(tmp) / "make-stub"
        setup = 'REPO_ROOT="$1"; source "$1/tests/shell/cases/pass_review_packet_test.sh"; _init_packet_repo "$2" demo; _write_make_stub "$3"'
        proc = run(["bash", "-c", setup, "probe", str(repo), str(root), str(stub)], repo)
        assert proc.returncode == 0, proc.stderr
        other = root / "projects/other/notes.md"
        other.parent.mkdir()
        other.write_text("other project\n")
        run(["git", "add", "projects/other/notes.md"], root).check_returncode()
        run(["git", "commit", "-qm", "Add other fixture project"], root).check_returncode()
        base = run(["git", "rev-parse", "HEAD~3"], root).stdout.strip()
        head = run(["git", "rev-parse", "HEAD"], root).stdout.strip()
        env = dict(os.environ, MAKE_BIN=str(stub), XASM_BIN=shutil.which("true"),
                   PYTHONDONTWRITEBYTECODE="1")
        packet = ["bash", str(root / "scripts/project_pass_review_packet.sh"), "demo", base, head]
        cases = {}

        def guard_case(name):
            try:
                review.ensure_clean_tracked(root)
                handoff = "accepted"
            except review.UserError:
                handoff = "refused"
            p = run(packet, root, env=env)
            cases[name] = {"handoff_guard": handoff, "packet_exit": p.returncode,
                           "packet_stale_guard": "tracked working tree changes would make gate evidence stale" in p.stderr}
            return p

        clean = guard_case("clean")
        # The packet's quality gates are fixture stubs, not a project verification.
        assert not cases["clean"]["packet_stale_guard"], clean.stderr
        (root / "projects/other/untracked.txt").write_text("untracked\n")
        guard_case("untracked_other_project")
        for name, path, staged in (
            ("unstaged_other_project", other, False),
            ("staged_other_project", other, True),
            ("unstaged_selected_project", root / "projects/demo/asm/demo.asm", False),
            ("unstaged_shared_tool", root / "scripts/project_common.sh", False),
        ):
            original = path.read_bytes()
            path.write_bytes(original + b"\n# probe\n")
            if staged:
                run(["git", "add", str(path.relative_to(root))], root).check_returncode()
            guard_case(name)
            assert cases[name] == {"handoff_guard": "refused", "packet_exit": 2, "packet_stale_guard": True}
            path.write_bytes(original)
            if staged:
                run(["git", "add", str(path.relative_to(root))], root).check_returncode()
        assert cases["clean"]["handoff_guard"] == cases["untracked_other_project"]["handoff_guard"] == "accepted"
        result["tracked_guard"] = cases

        doc = "# Process Friction\n\n## Review source: pass 7, archive pending\n\n- Inspection prompted.\n"
        items = list(friction.queue_candidates(doc, "queue.md").values())
        control = friction.queue_candidates("# Process Friction\n\n- Inspection prompted.\n  Source: review pass 7.\n", "queue.md")
        assert len(items) == 2 and len(control) == 1
        assert not friction.queue_candidates("# Process Friction\n\n_None._\n", "queue.md")
        result["queue_metadata"] = {"heading_and_bullet": items, "indented_source_count": len(control), "empty_count": 0}

        manifest = Path(tmp) / "policy.csv"
        marker = policy.Marker(1, 7, "advisory", 0, 0, 1, 1, 1, "reviewed")
        outcomes = {}
        for rationale in ("Internal branch target.", "An external caller requires this global.", ""):
            with manifest.open("w", newline="") as f:
                writer = csv.writer(f)
                writer.writerow(policy.MANIFEST_FIELDS)
                writer.writerow(["BranchTarget", "global", "retained_headerless", "retain_global", rationale])
            errors = policy.check_manifest(manifest, marker, set(), {"BranchTarget"})
            outcomes[rationale or "<empty>"] = len(errors)
        assert list(outcomes.values()) == [0, 0, 1]
        result["policy_rationale_validation"] = {"errors": outcomes, "scope": "manifest validator; no semantic caller proof"}

        trace = root / "projects/demo/tools/trace"
        trace.mkdir(parents=True)
        for name in ("run_probe.py", "analyze_probe.py"):
            (trace / name).write_text("import json, os, sys\nprint(json.dumps({'cwd': os.getcwd(), 'args': sys.argv[1:]}))\n")
        helper = [sys.executable, str(repo / "scripts/agent_review.py"), "--repo", str(root)]
        tail = ["--scenario", "one", "--frames", "60", "--timeout", "5"]
        bad = run([sys.executable, str(root), "trace-project", "demo", "run_probe.py", "--", *tail], repo)
        assert bad.returncode == 1 and "can't find '__main__' module" in bad.stderr
        repetitions = 0
        for action, name in (("trace-project", "run_probe.py"), ("analyze-project", "analyze_probe.py")):
            for _ in range(10):
                p = run([*helper, action, "demo", name, "--", *tail], repo)
                assert p.returncode == 0, p.stderr
                assert json.loads(p.stdout) == {"cwd": str(root), "args": tail}
                repetitions += 1
        result["python_invocation"] = {"directory_program_exit": bad.returncode,
                                        "missing_main": True, "valid_stub_dispatches": repetitions,
                                        "emulator_runs": 0}

        codex = shutil.which("codex")
        if not codex:
            result["prefix_rules"] = {"status": "skipped", "reason": "codex unavailable"}
        else:
            # Offline policy checks do not execute the supplied commands.
            rules = Path(tmp) / "probe.rules"
            rules.write_text('prefix_rule(pattern=["python3", "/fixture/scripts/agent_review.py", "--repo", "/fixture", "start-pass", "--project", "demo"], decision="allow")\n')
            prefix = ["python3", "/fixture/scripts/agent_review.py", "--repo", "/fixture", "start-pass"]
            qualified = [*prefix, "--project", "demo"]
            policy_cases = {
                "unqualified_help": [*prefix, "--help"],
                "qualified_help": [*qualified, "--help"],
                "qualified_handoff_multiline": [*qualified, "--pass-id", "7", "--learning", "First line\nSecond line: `literal` and agent's note."],
                "other_project": [*prefix, "--project", "other", "--help"],
            }
            policy_cases["wrapped_handoff_multiline"] = ["/bin/zsh", "-lc", shlex.join(policy_cases["qualified_handoff_multiline"])]
            policy_cases["wrapped_qualified_help"] = ["/bin/zsh", "-lc", shlex.join(policy_cases["qualified_help"])]
            outcomes = {}
            for name, argv in policy_cases.items():
                p = run([codex, "execpolicy", "check", "--rules", str(rules), "--", *argv], repo)
                assert p.returncode == 0, p.stderr
                data = json.loads(p.stdout)
                outcomes[name] = {"decision": data.get("decision"), "match_count": len(data.get("matchedRules", []))}
            assert outcomes["qualified_help"]["decision"] == "allow"
            assert outcomes["unqualified_help"]["decision"] != "allow"
            assert outcomes["other_project"]["decision"] != "allow"
            result["prefix_rules"] = {"version": run([codex, "--version"], repo).stdout.strip(), "cases": outcomes,
                                      "scope": "one supplied rule file; not a live approval test"}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
