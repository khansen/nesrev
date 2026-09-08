#!/usr/bin/env python3
"""Synthetic producer/refusal tests; no private project inputs."""

import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import analysis_bundle as bundle


class BundleTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="nesrev-bundle-test-")
        self.root = Path(self.temporary.name)
        self.source = self.root / "input.asm"
        (self.root / "parts").mkdir()
        self.include = self.root / "parts" / "data.inc"
        self.payload = self.root / "parts" / "bytes.bin"
        self.config = self.root / "project.conf"
        self.policy = self.root / "extents.csv"
        self.missing = self.root / "optional.conf"
        self.source.write_text('.ORG $C000\nReset:\n LDX #0\n LDA Table,X\n RTS\n.INCSRC "parts/data.inc"\n')
        self.include.write_text('Table:\n.DB 1,2,3\nTail:\n.INCBIN "bytes.bin"\n')
        self.payload.write_bytes(b"\x04\x05")
        self.config.write_text('NESREV_RECOVERY_STATUS="none"\n')
        self.policy.write_text("label,expected_size,reason\nTable,3,three bytes\nTail,2,two bytes\n")
        self.cwd = os.getcwd()
        os.chdir(self.root)
        self.directory = self.root / "analysis"
        self.directory.mkdir()
        self.context = {"profile": bundle.PROFILE, "project": "synthetic", "config": str(self.config),
                        "source": str(self.source), "source_argument": str(self.source),
                        "rom_range": "$C000-$FFFF", "cpu_base": "$C000",
                        "policies": [bundle.fingerprint(p, optional=True) for p in
                                     (self.config, self.policy, self.missing)]}
        bundle.write_json(self.directory / "context.json", self.context)
        self.path = self.directory / "bundle.json"

    def tearDown(self):
        os.chdir(self.cwd)
        self.temporary.cleanup()

    def produce(self):
        self.assertEqual(bundle.produce(str(self.directory), str(self.source), str(self.root / "out.bin")), 0)
        return bundle.Bundle(self.path, self.source)

    def test_production_and_standalone_equivalence(self):
        shared = self.produce()
        self.assertEqual(set(shared.data["outputs"]), bundle.ARTIFACTS)
        self.assertEqual(len(shared.load("data_consumers")), 2)
        shared.load("listing")
        shared.load("index_patterns")
        shared.load("xref")
        for script, args in [("embedded_pointer_audit.py", [str(self.source)]),
                             ("data_extent_assertions_check.sh", [str(self.source), str(self.policy)])]:
            command = [sys.executable if script.endswith(".py") else "bash", str(ROOT / "scripts" / script)] + args
            plain = subprocess.run(command, capture_output=True)
            env = dict(os.environ, NESREV_ANALYSIS_BUNDLE=str(self.path))
            reused = subprocess.run(command, env=env, capture_output=True)
            self.assertEqual((reused.returncode, reused.stdout, reused.stderr),
                             (plain.returncode, plain.stdout, plain.stderr))
            self.assertEqual(reused.returncode, 0, reused.stderr)

    def test_independent_same_size_timestamp_mutations(self):
        shared = self.produce()
        for path in (self.source, self.include, self.payload, self.config, self.policy):
            with self.subTest(path=path.name):
                original, before = path.read_bytes(), path.stat()
                path.write_bytes(bytes([original[0] ^ 1]) + original[1:])
                os.utime(path, ns=(before.st_atime_ns, before.st_mtime_ns))
                with self.assertRaisesRegex(bundle.BundleError, "changed input or output"):
                    shared.validate()
                path.write_bytes(original)
                os.utime(path, ns=(before.st_atime_ns, before.st_mtime_ns))
                shared.validate()

    def test_missing_optional_policy_appears(self):
        shared = self.produce()
        self.missing.write_text("new policy")
        with self.assertRaisesRegex(bundle.BundleError, "changed input or output"):
            shared.validate()

    def test_negative_lookup_and_deleted_input(self):
        shared = self.produce()
        (self.root / "fallback").mkdir()
        (self.root / "fallback" / "child.inc").write_text("RTS\n")
        probe_source = self.root / "probe.asm"
        probe_source.write_text('.ORG $C000\n.INCSRC "child.inc"\n')
        manifest = self.root / "probe.json"
        command = [bundle.executable(), "--pure-binary", "-Ifallback", "-o", str(self.root / "probe.bin"),
                   "--dependency-manifest=" + str(manifest), str(probe_source)]
        self.assertEqual(subprocess.run(command).returncode, 0)
        deps = bundle.read_json(manifest)
        bundle.check_dependencies(deps, str(probe_source), command)
        self.assertTrue(deps["missing_paths"], "fixture must actually exercise negative lookups")
        candidate = Path(deps["missing_paths"][0])
        candidate.parent.mkdir(parents=True, exist_ok=True)
        candidate.write_bytes(b"new candidate")
        with self.assertRaisesRegex(bundle.BundleError, "new lookup candidate"):
            bundle.check_dependencies(deps, str(probe_source), command)
        candidate.unlink()
        shared.validate()
        self.payload.unlink()
        with self.assertRaises(FileNotFoundError):
            shared.validate()

    def test_changed_output_independently(self):
        shared = self.produce()
        for name, entry in shared.data["outputs"].items():
            with self.subTest(artifact=name):
                path = Path(entry["path"])
                original = path.read_bytes()
                path.write_bytes(original[:-1])
                with self.assertRaisesRegex(bundle.BundleError, "changed input or output"):
                    shared.validate()
                path.write_bytes(original)
                shared.validate()

    def test_descriptor_refusals_independently(self):
        shared = self.produce()
        mutations = [lambda d: d.update(version="99"), lambda d: d.update(complete=False),
                     lambda d: d["context"].update(profile="unknown"),
                     lambda d: d["outputs"].pop("listing"),
                     lambda d: d["argv"].append("--xref-instructions=true"),
                     lambda d: d["reader"].update(sha256="0" * 64)]
        for change in mutations:
            altered = copy.deepcopy(shared.data)
            change(altered)
            bundle.write_json(self.path, altered)
            with self.assertRaises(bundle.BundleError):
                bundle.Bundle(self.path, self.source)
            self.path.write_bytes(shared.raw)
            shared.validate()
        with self.assertRaisesRegex(bundle.BundleError, "source/project mismatch"):
            bundle.Bundle(self.path, self.include)
        with self.assertRaisesRegex(bundle.BundleError, "not bound"):
            shared.require_policy(self.include)

    def test_schema_refusals(self):
        shared = self.produce()
        for name in bundle.ARTIFACTS - {"binary"}:
            with self.subTest(artifact=name):
                with self.assertRaises(bundle.BundleError):
                    bundle.check_schema(name, {})
        listing = shared.load("listing")
        del listing["records"][0]["bytes_hex"]
        with self.assertRaisesRegex(bundle.BundleError, "listing.bytes_hex"):
            bundle.check_schema("listing", listing)
        with self.assertRaisesRegex(bundle.BundleError, "duplicate JSON key"):
            bundle.decode('{"version": "1", "version": "2"}')

    def test_profile_options_independent_of_manifest_argument_match(self):
        shared = self.produce()
        data = copy.deepcopy(shared.data)
        manifest_path = data["dependencies"]["path"]
        manifest = bundle.read_json(manifest_path)
        for argv in (data["argv"], manifest["invocation"]["argv"]):
            argv[argv.index("--xref-include-owner=true")] = "--xref-include-owner=false"
        bundle.write_json(manifest_path, manifest)
        data["dependencies"] = bundle.fingerprint(manifest_path)
        bundle.write_json(self.path, data)
        with self.assertRaisesRegex(bundle.BundleError, "option/profile mismatch"):
            bundle.Bundle(self.path, self.source)

    def test_zero_exit_with_missing_outputs_does_not_publish(self):
        actual_run = bundle.subprocess.run
        def remove_after_run(command):
            result = actual_run(command)
            (self.directory / "listing.json").unlink()
            return result
        with patch.object(bundle.subprocess, "run", side_effect=remove_after_run):
            with self.assertRaises(FileNotFoundError):
                bundle.produce(str(self.directory), str(self.source), str(self.root / "out.bin"))
        self.assertFalse(self.path.exists())

    def test_supplied_leaf_refusals_do_not_invoke_xasm(self):
        spy = self.root / "xasm"
        shutil.copyfile(ROOT / "tests/fixtures/analysis_count_xasm.py", spy)
        spy.chmod(0o755)
        calls = self.root / "calls.jsonl"
        env = dict(os.environ, BUNDLE_TEST_REAL_XASM=bundle.executable(), BUNDLE_TEST_CALLS=str(calls),
                   XASM_BIN=str(spy), PATH=str(self.root) + os.pathsep + os.environ["PATH"])
        with patch.dict(os.environ, env):
            shared = self.produce()
        self.assertEqual(len(calls.read_text().splitlines()), 1)
        calls.unlink()
        leaves = [("embedded_pointer_audit.py", [str(self.source)]),
                  ("data_extent_assertions_check.sh", [str(self.source), str(self.policy)])]
        env["NESREV_ANALYSIS_BUNDLE"] = str(self.path)
        for script, args in leaves:
            command = [sys.executable if script.endswith(".py") else "bash", str(ROOT / "scripts" / script)] + args
            run = subprocess.run(command, env=env, capture_output=True)
            self.assertEqual(run.returncode, 0, run.stderr)
            self.assertFalse(calls.exists())
        for supplied_path in ("", str(self.root / "missing.json"), str(self.path)):
            if supplied_path == str(self.path):
                Path(shared.data["outputs"]["listing"]["path"]).write_text("{")
            env["NESREV_ANALYSIS_BUNDLE"] = supplied_path
            for script, args in leaves:
                command = [sys.executable if script.endswith(".py") else "bash", str(ROOT / "scripts" / script)] + args
                run = subprocess.run(command, env=env, capture_output=True)
                self.assertEqual(run.returncode, 65, run.stderr)
                self.assertIn(b"refused:", run.stderr)
                self.assertNotIn(b"Traceback", run.stderr)
                self.assertFalse(calls.exists())

    def test_failed_producer_does_not_publish(self):
        with patch.object(bundle.subprocess, "run", return_value=subprocess.CompletedProcess([], 3)):
            self.assertEqual(bundle.produce(str(self.directory), str(self.source), str(self.root / "out.bin")), 3)
        self.assertFalse(self.path.exists())

    def test_old_manifest_refused_before_producer(self):
        (self.directory / "dependencies.json").write_text("{}")
        with patch.object(bundle.subprocess, "run") as run:
            with self.assertRaisesRegex(bundle.BundleError, "dependency output already exists"):
                bundle.produce(str(self.directory), str(self.source), str(self.root / "out.bin"))
            run.assert_not_called()

    def test_invalid_supplied_bundle_never_assembles(self):
        for path in ("", str(self.path)):
            with patch.dict(os.environ, {"NESREV_ANALYSIS_BUNDLE": path}), patch.object(bundle.subprocess, "run") as run:
                with self.assertRaises((bundle.BundleError, OSError)):
                    bundle.supplied(self.source)
                run.assert_not_called()

    def test_changed_descriptor_during_use(self):
        shared = self.produce()
        self.path.write_bytes(shared.raw + b" ")
        with self.assertRaisesRegex(bundle.BundleError, "descriptor changed"):
            shared.validate()

    def test_policy_output_alias_refused_before_execution(self):
        alias = self.root / "alias.bin"
        os.link(self.config, alias)
        before = self.config.read_bytes()
        with patch.object(bundle.subprocess, "run") as run:
            with self.assertRaisesRegex(bundle.BundleError, "aliases policy input"):
                bundle.produce(str(self.directory), str(self.source), str(alias))
            run.assert_not_called()
        self.assertEqual(self.config.read_bytes(), before)

    def test_production_detects_policy_change_before_publication(self):
        actual_run = bundle.subprocess.run
        def change_after_run(command):
            result = actual_run(command)
            self.config.write_text('NESREV_RECOVERY_STATUS="configured"\n')
            return result
        with patch.object(bundle.subprocess, "run", side_effect=change_after_run), \
                patch.object(bundle, "write_json", wraps=bundle.write_json) as publish:
            with self.assertRaisesRegex(bundle.BundleError, "changed input or output"):
                bundle.produce(str(self.directory), str(self.source), str(self.root / "out.bin"))
            publish.assert_not_called()
        self.assertFalse(self.path.exists())

    def test_selected_producer_change(self):
        shared = self.produce()
        replacement = self.root / "replacement-xasm"
        replacement.write_bytes(b"different executable")
        replacement.chmod(0o755)
        with patch.dict(os.environ, XASM_BIN=str(replacement)):
            with self.assertRaisesRegex(bundle.BundleError, "producer build mismatch"):
                shared.validate()

    def make_ci_fixture(self):
        project = self.root / "projects" / "synthetic"
        docs = project / "docs" / "reverse_engineering"
        inventory = docs / "inventory"
        inventory.mkdir(parents=True)
        (inventory / "pass").mkdir()
        (inventory / "pass/data_coverage.json").write_text("[]\n")
        for directory in ("asm", "reference", "build", "docs/crosswalk"):
            (project / directory).mkdir(parents=True, exist_ok=True)
        conf = {"PROJECT_NAME": "synthetic", "ASM_FILE": "projects/synthetic/asm/input.asm",
                "REF_NES": "projects/synthetic/reference/input.nes", "DOC_ROOT": "projects/synthetic/docs/reverse_engineering",
                "SYSTEMS_DOC": "projects/synthetic/docs/reverse_engineering/SYSTEMS.md",
                "WARN_BASELINE_FILE": "projects/synthetic/docs/reverse_engineering/WARNING_BASELINE.txt",
                "OUT_BIN": "projects/synthetic/build/out.bin", "NESREV_RECOVERY_STATUS": "none"}
        (project / "project.conf").write_text("".join(f'{key}="{value}"\n' for key, value in conf.items()))
        (project / "asm/input.asm").write_text('.ORG $C000\n; External vector entry returns to the test harness.\nReset:\n RTS\n.DSB 16377\n.DW Reset,Reset,Reset\n')
        prg = b"\x60" + bytes(16377) + b"\x00\xc0" * 3
        (project / "reference/input.nes").write_bytes(b"NES\x1a\x01\x00" + bytes(10) + prg)
        (docs / "WARNING_BASELINE.txt").write_text("")
        for name in ("ONBOARDING.md", "QUICK_REFERENCE.md", "MEMORY_MAP.md", "SYSTEMS.md"):
            (docs / name).write_text("# Synthetic harness\n\nReset returns immediately to its caller.\n")
        (project / "docs/crosswalk/TERMINOLOGY_CROSSWALK.md").write_text(
            "| Reference term / aliases | Asm symbol(s) | Mapping confidence | Evidence |\n|---|---|---|---|\n")
        from project_artifact_manifest import ARTIFACTS
        for artifact in ARTIFACTS:
            if artifact.header:
                (docs / artifact.relative_path).write_text(artifact.header + "\n")
        from data_format_targets_check import CANONICAL_FAMILIES
        with (inventory / "data_format_targets.csv").open("a") as stream:
            for family in sorted(CANONICAL_FAMILIES):
                stream.write(f"{family},absent_not_applicable,,Synthetic return-only fixture\n")
        (inventory / "renames.csv").write_text("old_name,new_name,reason,confidence,pass_id\n")
        (inventory / "policy_baseline.csv").write_text("symbol,inventory,disposition,localization,rationale\n")
        (inventory / "kpis.conf").write_text("".join(f"MAX_{key}=0\n" for key in (
            "ACTIVE_RAW_LOWADDR", "ACTIVE_RAW_ABSROM", "ACTIVE_MAGIC_IMMEDIATES", "ACTIVE_BRANCH_LITERALS",
            "INFERRED_ANNOTATIONS", "PLACEHOLDER_COMMENTS", "UNDOCUMENTED_PROCEDURES",
            "UNDOCUMENTED_GLOBAL_CODE_LABELS", "UNDOCUMENTED_DATA_LABELS")))
        (docs / "PROGRESS_SCORECARD.md").write_text(
            "| pass_id | focus | verify | docs_check | rework_items | notes |\n|---|---|---|---|---|---|\n"
            "| 1 | Return-only fixture | pass | pass | 0 | Analogue: none (synthetic harness). "
            "policy-baseline-audit: semantic_claims=reviewed; procedures=0/0; global_code_labels=0/0; "
            "retained_headerless=0; action=reviewed all detail rows. |\n")
        (docs / "SEMANTIC_CLAIMS.md").write_text(
            "# Semantic Claims\n\n## Claim: reset-entry\n\nSubject: Reset\nKind: subsystem\nSubsystem: boot\n"
            "Claim: reset returns to the harness.\nConfidence: high\nEvidence:\n- The fixture starts at `Reset`.\n"
            "Caveats:\n- None.\nCanonical docs:\n- SYSTEMS.md\n")
        shutil.copytree(ROOT / "scripts", self.root / "scripts", ignore=shutil.ignore_patterns("__pycache__"))
        shutil.copytree(ROOT / "agent_playbook", self.root / "agent_playbook")
        shutil.copyfile(ROOT / "AGENTS.md", self.root / "AGENTS.md")
        shutil.copyfile(ROOT / "Makefile", self.root / "Makefile")
        return project

    def test_complete_ci_assembles_once_and_mismatch_twice(self):
        project = self.make_ci_fixture()
        spy = self.root / "xasm"
        shutil.copyfile(ROOT / "tests/fixtures/analysis_count_xasm.py", spy)
        spy.chmod(0o755)
        calls = self.root / "calls.jsonl"
        env = dict(os.environ, BUNDLE_TEST_REAL_XASM=bundle.executable(), BUNDLE_TEST_CALLS=str(calls),
                   XASM_BIN=str(spy), PATH=str(self.root) + os.pathsep + os.environ["PATH"])
        init = subprocess.run(["bash", "scripts/refresh_inventory.sh", "synthetic"],
                              env=env, capture_output=True)
        self.assertEqual(init.returncode, 0, init.stderr)
        calls.write_text("")
        run = subprocess.run(["make", "project-ci", "PROJECT=synthetic"], env=env, capture_output=True)
        self.assertEqual(run.returncode, 0, run.stdout.decode() + run.stderr.decode())
        self.assertIn(b"Doc consistency checks passed", run.stdout)
        self.assertEqual(len(calls.read_text().splitlines()), 1)
        legacy = self.root / "scripts" / "baseline_ci.sh"
        legacy.write_text('''#!/usr/bin/env bash
set -euo pipefail
scratch="$(mktemp -d)"
trap 'rm -rf "${scratch}"' EXIT
export NESREV_XREF_FILE="${scratch}/xref_with_data.json"
bash scripts/project_verify.sh "$1"
bash scripts/project_process_check.sh "$1"
bash scripts/project_maturity_check.sh "$1"
bash scripts/project_docs_check.sh "$1"
''')
        calls.write_text("")
        baseline = subprocess.run(["bash", str(legacy), "synthetic"], env=env, capture_output=True)
        self.assertEqual(baseline.returncode, 0, baseline.stdout.decode() + baseline.stderr.decode())
        self.assertEqual(len(calls.read_text().splitlines()), 5)
        self.assertEqual(baseline.stdout, run.stdout.split(b"\n", 1)[1])
        self.assertEqual(baseline.stderr, run.stderr)
        reference = project / "reference/input.nes"
        raw = reference.read_bytes()
        reference.write_bytes(raw[:16] + b"\xea" + raw[17:])
        calls.write_text("")
        mismatch = subprocess.run(["make", "project-ci", "PROJECT=synthetic"], env=env, capture_output=True)
        self.assertEqual(mismatch.returncode, 2)
        self.assertIn(b"output PRG differs", mismatch.stderr)
        invocations = [json.loads(line) for line in calls.read_text().splitlines()]
        self.assertEqual(len(invocations), 2)
        self.assertTrue(any(arg.startswith("--compare=") for arg in invocations[1]))


if __name__ == "__main__":
    unittest.main()
