#!/usr/bin/env python3
"""Invocation-local assembled facts; see ANALYSIS_BUNDLE_SPEC.md."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tempfile

import instruction_records


class BundleError(ValueError):
    pass


PROFILE = "ci-data-v1"
ARTIFACTS = {"binary", "xref", "listing", "index_patterns", "data_consumers"}
PROFILES = {
    PROFILE: ARTIFACTS,
    "ci-instructions-v1": ARTIFACTS | {"instructions"},
    "inventory-instructions-v1": {"binary", "xref", "instructions"},
    "instructions-v1": {"binary", "instructions"},
    "pass-prep-instructions-v1": ARTIFACTS | {"instructions", "summary", "coverage"},
}
STRICT_PROFILES = {PROFILE, "ci-instructions-v1"}
ROLES = {"source", "binary", "charmap", "analysis_source", "comparison", "producer"}


def require(condition, message):
    if not condition:
        raise BundleError(message)


def absolute(path):
    # Keep lookup semantics through symlinks followed by '..'.
    return str(path) if os.path.isabs(path) else os.getcwd() + "/" + str(path)


def read_bytes(path):
    fd = os.open(path, os.O_RDONLY | os.O_NONBLOCK)
    with os.fdopen(fd, "rb") as stream:
        require(stat.S_ISREG(os.fstat(stream.fileno()).st_mode), f"not a regular file: {path}")
        return stream.read()


def fingerprint(path, optional=False):
    path = absolute(path)
    try:
        raw = read_bytes(path)
    except (FileNotFoundError, NotADirectoryError):
        if optional:
            return {"path": path, "missing": True}
        raise
    return {"path": path, "size": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}


def pairs_unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


READER_ID = fingerprint(__file__)
INSTRUCTION_READER_ID = fingerprint(instruction_records.__file__)


def decode(raw):
    return json.loads(raw, object_pairs_hook=pairs_unique)


def read_json(path):
    return decode(read_bytes(path))


def write_json(path, data):
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=Path(path).parent,
                                     delete=False) as stream:
        temporary = stream.name
        try:
            json.dump(data, stream, indent=2)
            stream.write("\n")
            stream.close()
            os.replace(temporary, path)
        finally:
            if os.path.exists(temporary):
                os.unlink(temporary)


def check_stamp(entry, optional=False):
    require(isinstance(entry, dict) and isinstance(entry.get("path"), str)
            and os.path.isabs(entry["path"]), "invalid fingerprint path")
    if optional and entry.get("missing") is True:
        require(set(entry) == {"path", "missing"}, "invalid absent-input fingerprint")
    else:
        require(type(entry.get("size")) is int and entry["size"] >= 0
                and isinstance(entry.get("sha256"), str)
                and re.fullmatch(r"[0-9a-f]{64}", entry["sha256"]), "invalid content fingerprint")
    actual = fingerprint(entry["path"], optional)
    expected = {key: entry[key] for key in actual if key in entry}
    require(actual == expected, f"changed input or output: {entry['path']}")


def executable():
    selected = os.environ.get("XASM_BIN", "xasm")
    found = shutil.which(selected)
    require(found is not None, f"xasm not found: {selected}")
    return absolute(found)


def check_dependencies(manifest, source, argv=None):
    require(isinstance(manifest, dict) and manifest.get("schema") == "xasm-dependencies"
            and manifest.get("version") == "1", "xasm dependency manifest version 1 required")
    require(isinstance(manifest.get("producer_version"), str), "missing producer version")
    invocation = manifest.get("invocation", {})
    require(isinstance(invocation, dict) and invocation.get("cwd") == os.getcwd(),
            "producer working directory mismatch")
    args = invocation.get("argv")
    require(isinstance(args, list) and args and all(isinstance(a, str) for a in args),
            "invalid producer arguments")
    if argv is not None:
        require(args == argv, "producer arguments mismatch")
    inputs = manifest.get("inputs")
    missing = manifest.get("missing_paths")
    require(isinstance(inputs, list) and inputs and isinstance(missing, list),
            "incomplete dependency manifest")
    producers, sources, paths = [], [], set()
    for entry in inputs:
        check_stamp(entry)
        require(entry["path"] not in paths, "duplicate dependency path")
        paths.add(entry["path"])
        roles = entry.get("roles")
        require(isinstance(roles, list) and roles and all(isinstance(r, str) for r in roles)
                and len(set(roles)) == len(roles) and set(roles) <= ROLES,
                "invalid dependency roles")
        if "producer" in roles:
            producers.append(entry)
        if "source" in roles:
            sources.append(entry["path"])
    require(source in sources, "root source absent from dependency manifest")
    require(len(producers) == 1, "exactly one producer dependency required")
    require(producers[0]["sha256"] == fingerprint(executable())["sha256"],
            "selected producer build mismatch")
    for path in missing:
        require(isinstance(path, str) and os.path.isabs(path) and path not in paths,
                "invalid or duplicate negative dependency")
        paths.add(path)
        require(fingerprint(path, optional=True).get("missing") is True,
                f"new lookup candidate: {path}")


def fields(row, types, name):
    require(isinstance(row, dict), f"invalid {name} record")
    for field, kind in types.items():
        require(type(row.get(field)) is kind, f"invalid {name}.{field}")


def check_schema(name, payload):
    if name == "instructions":
        instruction_records.validate(payload)
    elif name == "summary":
        require(isinstance(payload, dict) and all(isinstance(payload.get(key), list) for key in
                ("top_callables", "top_jump_targets", "top_data_labels")), "complete summary object required")
    elif name == "coverage":
        require(isinstance(payload, list), "coverage array required")
        for row in payload:
            fields(row, {"label": str, "declared_start": str, "declared_end_exclusive": str,
                         "declared_size": int, "covered_ranges": list, "covered_size": int,
                         "uncovered_ranges": list, "uncovered_size": int, "access_count": int,
                         "has_indexed_accesses_without_exact_coverage": bool}, name)
    elif name == "xref":
        require(isinstance(payload, dict) and payload.get("version") == "2",
                "xref version 2 required")
        require(all(isinstance(payload.get(key), list) for key in
                    ("symbols", "references", "data_directive_references")), "incomplete xref")
        require(isinstance(payload.get("build"), dict)
                and payload["build"].get("pure_binary") is True, "non-binary xref")
        require("instruction_records" not in payload, "instruction records must use the separate output")
    elif name == "listing":
        require(isinstance(payload, dict) and payload.get("version") == "1"
                and isinstance(payload.get("records"), list), "listing version 1 required")
        for row in payload["records"]:
            fields(row, {"file": str, "line": int, "column": int, "source_text": str,
                         "cpu_address_start": str, "cpu_address_end": str,
                         "output_offset_start": int, "output_offset_end": int,
                         "bytes_hex": list, "directive_or_opcode": str,
                         "continuation_of_record": bool}, name)
            require(all(isinstance(b, str) and re.fullmatch(r"[0-9A-F]{2}", b)
                        for b in row["bytes_hex"]), "invalid listing bytes")
    else:
        require(isinstance(payload, list), f"{name} array required")
        for row in payload:
            required = ({"table_label": str, "site_addr": str, "access_kind": str,
                         "access_pattern": str, "index_register": str, "displacement": int,
                         "index_value_source_kind": str} if name == "index_patterns" else
                        {"label": str, "declared_size": int, "declared_start": str,
                         "declared_end_exclusive": str, "read_sites": list, "write_sites": list})
            fields(row, required, name)


def check_context(context, source=None):
    require(isinstance(context, dict) and context.get("profile") in PROFILES,
            "unsupported bundle profile")
    for key in ("source", "source_argument"):
        require(isinstance(context.get(key), str) and context[key], f"missing context: {key}")
    require(os.path.isabs(context["source"]), "source path must be absolute")
    require(absolute(context["source_argument"]) == context["source"], "source argument mismatch")
    if source is not None:
        require(context["source"] == absolute(source), "bundle source/project mismatch")
    require(isinstance(context.get("policies"), list), "missing policy inputs")
    for policy in context["policies"]:
        check_stamp(policy, optional=True)
    if context["profile"] == "instructions-v1":
        require(all(context.get(key) is None for key in ("config", "project", "rom_range", "cpu_base")),
                "source-only profile cannot certify project context")
        return
    for key in ("config", "project", "rom_range", "cpu_base"):
        require(isinstance(context.get(key), str) and context[key], f"missing context: {key}")
    require(os.path.isabs(context["config"]), "configuration path must be absolute")
    require(context["config"] in [p["path"] for p in context["policies"]
                                   if not p.get("missing")], "configuration fingerprint missing")


class Bundle:
    def __init__(self, path, source=None):
        self.path = path
        self.raw = read_bytes(path)
        self.data = decode(self.raw)
        require(isinstance(self.data, dict) and self.data.get("schema") == "nesrev-analysis"
                and self.data.get("version") == "1" and self.data.get("complete") is True,
                "complete NESrev analysis bundle version 1 required")
        self.source = source
        self.validate()

    def validate(self):
        require(read_bytes(self.path) == self.raw, "bundle descriptor changed during reuse")
        check_context(self.data.get("context"), self.source)
        manifest = self.data.get("dependencies")
        check_stamp(manifest)
        dependencies = read_json(manifest["path"])
        check_dependencies(dependencies, self.data["context"]["source"], self.data.get("argv"))
        require(self.data.get("argv") == expected_argv(self.data["context"],
                self.data.get("outputs"), manifest["path"], dependencies["invocation"]["argv"][0]),
                "bundle option/profile mismatch")
        check_stamp(self.data.get("reader"))
        require(self.data["reader"]["sha256"] == READER_ID["sha256"], "bundle reader build mismatch")
        outputs = self.data.get("outputs")
        require(isinstance(outputs, dict) and set(outputs) == PROFILES[self.data["context"]["profile"]],
                "incomplete bundle outputs")
        for entry in outputs.values():
            check_stamp(entry)
        if "instructions" in outputs:
            check_stamp(self.data.get("instruction_reader"))
            require(self.data["instruction_reader"]["sha256"] == INSTRUCTION_READER_ID["sha256"],
                    "instruction reader build mismatch")

    def require_policy(self, path):
        require(absolute(path) in [p["path"] for p in self.data["context"]["policies"]],
                f"policy input not bound to bundle: {path}")

    def load(self, name):
        require(name in self.data["outputs"], f"bundle profile lacks required artifact: {name}")
        entry = self.data["outputs"][name]
        raw = read_bytes(entry["path"])
        require(hashlib.sha256(raw).hexdigest() == entry["sha256"], f"changed artifact: {name}")
        payload = decode(raw)
        check_schema(name, payload)
        if name == "instructions":
            dependencies = read_json(self.data["dependencies"]["path"])
            sources = {entry["path"] for entry in dependencies["inputs"] if "source" in entry["roles"]}
            instruction_records.check_sources(payload, sources, absolute)
            instruction_records.check_binary(payload, read_bytes(self.data["outputs"]["binary"]["path"]))
        return payload


def supplied(source):
    if "NESREV_ANALYSIS_BUNDLE" not in os.environ:
        return None
    path = os.environ["NESREV_ANALYSIS_BUNDLE"]
    require(bool(path), "empty supplied bundle path")
    return Bundle(path, source)


def expected_argv(context, outputs, manifest, producer):
    require(isinstance(outputs, dict) and set(outputs) == PROFILES[context["profile"]],
            "incomplete bundle outputs")
    argv = [producer, "--pure-binary"]
    if context["profile"] in STRICT_PROFILES:
        argv += ["--Werror=unused-equ"]
    argv += ["-o", outputs["binary"]["path"]]
    if "xref" in outputs:
        argv += ["--xref=" + outputs["xref"]["path"], "--xref-format=json",
                 "--xref-include-owner=true", "--xref-data=true"]
    if "listing" in outputs:
        argv += ["--listing=" + outputs["listing"]["path"], "--listing-format=json"]
    if "index_patterns" in outputs:
        argv += ["--analyze-index-patterns", "--index-patterns-output=" + outputs["index_patterns"]["path"],
                 "--index-patterns-format=json"]
    if "data_consumers" in outputs:
        argv += ["--data-consumers", "--data-consumers-output=" + outputs["data_consumers"]["path"],
                 "--data-consumers-format=json"]
    if "instructions" in outputs:
        argv += ["--instruction-records-output=" + outputs["instructions"]["path"]]
    if "summary" in outputs:
        argv += ["--xref-summary", "--xref-summary-output=" + outputs["summary"]["path"],
                 "--xref-summary-format=json"]
    if "coverage" in outputs:
        argv += ["--analyze-data-coverage", "--data-coverage-output=" + outputs["coverage"]["path"],
                 "--data-coverage-format=json"]
    return argv + ["--dependency-manifest=" + manifest, context["source_argument"]]


def prepare_source(directory, source, policies):
    context = {"profile": "instructions-v1", "project": None, "config": None,
               "source": absolute(source), "source_argument": str(source),
               "rom_range": None, "cpu_base": None,
               "policies": [fingerprint(p) for p in dict.fromkeys(policies)]}
    check_context(context)
    write_json(Path(directory) / "context.json", context)


def produce(directory, source, output, profile=None):
    directory = Path(absolute(directory))
    context = read_json(directory / "context.json")
    check_context(context, source)
    if profile is not None:
        require(context["profile"] == profile, "production profile mismatch")
    require(not (directory / "bundle.json").exists(), "bundle already published")
    outputs = {name: {"path": str(directory / (name + ".json"))} for name in PROFILES[context["profile"]]}
    if "xref" in outputs:
        outputs["xref"] = {"path": str(directory / "xref_with_data.json")}
    outputs["binary"] = {"path": absolute(output)}
    for policy in context["policies"]:
        target = outputs["binary"]["path"]
        require(target != policy["path"] and not
                (os.path.exists(target) and os.path.exists(policy["path"])
                 and os.path.samefile(target, policy["path"])), "binary output aliases policy input")
    manifest = str(directory / "dependencies.json")
    require(not os.path.lexists(manifest), "dependency output already exists")
    argv = expected_argv(context, outputs, manifest, executable())
    rc = subprocess.run(argv).returncode
    if rc:
        return 128 - rc if rc < 0 else rc
    dependencies = read_json(manifest)
    check_dependencies(dependencies, context["source"], argv)
    for name, entry in outputs.items():
        raw = read_bytes(entry["path"])
        if name != "binary":
            check_schema(name, decode(raw))
        entry.update(size=len(raw), sha256=hashlib.sha256(raw).hexdigest())
    data = {"schema": "nesrev-analysis", "version": "1", "complete": True,
            "context": context, "dependencies": fingerprint(manifest), "argv": argv,
            "outputs": outputs, "reader": READER_ID}
    if "instructions" in outputs:
        data["instruction_reader"] = INSTRUCTION_READER_ID
    check_context(context, source)
    check_dependencies(dependencies, context["source"], argv)
    write_json(directory / "bundle.json", data)
    try:
        Bundle(directory / "bundle.json", source)
    except Exception:
        (directory / "bundle.json").unlink()
        raise
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    stamp = commands.add_parser("fingerprint")
    stamp.add_argument("path")
    prepare = commands.add_parser("prepare")
    for arg in ("directory", "project", "config", "config_digest", "source", "rom_range", "cpu_base"):
        prepare.add_argument(arg)
    prepare.add_argument("policies", nargs="*")
    prepare.add_argument("--profile", choices=sorted(PROFILES), default=PROFILE)
    source_prepare = commands.add_parser("prepare-source")
    source_prepare.add_argument("directory")
    source_prepare.add_argument("source")
    source_prepare.add_argument("policies", nargs="*")
    artifact = commands.add_parser("artifact")
    artifact.add_argument("path")
    artifact.add_argument("name")
    produce_cmd = commands.add_parser("produce")
    for arg in ("directory", "source", "output"):
        produce_cmd.add_argument(arg)
    produce_cmd.add_argument("--profile", choices=sorted(PROFILES))
    validate = commands.add_parser("validate")
    validate.add_argument("path")
    validate.add_argument("--source")
    validate.add_argument("--project")
    validate.add_argument("--config")
    validate.add_argument("--rom-range")
    validate.add_argument("--cpu-base")
    validate.add_argument("--policy", action="append", default=[])
    validate.add_argument("--xref")
    validate.add_argument("--artifact", action="append", default=[])
    validate.add_argument("--profile", choices=sorted(PROFILES))
    args = parser.parse_args()
    if args.command == "fingerprint":
        print(fingerprint(args.path)["sha256"])
    elif args.command == "prepare":
        config = fingerprint(args.config)
        require(config["sha256"] == args.config_digest, "configuration changed while loading")
        require(args.profile != "instructions-v1", "use prepare-source for the source-only profile")
        context = {"profile": args.profile, "project": args.project, "config": absolute(args.config),
                   "source": absolute(args.source), "source_argument": args.source,
                   "rom_range": args.rom_range, "cpu_base": args.cpu_base,
                   "policies": [fingerprint(p, optional=True) for p in
                                dict.fromkeys([args.config] + args.policies)]}
        check_context(context)
        write_json(Path(args.directory) / "context.json", context)
    elif args.command == "prepare-source":
        prepare_source(args.directory, args.source, args.policies)
    elif args.command == "produce":
        return produce(args.directory, args.source, args.output, args.profile)
    elif args.command == "artifact":
        bundle = Bundle(args.path)
        require(args.name in bundle.data["outputs"], f"bundle profile lacks required artifact: {args.name}")
        print(bundle.data["outputs"][args.name]["path"])
    else:
        bundle = Bundle(args.path, args.source)
        if args.profile:
            require(bundle.data["context"]["profile"] == args.profile, "bundle profile mismatch")
        for artifact in args.artifact:
            require(artifact in bundle.data["outputs"], f"bundle profile lacks required artifact: {artifact}")
        for policy in args.policy:
            bundle.require_policy(policy)
        if args.xref is not None:
            require(absolute(args.xref) == bundle.data["outputs"]["xref"]["path"], "shared xref path mismatch")
        for key in ("project", "config", "rom_range", "cpu_base"):
            expected = getattr(args, key)
            if expected is not None:
                if key == "config":
                    expected = absolute(expected)
                require(bundle.data["context"][key] == expected, f"bundle {key} mismatch")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BundleError, OSError, ValueError, KeyError, TypeError) as exc:
        print(f"error: analysis bundle refused: {exc}", file=sys.stderr)
        raise SystemExit(65)
