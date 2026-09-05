"""Synthetic complete packet fixture shared by producer/consumer tests."""
import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from review_packet_evidence import COMMANDS, GATES, TOOLS, failure_summary


def environment_fixture():
    return {"status": "pass", "failures": [],
            "context": {"doc_root": "docs", "crosswalk": "crosswalk"},
            "tools": {name: {"requested": "xasm" if name == "assembler" else name,
                             "path": f"/synthetic/bin/{name}", "sha256": "b" * 64,
                             "status": "present"} for name in TOOLS},
            "inputs": {name: {"path": f"/synthetic/{name}", "sha256": "c" * 64,
                              "size": 16, "status": "present"} for name in ("source", "reference")}}


def packet(head, project="demo", statuses=None, verify_output="Verification complete",
           verify_command=None, title="Packet", environment=None, state_integrity="pass"):
    statuses = statuses or {}
    environment = environment if environment is not None else environment_fixture()
    commands = {name: f"make {name} PROJECT={project}" for name in GATES}
    commands.update({"cache-preparation": f"make project-pass-prep PROJECT={project}",
                     "next-pass": f"make project-next-pass PROJECT={project}",
                     "proof-debt": "python3 scripts/proof_debt.py docs crosswalk",
                     "crosswalk": "python3 scripts/proof_debt.py --crosswalk-only docs crosswalk"})
    if verify_command is not None:
        commands["project-verify"] = verify_command
    for name in (*GATES, "cache-preparation", "next-pass"):
        if "XASM_BIN=" not in commands[name]:
            commands[name] = "XASM_BIN=xasm " + commands[name]
    commands["cache-preparation"] = "PROJECT_PASS_PREP_WRITE_RAW_RAM_REVIEW=0 " + commands["cache-preparation"]
    records = [{"name": name, "review_head": head, "command": commands[name],
                "exit_status": statuses.get(name, 0)} for name in COMMANDS]
    failures = failure_summary(environment, records, state_integrity)
    summary = {"schema_version": 1, "review_head": head, "project": project,
               "environment": environment, "state_integrity": state_integrity,
               "gates": records[:len(GATES)], "supporting_evidence": records[len(GATES):],
               "failures": failures, "status": "fail" if failures else "pass"}
    sections = [f"# {title}\n\n## Reviewed State\n\n- Project: `{project}`\n- Review head SHA: `{head}`\n"]
    def block(label, command, status, output):
        fence = "`" * max(3, max((len(value) for value in re.findall(r"`+", output)), default=0) + 1)
        sections.append(f"\n### {label}\n\nState: `review_head {head}`\n\nCommand:\n\n```sh\n{command}\n```\n\nExit status: `{status if status is not None else 'not-run'}`\n\nOutput:\n\n{fence}text\n{output}\n{fence}\n")
    block("Build and Fixture Prerequisites", "python3 scripts/review_packet_evidence.py environment",
          int(environment["status"] != "pass"), json.dumps(environment))
    for record in records:
        output = verify_output if record["name"] == "project-verify" else "Synthetic evidence"
        block(COMMANDS[record["name"]], record["command"], record["exit_status"], output)
    sections.append("\n## Required Gate Summary\n\n```json\n" + json.dumps(summary, indent=2) + "\n```\n")
    return "".join(sections)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--head", required=True)
    parser.add_argument("--project", default="demo")
    parser.add_argument("--title", default="Packet")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verify-output", default="Verification complete")
    parser.add_argument("--verify-command")
    parser.add_argument("--verify-exit", type=int, default=0)
    parser.add_argument("--process-exit", type=int, default=0)
    parser.add_argument("--docs-exit", type=int, default=0)
    args = parser.parse_args()
    value = packet(args.head, args.project, {"project-verify": args.verify_exit,
                   "project-process-check": args.process_exit, "project-docs-check": args.docs_exit},
                   args.verify_output, args.verify_command, args.title)
    if args.output:
        args.output.write_text(value)
    else:
        print(value, end="")


if __name__ == "__main__":
    main()
