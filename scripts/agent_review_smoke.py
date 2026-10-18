"""Prepare a live permission smoke test without starting the pass/review loop."""

from __future__ import annotations

import json
import shlex
from pathlib import Path

import agent_review as review


def load_spec(root: Path, project: str, path: Path) -> dict:
    try:
        spec = json.loads(path.read_text())
        if (not isinstance(spec, dict) or not {"inspection", "trace"} <= set(spec)
                or set(spec) - {"inspection", "trace", "analysis", "trace_role"}):
            raise ValueError("expected inspection/trace and optional analysis/trace_role")
        if spec.get("trace_role", "implementer") not in {"implementer", "reviewer"}:
            raise ValueError("trace_role must be implementer or reviewer")
        inspection, trace = spec["inspection"], spec["trace"]
        if (not isinstance(inspection, dict) or set(inspection) != {"path", "symbols"}
                or not isinstance(trace, dict) or set(trace) != {"driver", "arguments"}
                or not isinstance(inspection["path"], str) or not isinstance(trace["driver"], str)
                or not isinstance(inspection["symbols"], list) or not isinstance(trace["arguments"], list)
                or not all(isinstance(s, str) for s in inspection["symbols"] + trace["arguments"])):
            raise ValueError("invalid inspection/trace fields")
        matches = review.project_symbol_matches(root, project, inspection["path"], inspection["symbols"])
        if not matches["matches"]:
            raise ValueError("inspection must match project source")
        if any(arg in {"--help", "-h", "--version"} for arg in trace["arguments"]):
            raise ValueError("smoke requires a real capture, not help/version output")
        review.project_trace_argv(root, project, trace["driver"], trace["arguments"])
        if "analysis" in spec:
            analysis = spec["analysis"]
            if (not isinstance(analysis, dict) or set(analysis) != {"driver", "arguments"}
                    or not isinstance(analysis["driver"], str)
                    or not isinstance(analysis["arguments"], list)
                    or not all(isinstance(s, str) for s in analysis["arguments"])):
                raise ValueError("invalid analysis fields")
            if any(arg in {"--help", "-h", "--version"} for arg in analysis["arguments"]):
                raise ValueError("smoke requires real analysis, not help/version output")
            review.project_analysis_argv(root, project, analysis["driver"], analysis["arguments"])
        return spec
    except (OSError, ValueError, TypeError) as exc:
        raise review.UserError(f"invalid smoke specification: {exc}") from exc


def prompt(root: Path, project: str, role: str, spec: dict) -> str:
    tool = review.script_argv(root)
    operations = []
    if role == spec.get("trace_role", "implementer"):
        if "analysis" in spec:
            analysis = spec["analysis"]
            operations.append(tool + ["analyze-project", project, analysis["driver"], "--", *analysis["arguments"]])
        trace = spec["trace"]
        operations.append(tool + ["trace-project", project, trace["driver"], "--", *trace["arguments"]])
    else:
        inspection = spec["inspection"]
        operations.append(tool + ["find-project-symbols", project, inspection["path"], *inspection["symbols"]])
    return (
        f"Live permission smoke test for {role}. This is the entire authorized task.\n"
        "Do not select, prepare, start, review, archive, or commit a pass. Ignore saved handoff state.\n"
        "Keep the launcher's permission mode unchanged. Do not add grants, switch modes, or rewrite "
        "commands after a refusal. Report a refusal and stop. For Codex trace-project/analyze-project, request sandbox "
        "escalation on the exact command; the installed rule should cover it.\n"
        "Run these standalone commands in order (repeated operations check grant reuse). Stop at the first "
        "failed command or refused scenario; do not continue the list:\n\n"
        + "\n\n".join("```sh\n" + shlex.join(argv) + "\n```" for argv in [tool + ["checkout-status"], *operations, *operations])
        + "\n\nReport each exit status and the inspection matches or each capture's acceptance and artifact path. "
        "A successful launch or help output is not a completed capture. Report approval requests, "
        "observed prompts, permission mode and any operator intervention separately; say unknown "
        "when the harness does not expose whether a human approved. End with SMOKE_COMMANDS_PASSED "
        "only when all commands and scenario acceptance succeeded. Then STOP. "
        "This marker does not certify absence of human intervention; the operator must check the "
        "session and tool logs. No semantic pass starts after this test."
    )
