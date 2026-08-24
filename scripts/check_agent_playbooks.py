#!/usr/bin/env python3
"""Validate AGENTS.md and the agent_playbook/ structure.

Permanent structural checks:

- required playbook files exist and are non-empty
- each playbook has an Ownership section
- anchored playbook `##` sections have body text, or an explicit redirect link
- the Mandatory Routing Table parses, every entry references a real
  playbook, and the expected task set is covered
- every internal markdown link resolves (file + anchor)
- no malformed markdown links (missing closing paren on the same line)
- no stale numbered references to AGENTS.md (`AGENTS.md §N`,
  `AGENTS.md:LINE`, etc.) sneak into operational files
- required root anchors stay present (so external links survive)
- root file stays within its line/word ceiling
- per-route bundles stay within their context budgets
- obsolete architecture labels ("Work Order (Strict Sequence)" in
  AGENTS.md and "Phase A".."Phase D" in AGENTS.md, PASS_WORKFLOW.md,
  and DATA_RECOVERY.md) do not reappear in the corridor-model files

Run via `make check-agent-playbooks` or directly:

    python3 scripts/check_agent_playbooks.py
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
ROOT = REPO / "AGENTS.md"
PLAYBOOK_DIR = REPO / "agent_playbook"

REQUIRED_PLAYBOOKS = [
    "NEW_PROJECT.md",
    "PASS_WORKFLOW.md",
    "ASM_STYLE.md",
    "DATA_RECOVERY.md",
    "DOCUMENTATION.md",
    "QUALITY_REVIEW.md",
    "REVIEW_AUDITS.md",
    "TOOLING.md",
]

EXPECTED_ROUTING_TASKS = [
    "Start a new project",
    "Resume or perform a semantic pass",
    "Recover hidden code or dispatch",
    "Reformat or interpret data tables/streams",
    "Symbolize RAM/ZP or state machines",
    "Constantize magic numbers, offsets, bounds, or hardware masks",
    "Review or rewrite comments/docs",
    "Assess gold-standard maturity",
    "Run a project-level review audit",
    "Review a committed project pass",
    "Change NESrev, xasm, wrappers, or quality gates",
    "Create or review a mod",
    "Audit for dead code, latent bugs, or micro-optimizations",
]

# Anchors that must stay present at AGENTS.md root because external
# documentation, memory, project scripts, and other repositories link to
# them. This is the complete manifest of published contact points: drop or
# rename any of these and you break inbound references; add one when a new
# root section's anchor becomes a stable contact point.
REQUIRED_ROOT_ANCHORS = [
    "batching-strategy",
    "bit-skip-overlay-cleanup",
    "blob-decode-kpi-pre-assessment",
    "canonical-artifacts",
    "common-nes-ppu-packet-stream-pattern",
    "confidence-protocol",
    "core-naming",
    "executable-rom-to-ram-image-recovery",
    "guiding-pass-philosophy",
    "high-value-pass-contract",
    "intermediate-artifacts",
    "literal-base-readability-rule",
    "mandatory-routing-table",
    "mission",
    "nesrev-code-pointer-recovery-pass",
    "nesrev-intake-sanity-gate",
    "output-philosophy",
    "phase-exit-checklist",
    "prior-project-reuse-gate",
    "readability-self-audit",
    "reviewer-simulation-checklist",
    "safety-rules",
    "session-orientation",
    "specialized-rule-index",
    "work-order",
]

ROOT_LINE_CEILING = 800
ROOT_WORD_CEILING = 6000

# Route budgets are sized for the actual playbook bundle sizes plus the root
# context, with modest headroom (~50 lines, ~100-150 words) so minor edits don't
# immediately re-trigger warnings. Bundles that include NEW_PROJECT.md carry
# project-bootstrap material and are intentionally larger.
#
# The word ceilings were recalibrated when the candidate-evidence /
# corridor-objective governance content was added to AGENTS.md and
# PASS_WORKFLOW.md (advisory `project-next-pass`, operator-selected corridor
# objective, pass-versus-commit, low-yield strategy checkpoint). Later process
# improvements added runtime-trace templates, trace-helper ROM policy,
# relocatable trace-mod guidance, inline dispatch naming, and CPU vector naming.
# Static-readability hardening later added mandatory NOP/padding, packed-flag,
# and redundant-sequence audit dispositions before static-exhaustion claims.
# The pointer-table relocation gate later added the ASM_STYLE naming/symbolic-body
# rule (present on the data-recovery and new-project bundles), which is why those
# two word ceilings carry a little more headroom than the pre-gate baseline. The
# gold-standard/default routes were relieved instead by splitting the review
# playbook: QUALITY_REVIEW.md now holds only the review criteria and the audit
# procedures moved to REVIEW_AUDITS.md, so the default ceiling returns to baseline.
# The new-project route also carries the opaque data/blob internal-structure
# rule because intake and early passes must not treat a referenced blob as
# structurally disposed without inspecting its consumers and interior fields.
# Core data-format coverage later made audio/music/SFX documentation and
# level/object/enemy/item/graphics format disposition explicit maturity
# requirements. That prose intentionally lives in DOCUMENTATION.md,
# QUALITY_REVIEW.md, and REVIEW_AUDITS.md, so the documentation-heavy route
# ceilings carry additional headroom rather than compressing the rule into
# ambiguous shorthand.
# These ceilings preserve the documented modest headroom over measured sizes
# rather than shaving required governance prose.
# The new-project line ceiling was raised from 3625 to 3650 when the masked /
# fixed-count data-extent-assertion trigger prose was added to QUALITY_REVIEW.md
# and PASS_WORKFLOW.md; 3650 restores roughly the same ~0.6% headroom the word
# ceiling already carries over the measured bundle, rather than compressing that
# governance rule into shorthand.
# Per-blob data-format dispositions added a small amount of TOOLING,
# DOCUMENTATION, QUALITY_REVIEW, REVIEW_AUDITS, and PASS_WORKFLOW prose. The
# affected route ceilings keep that rule explicit: data labels are not mature
# merely because their names are documented; opaque spans need consumer,
# pointer-search, extent, and reflow evidence.
# The data-recovery line ceiling was raised from 2470 to 2560 when the
# Static-Analysis Scanner section (the static_analysis.py dead-code / latent-bug /
# micro-optimization tool and its make wrapper) was documented in full in
# TOOLING.md, and the new-project ceilings from 3650/26650 to 3660/26720 for the
# matching root routing row ("Audit for dead code, latent bugs, or
# micro-optimizations"). The tool documents a novel CFG+liveness analysis and its
# finding categories; the ceilings carry that prose at readable length with the
# same modest headroom the other ceilings hold, rather than compressing it.
# The default ceiling was raised from 2650/19100 to 2700/19260 when the
# Static-Analysis Scanner section documented the per-finding `annotated` flag and
# the report's Source-annotation status / worklist block (which findings still
# need a source comment). This keeps that governance prose explicit rather than
# compressing it, at the same modest headroom the other ceilings hold.
# The data-recovery ceiling was raised from 2560/19000 to 2585/19140 when the
# scanner section was corrected: the annotation flag is checked only on a
# finding's flagged instruction (not context lines), the report describes the
# observable ("has an inline comment") rather than overclaiming, and the fixed-
# bit-7 register set was documented as distinct from the side-effect-read set.
# The static-analysis tail-call category later added a listing-backed source-
# annotation worklist for `JSR target` / `RTS` shapes. The default and
# data-recovery word ceilings were raised narrowly to preserve that distinction
# between parity-kept annotation and non-parity rewrites without shortening the
# scanner contract into ambiguous shorthand.
# Orientation-sensitive naming later added an explicit ASM_STYLE confidence rule
# for axes, byte order, row/column, direction, class/zone, and field order, plus
# a root reviewer-checklist pointer. The affected route ceilings were raised to
# keep the defining-evidence examples readable instead of compressing a subtle
# semantic-safety rule.
# Mechanical pass-start hardening later made `project-next-pass` the normal
# operator entry point, kept `project-pass-prep` as an explicit cache/debug
# helper, and documented that `project-pass-start` rejects missing or stale
# `next_pass.json` instead of silently choosing from old evidence. The word
# ceilings carry that sequencing rule at readable length with the same modest
# measured-plus-headroom convention.
# PASS_WORKFLOW.md later gained two worked end-to-end pass examples: a
# rename-only label pass and a raw-RAM symbol pass. Those examples intentionally
# spell out commands, ledger rows, verification, closeout, and staged artifacts
# so new operators can follow the process mechanically.
# Declaration-symbol review later made non-obvious symbol comments and related
# symbol-family grouping explicit across QUALITY_REVIEW.md, DOCUMENTATION.md,
# and ASM_STYLE.md. The default-budgeted mod route and the new-project route
# cross their previous word ceilings because they include the affected playbook
# bundles, so their ceilings preserve readable rule text instead of compressing
# a review criterion into shorthand.
# Executable ROM-to-RAM image recovery later added a mandatory fresh-intake
# smell check, source/destination translation formula, iterative intra-image
# rescan rule, operand-parity trap, `codeentries.txt` representation rule,
# warning-baseline rationale, and root specialized-index entry. The root index
# affects every default route, so these ceilings preserve measured-plus-headroom
# instead of compressing the recovery rule into shorthand.
# Hidden-code intake hardening later connected auto-seeded unused-symbol warning
# rows to orphan-opcode recovery, documented the disposition/rescan loop, and
# spelled out the MMC1 inline-call bank-context failure plus direct `bank|addr`
# codeentries recovery path. The affected ceilings keep that rule readable with
# the same measured-plus-headroom convention.
# Orphan-opcode scanner promotion later added the project-hidden-code-scan
# wrapper and advisory output semantics to the default/hidden-code routes. The
# recalculated ceilings keep measured-plus-headroom across bundled routes
# instead of compressing the false-positive cautions that keep the scanner from
# becoming a misleading gate.
# Control-flow target validation later documented the scanner's per-bank
# resolution rule, the yes/no/unknown contract, and the four validation columns.
# That distinction is what keeps a copied byte run from reading as recovered
# code, so the affected ceilings carry it at measured-plus-headroom instead of
# compressing it into shorthand.
# The cross-corridor identity pass and the two vocabulary-drift detectors added
# a genuinely new pass shape plus its tooling entry, not more prose about
# existing rules. Corridor passes cannot justify identity naming from local
# evidence, so without a named shape for it the deferral repeats indefinitely;
# compressing that into shorthand is what produced the gap. The section was cut
# twice before recalibrating, and the three affected ceilings now carry it at
# measured-plus-headroom.
# Proof-debt signals and deferral capture added the operator-facing half of
# the same work: the detectors are useless if the contract for dismissing and
# for capturing a deferral is not written down where the operator reads it.
# Raised again rather than compressing the prose further. Squeezing rules into
# telegraphese to fit a ceiling trades a measurable number for an unmeasurable
# loss, and the earlier round had already cost one paragraph its antecedent.
# PASS_WORKFLOW.md and TOOLING.md are now the two largest playbooks by a wide
# Raised again for the REWORK_ITEMS and DEFERRALS wrapper arguments, which are
# operator-facing inputs: an argument nobody can find is an argument nobody
# uses, and both exist to replace something the tool used to decide silently.
# margin; if they keep growing, the answer is splitting an ownership cluster
# into its own file per README.md#adding-a-playbook, not further compression.
# Project-pass review packet generation later added TOOLING prose for the
# external review handoff packet. The default route carries TOOLING, so the
# ceiling preserves the same measured-plus-headroom convention.
# Agent-review handoff later added the local worker-loop contract beside the
# packet workflow in TOOLING.md. The hidden-code and default routes carry that
# tooling prose, so their ceilings preserve measured-plus-headroom rather than
# shortening the operator-facing command sequence.
# Review-artifact archiving later added the durable-versus-regenerable split
# for worker-loop artifacts. The additional TOOLING prose keeps review verdicts
# and implementer responses from being lost while leaving packet bodies ignored.
# The tmux notifier later made the first concrete transport explicit: pane
# discovery, role target variables, watcher commands, and the idle-at-prompt
# safety boundary. Those commands are operator-facing; shortening them would
# reintroduce the copy/paste ambiguity the transport exists to remove.
# Committed project-pass review later gained its own routing row so reviewer
# prompts can point at AGENTS.md instead of carrying a duplicate playbook bundle.
# That route intentionally combines review procedures, review criteria, pass
# mechanics, ASM naming/style, and packet/gate/handoff tooling; the ceiling
# preserves measured-plus-headroom for that review surface.
ROUTE_BUDGETS = {
    "default": (3225, 23040),
    "data-recovery": (2965, 21870),
    "new-project": (4050, 29400),
    "project-pass-review": (4170, 29050),
}

DATA_RECOVERY_ROUTE_KEY = "DATA_RECOVERY.md"
NEW_PROJECT_ROUTE_KEY = "NEW_PROJECT.md"
PROJECT_PASS_REVIEW_TASK = "Review a committed project pass"

STALE_REF_PATTERNS = [
    re.compile(r"AGENTS\.md[\\`'\"\s]{0,4}§"),
    re.compile(r"AGENTS\.md:\d"),
    re.compile(r"AGENTS\.md\s+line\s+\d"),
    re.compile(r"AGENTS\.md\s+sections?\s+\d", re.IGNORECASE),
]

STALE_REF_GLOBS = ["*.md", "*.sh", "*.py", "*.txt"]

# Architecture labels that conflict with the corridor model. The
# canonical homes are AGENTS.md#work-order (Corridor Execution Contract)
# and PASS_WORKFLOW.md#project-maturity-dimensions; use those anchors
# instead of these labels in the files listed below.
OBSOLETE_WORK_ORDER_HEADING = "Work Order (Strict Sequence)"
OBSOLETE_PHASE_LABEL_RE = re.compile(r"\bPhase [A-D]\b")
OBSOLETE_PHASE_FILES = [
    "AGENTS.md",
    "agent_playbook/PASS_WORKFLOW.md",
    "agent_playbook/DATA_RECOVERY.md",
]

ANCHOR_RE = re.compile(r'<a\s+id="([^"]+)"\s*></a>')
# Both URL and fragment parts may be empty. We catch the genuinely
# malformed cases (`[text]()`, `[text](#)`) explicitly in
# check_links_and_anchors so we can fail with a clear message instead of
# the regex silently rejecting them.
LINK_RE = re.compile(r"\[[^\]]+\]\(([^)#]*)(?:#([^)]*))?\)")
# Catches `[text](url` with no closing paren on the same line. Negative
# lookahead requires no `)` before the next `[`, line end, or paragraph break.
MALFORMED_LINK_RE = re.compile(r"\[[^\]]+\]\([^)\n]{1,200}$", re.MULTILINE)
CODE_SPAN_RE = re.compile(r"`[^`\n]*`")
FENCED_CODE_RE = re.compile(r"```.*?```", re.DOTALL)
ROUTING_HEADER_RE = re.compile(r"^\|\s*Task\s*\|\s*Mandatory playbooks\s*\|", re.IGNORECASE)


def fail(errors: list[str], msg: str) -> None:
    errors.append(msg)


def warn(warnings: list[str], msg: str) -> None:
    warnings.append(msg)


def strip_code(text: str) -> str:
    text = FENCED_CODE_RE.sub("", text)
    text = CODE_SPAN_RE.sub("", text)
    return text


def file_stats(path: Path) -> tuple[int, int]:
    text = path.read_text(encoding="utf-8")
    lines = text.count("\n") + (0 if text.endswith("\n") else 1)
    words = len(text.split())
    return lines, words


def check_playbook_files(errors: list[str]) -> None:
    for name in REQUIRED_PLAYBOOKS:
        path = PLAYBOOK_DIR / name
        if not path.is_file():
            fail(errors, f"missing playbook: agent_playbook/{name}")
            continue
        text = path.read_text(encoding="utf-8")
        if len(text.strip()) < 200:
            fail(errors, f"playbook agent_playbook/{name} looks empty ({len(text)} bytes)")
        if not re.search(r"^## Ownership\b", text, re.MULTILINE):
            fail(errors, f"playbook agent_playbook/{name} is missing an `## Ownership` section")


def check_links_and_anchors(errors: list[str]) -> None:
    files = [ROOT] + sorted(PLAYBOOK_DIR.glob("*.md"))
    anchors_by_file: dict[Path, set[str]] = {}
    for path in files:
        # Strip fenced and inline code before scanning for anchors so example
        # `<a id="..."></a>` snippets inside backticks don't get treated as
        # real anchors (and don't trigger duplicate-anchor failures).
        stripped = strip_code(path.read_text(encoding="utf-8"))
        ids = ANCHOR_RE.findall(stripped)
        seen: dict[str, int] = {}
        for aid in ids:
            seen[aid] = seen.get(aid, 0) + 1
        for aid, count in sorted(seen.items()):
            if count > 1:
                fail(
                    errors,
                    f"{path.relative_to(REPO)}: duplicate anchor id={aid!r} appears "
                    f"{count} times; inbound links to #{aid} would be ambiguous",
                )
        anchors_by_file[path] = set(ids)

    for path in files:
        text = path.read_text(encoding="utf-8")
        stripped = strip_code(text)

        # Malformed links (missing closing paren on the same line)
        for m in MALFORMED_LINK_RE.finditer(stripped):
            line_no = stripped[:m.start()].count("\n") + 1
            fail(errors, f"{path.relative_to(REPO)}:{line_no}: malformed link missing closing paren")

        for m in LINK_RE.finditer(stripped):
            target, anchor = m.group(1), m.group(2)
            line_no = stripped[:m.start()].count("\n") + 1
            if target.startswith(("http://", "https://", "mailto:")):
                continue
            # `[text](#)` (empty fragment) and `[text]()` (no target, no
            # fragment) are both malformed — fail with a specific message so
            # the reader can fix the right thing.
            if anchor is not None and anchor == "":
                fail(
                    errors,
                    f"{path.relative_to(REPO)}:{line_no}: link has empty fragment "
                    f"(`#` with no anchor name)",
                )
                continue
            if not target and not anchor:
                fail(errors, f"{path.relative_to(REPO)}:{line_no}: empty link target")
                continue
            if not target:
                # Same-file anchor link: `[text](#anchor)`.
                target_path = path
            else:
                target_path = (path.parent / target).resolve()
                # Skip targets that intentionally point outside the
                # validated tree (project READMEs, generated assets, etc.).
                try:
                    target_path.relative_to(REPO)
                except ValueError:
                    continue
            if not target_path.exists():
                fail(errors, f"{path.relative_to(REPO)}:{line_no}: broken link target {target!r}")
                continue
            if anchor and target_path.is_file():
                if target_path not in anchors_by_file:
                    anchors_by_file[target_path] = set(ANCHOR_RE.findall(target_path.read_text(encoding="utf-8")))
                if anchor not in anchors_by_file[target_path]:
                    fail(
                        errors,
                        f"{path.relative_to(REPO)}:{line_no}: link to {target}#{anchor} but anchor not found in {target_path.relative_to(REPO)}",
                    )


def check_anchored_playbook_sections_have_body(errors: list[str]) -> None:
    for path in sorted(PLAYBOOK_DIR.glob("*.md")):
        lines = path.read_text(encoding="utf-8").splitlines()
        i = 0
        while i < len(lines):
            if ANCHOR_RE.fullmatch(lines[i].strip()) is None:
                i += 1
                continue

            heading_idx = i + 1
            while heading_idx < len(lines) and not lines[heading_idx].strip():
                heading_idx += 1
            if heading_idx >= len(lines) or not lines[heading_idx].startswith("## "):
                i += 1
                continue

            body_start = heading_idx + 1
            body_end = body_start
            while body_end < len(lines):
                stripped = lines[body_end].strip()
                if ANCHOR_RE.fullmatch(stripped) is not None:
                    break
                if lines[body_end].startswith("## "):
                    break
                body_end += 1

            body = [
                line.strip()
                for line in lines[body_start:body_end]
                if line.strip() and ANCHOR_RE.fullmatch(line.strip()) is None
            ]
            if not body:
                fail(
                    errors,
                    f"{path.relative_to(REPO)}:{i + 1}: anchored section "
                    f"{lines[heading_idx].strip()!r} has no body",
                )
            i = body_end


def check_routing_table(errors: list[str], warnings: list[str]) -> list[tuple[str, list[str]]]:
    text = ROOT.read_text(encoding="utf-8")
    lines = text.splitlines()
    start = None
    for i, line in enumerate(lines):
        if ROUTING_HEADER_RE.match(line):
            start = i
            break
    if start is None:
        fail(errors, "AGENTS.md is missing the Mandatory Routing Table header")
        return []

    rows: list[tuple[str, list[str]]] = []
    seen_tasks: set[str] = set()
    for line in lines[start + 2:]:
        if not line.startswith("|"):
            break
        parts = [c.strip() for c in line.strip("|").split("|")]
        if len(parts) < 2:
            continue
        task = parts[0]
        playbooks = [p.strip(" `") for p in parts[1].split(",") if p.strip()]
        if not task:
            fail(errors, "routing table has a row with an empty task name")
            continue
        if task in seen_tasks:
            fail(errors, f"routing table has duplicate task row: {task!r}")
        seen_tasks.add(task)
        if not playbooks:
            fail(errors, f"routing row {task!r}: empty playbook bundle")
        rows.append((task, playbooks))

    tasks = {task for task, _ in rows}
    for expected in EXPECTED_ROUTING_TASKS:
        if expected not in tasks:
            fail(errors, f"routing table missing expected task row: {expected!r}")
    extras = tasks - set(EXPECTED_ROUTING_TASKS)
    for extra in sorted(extras):
        warn(warnings, f"routing table has unexpected task row: {extra!r}")

    for task, playbooks in rows:
        for pb in playbooks:
            if pb not in REQUIRED_PLAYBOOKS:
                fail(errors, f"routing row {task!r}: unknown playbook {pb!r}")

    return rows


def check_stale_refs(warnings_list: list[str]) -> None:
    seen: set[tuple[str, int, str]] = set()
    for pattern in STALE_REF_GLOBS:
        for path in REPO.rglob(pattern):
            try:
                rel = path.relative_to(REPO)
            except ValueError:
                continue
            # Skip the validator itself (it documents the patterns) and any
            # tooling tree that legitimately mentions deprecated forms.
            if rel.parts[0] in {".git", "node_modules", "build", "dist"}:
                continue
            try:
                text = path.read_text(encoding="utf-8")
            except (UnicodeDecodeError, OSError):
                continue
            if path == Path(__file__):
                continue
            for pat in STALE_REF_PATTERNS:
                for m in pat.finditer(text):
                    key = (str(rel), m.start(), pat.pattern)
                    if key in seen:
                        continue
                    seen.add(key)
                    warn(
                        warnings_list,
                        f"{rel}: contains stale AGENTS.md reference ({pat.pattern})",
                    )


def check_root_budget(warnings: list[str]) -> tuple[int, int]:
    lines, words = file_stats(ROOT)
    if lines > ROOT_LINE_CEILING:
        warn(warnings, f"AGENTS.md is {lines} lines, over ceiling {ROOT_LINE_CEILING}")
    if words > ROOT_WORD_CEILING:
        warn(warnings, f"AGENTS.md is {words} words, over ceiling {ROOT_WORD_CEILING}")
    return lines, words


def check_route_budgets(rows: list[tuple[str, list[str]]], root_stats: tuple[int, int], warnings: list[str]) -> None:
    if not rows:
        return
    root_lines, root_words = root_stats
    for task, playbooks in rows:
        total_lines, total_words = root_lines, root_words
        for pb in playbooks:
            path = PLAYBOOK_DIR / pb
            if not path.is_file():
                continue
            pl, pw = file_stats(path)
            total_lines += pl
            total_words += pw
        if task == PROJECT_PASS_REVIEW_TASK:
            budget_key = "project-pass-review"
        elif NEW_PROJECT_ROUTE_KEY in playbooks:
            budget_key = "new-project"
        elif DATA_RECOVERY_ROUTE_KEY in playbooks:
            budget_key = "data-recovery"
        else:
            budget_key = "default"
        max_lines, max_words = ROUTE_BUDGETS[budget_key]
        if total_lines > max_lines or total_words > max_words:
            warn(
                warnings,
                f"route '{task}': {total_lines}L/{total_words}W exceeds budget "
                f"{max_lines}L/{max_words}W",
            )


def check_required_root_anchors(errors: list[str]) -> None:
    text = ROOT.read_text(encoding="utf-8")
    anchors = set(ANCHOR_RE.findall(text))
    for required in REQUIRED_ROOT_ANCHORS:
        if required not in anchors:
            fail(errors, f"AGENTS.md missing required root anchor #{required}")


def check_obsolete_architecture_labels(errors: list[str]) -> None:
    root_text = ROOT.read_text(encoding="utf-8")
    if OBSOLETE_WORK_ORDER_HEADING in root_text:
        for i, line in enumerate(root_text.splitlines(), start=1):
            if OBSOLETE_WORK_ORDER_HEADING in line:
                fail(
                    errors,
                    f"AGENTS.md:{i}: obsolete heading {OBSOLETE_WORK_ORDER_HEADING!r} "
                    f"(replaced by Corridor Execution Contract at #work-order)",
                )

    for rel in OBSOLETE_PHASE_FILES:
        path = REPO / rel
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        for i, line in enumerate(text.splitlines(), start=1):
            for m in OBSOLETE_PHASE_LABEL_RE.finditer(line):
                fail(
                    errors,
                    f"{rel}:{i}: obsolete architecture label {m.group(0)!r} "
                    f"(replaced by project-maturity dimensions at "
                    f"PASS_WORKFLOW.md#project-maturity-dimensions)",
                )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Treat warnings as failures (exit 2 when any warning fires).",
    )
    args = parser.parse_args()

    errors: list[str] = []
    warnings: list[str] = []

    check_playbook_files(errors)
    check_links_and_anchors(errors)
    check_anchored_playbook_sections_have_body(errors)
    rows = check_routing_table(errors, warnings)
    check_stale_refs(warnings)
    root_stats = check_root_budget(warnings)
    check_route_budgets(rows, root_stats, warnings)
    check_required_root_anchors(errors)
    check_obsolete_architecture_labels(errors)

    for w in warnings:
        print(f"WARN: {w}")
    for e in errors:
        print(f"FAIL: {e}", file=sys.stderr)

    if errors:
        print(f"\n{len(errors)} failure(s), {len(warnings)} warning(s)", file=sys.stderr)
        return 1
    if args.strict and warnings:
        print(f"\nstrict mode: {len(warnings)} warning(s) escalated to failure", file=sys.stderr)
        return 2
    print(f"\nOK ({len(warnings)} warning(s))")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
