#!/usr/bin/env python3
"""Proof-debt signals: transformation work recorded against evidence recorded.

A pass changes the source. The artifacts that say *why* the change is believed
correct — the terminology crosswalk, the semantic-claims ledger, the working
notes — are updated separately, and nothing notices when they stop being
updated. The gap is invisible because every individual pass is defensible: it
is only the ratio, accumulated over many passes, that shows the project is
transforming faster than it is proving.

Every signal here is a ratio rather than a count, so it is silent on a young
project by construction and grows louder on its own as work accumulates. No
per-project threshold tuning.

Every signal can be permanently dismissed by a row in the acknowledgement
ledger (see `load_acknowledgements`), following the pattern already used by
`constant_magic_allowlist.csv` and `WARNING_BASELINE.txt`: a heuristic on a
judgement call cannot be made never-wrong, so disagreement is made cheap and
durable instead. A false positive costs one ledger row, once.

Used by `project-next-pass` (operator signals at the mandated chokepoint) and
`project-maturity-summary` (advisory dashboard).
"""

from __future__ import annotations

import csv
import re
from pathlib import Path

ACK_HEADER = ["signal", "reason", "pass_id"]

# Deferring is normal; deferring systematically with nowhere durable to
# record what would close each gap is not. Calibrated against the corpus:
# projects deferring at or above this rate that keep no notes are the
# outlier shape, not the norm.
DEFERRAL_RATE_THRESHOLD = 0.15
RECENT_WINDOW = 20
RECENT_DEFERRAL_THRESHOLD = 2
RUNTIME_DEFERRAL_THRESHOLD = 5
# Claims belong to gold closeout, so the trigger is the naming phase being
# finished rather than how much naming has happened.
MAX_UNRESOLVED_FOR_CLAIMS = 0
# Genuine ratio thresholds. A trigger that fires only at exactly zero is
# silenced permanently by one row or one empty file — the "rewards existence,
# not currency" defect these signals were built to correct.
MIN_CROSSWALK_MAPPED_RATIO = 0.25
MAX_UNCLOSED_DEFERRAL_RATIO = 0.5

# Filenames that indicate a runtime gap was scheduled rather than parked.
TRACE_DOC_RE = re.compile(r"trace|scenario|runbook|capture", re.IGNORECASE)
RUNTIME_RE = re.compile(
    r"\bdynamic\b|\bruntime\b|\btrace\b|\bcapture\b|\bin.game\b|\bemulator\b",
    re.IGNORECASE,
)

# Phrasing a pass uses when it knowingly leaves a gap behind. Matched against
# the scorecard notes cell only.
DEFERRAL_RE = re.compile(
    r"out of scope|left .{0,40}\bfor later\b|defer(?:red|s)?\b|revisit|"
    r"pending (?:later|stronger|further|runtime)|still (?:needs?|unresolved)",
    re.IGNORECASE,
)


def _read(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return ""


def load_acknowledgements(path: Path) -> set[str]:
    """Signal ids the operator has explicitly dismissed, with a written reason.

    Ledger is CSV with header `signal,reason,pass_id`. A row without a reason
    is ignored: the point of the ledger is the recorded judgement, not the
    silence.
    """
    text = _read(path)
    if not text:
        return set()
    acked: set[str] = set()
    for row in csv.DictReader(text.splitlines()):
        signal = (row.get("signal") or "").strip()
        reason = (row.get("reason") or "").strip()
        if signal and reason:
            acked.add(signal)
    return acked


def scorecard_rows(path: Path) -> list[dict[str, str]]:
    """Parsed scorecard data rows, in file order."""
    rows: list[dict[str, str]] = []
    header: list[str] | None = None
    for raw in _read(path).splitlines():
        line = raw.strip()
        if not (line.startswith("|") and line.endswith("|")):
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        if cells and cells[0] == "pass_id":
            header = cells
            continue
        if header is None or len(cells) != len(header):
            continue
        if not cells[0].isdigit():
            continue
        rows.append(dict(zip(header, cells)))
    return rows


def unresolved_labels(rows: list[dict[str, str]]) -> int | None:
    """Unresolved-label count from the latest scorecard row, if recorded."""
    for r in reversed(rows):
        cell = (r.get("labels_remaining") or "").strip()
        m = re.match(r"(\d+)", cell)
        if m:
            return int(m.group(1))
    return None


def deferral_rows(path: Path) -> list[dict[str, str]]:
    """Rows from the captured-deferral ledger, empty when absent."""
    if not path.is_file():
        return []
    try:
        with path.open(newline="", encoding="utf-8") as fh:
            return [dict(r) for r in csv.DictReader(fh)]
    except (OSError, UnicodeDecodeError):
        return []


def _is_crosswalk_header(cells: list[str]) -> bool:
    """Recognise both crosswalk header spellings.

    The canonical header is `Reference term / aliases | Asm symbol(s) |
    Mapping confidence | Evidence`; thirteen projects predating it use
    `Reference term | Asm symbol(s) | Confidence | Notes`. Matching the
    canonical spelling exactly read every one of those as an empty table,
    which silently disabled the crosswalk signal and the vocabulary check's
    healthy-family suppression on more than half the corpus.
    """
    return (
        len(cells) >= 2
        and cells[0].lower().startswith("reference term")
        and "asm symbol" in cells[1].lower()
    )


def crosswalk_mapped(path: Path) -> tuple[int, int]:
    """(total data rows, rows carrying a real asm symbol)."""
    total = mapped = 0
    in_table = False
    for raw in _read(path).splitlines():
        line = raw.strip()
        if not (line.startswith("|") and line.endswith("|")):
            in_table = False
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        if _is_crosswalk_header(cells):
            in_table = True
            continue
        if not in_table or len(cells) < 3:
            continue
        if set("".join(cells)) <= set("-: "):
            continue
        total += 1
        if cells[1] and cells[2].lower() not in {"reference-only", "unmapped", ""}:
            mapped += 1
    return total, mapped


def semantic_claim_count(path: Path) -> int:
    """Claims recorded, excluding the scaffold template heading."""
    n = 0
    for raw in _read(path).splitlines():
        m = re.match(r"^##\s+Claim:\s*(.+?)\s*$", raw)
        if m and m.group(1) != "semantic-slug":
            n += 1
    return n


def rename_count(path: Path) -> int:
    text = _read(path)
    if not text:
        return 0
    return max(0, len([ln for ln in text.splitlines() if ln.strip()]) - 1)


LABEL_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*):")
UNRESOLVED_LABEL_RE = re.compile(r"^L[0-9A-F]{4,5}$")


def provenance_coverage(
    *, asm: Path, renames: Path, crosswalk: Path, deferrals: Path
) -> list[tuple[str, int, int, str]]:
    """Fraction of the work each authored ledger accounts for.

    The KPI suite measures the assembly; nothing measures whether the evidence
    about the assembly is complete. Every name in a disassembly is invented, so
    a named label with no ledger row is a decision no reviewer can trace — a
    blind spot that a schema-valid ledger hides.

    Derived, never stored: this joins the asm against ledgers that already
    exist. Returns (class, accounted, total, note) rows.
    """
    out: list[tuple[str, int, int, str]] = []

    labels = {
        m.group(1)
        for line in _read(asm).splitlines()
        if (m := LABEL_RE.match(line)) and not UNRESOLVED_LABEL_RE.match(m.group(1))
    }
    reasoned = set()
    if renames.is_file():
        with renames.open(newline="", encoding="utf-8") as fh:
            for row in csv.DictReader(fh):
                if (row.get("new_name") or "").strip() and (row.get("reason") or "").strip():
                    reasoned.add(row["new_name"].strip())
    out.append(("named labels -> rename ledger", len(labels & reasoned), len(labels),
                "names whose reason a reviewer can trace"))

    total_terms, mapped = crosswalk_mapped(crosswalk)
    out.append(("reference terms -> crosswalk", mapped, total_terms,
                "manual vocabulary tied to code"))

    ledger = deferral_rows(deferrals)
    closed = sum(1 for r in ledger if (r.get("revisit_condition") or "").strip())
    out.append(("deferrals -> revisit condition", closed, len(ledger),
                "gaps stating what would close them"))

    return out


def collect(
    *,
    scorecard: Path,
    crosswalk: Path,
    semantic_claims: Path,
    renames: Path,
    working_notes: Path,
    deferrals: Path,
    doc_root: Path,
    acknowledgements: Path,
    min_passes: int = 8,
) -> list[dict[str, str]]:
    """Return proof-debt signals, strongest first.

    A signal fires only when transformation work has accumulated well past the
    point where the corresponding evidence artifact should have moved.
    """
    acked = load_acknowledgements(acknowledgements)
    rows = scorecard_rows(scorecard)
    passes = max((int(r["pass_id"]) for r in rows), default=-1)
    if passes < min_passes:
        return []

    renames_logged = rename_count(renames)
    signals: list[dict[str, str]] = []

    def add(sid: str, text: str, action: str) -> None:
        if sid in acked:
            return
        signals.append({"id": sid, "text": text, "action": action})

    # Naming work with no term ever mapped back to the reference vocabulary.
    total_terms, mapped_terms = crosswalk_mapped(crosswalk)
    mapped_ratio = mapped_terms / total_terms if total_terms else 1.0
    if total_terms and mapped_ratio < MIN_CROSSWALK_MAPPED_RATIO:
        add(
            "crosswalk_unmapped",
            f"{renames_logged} renames logged across {len(rows)} passes, "
            f"but only {mapped_terms} of {total_terms} crosswalk terms "
            f"({mapped_ratio:.0%}) map to code",
            "run an identity pass (PASS_WORKFLOW.md#identity-pass) or record "
            "why these terms have no single code owner",
        )

    # Naming complete with no evidence-backed conclusion ever recorded.
    # Deliberately a completion binary rather than a ratio: gold closeout
    # requires at least one claim, and there is no denominator for how many
    # a project ought to have.
    # Gated on the naming phase being done, not on rename volume: claims are a
    # gold-closeout artifact, and the corpus shows healthy projects record their
    # first one well past the midpoint. A volume trigger fires for hundreds of
    # passes on projects that go on to record claims properly.
    claims = semantic_claim_count(semantic_claims)
    unresolved = unresolved_labels(rows)
    if (
        semantic_claims.exists()
        and claims == 0
        and unresolved is not None
        and unresolved <= MAX_UNRESOLVED_FOR_CLAIMS
    ):
        add(
            "semantic_claims_empty",
            f"semantic naming is complete ({unresolved} unresolved labels after "
            f"{len(rows)} passes), but SEMANTIC_CLAIMS.md records no claims",
            "record a claim for each subsystem whose ownership is settled "
            "(QUALITY_REVIEW.md#semantic-claims)",
        )

    # Deferrals accumulating with nowhere durable to record what would close
    # them. Two shapes: a project predating the deferral ledger, and a ledger
    # whose rows were captured but never given a revisit condition.
    ledger = deferral_rows(deferrals)
    scorecard_deferrals = sum(1 for r in rows if DEFERRAL_RE.search(r.get("notes", "")))
    rate = scorecard_deferrals / len(rows) if rows else 0.0
    recent = sum(
        1 for r in rows[-RECENT_WINDOW:] if DEFERRAL_RE.search(r.get("notes", ""))
    )
    # Two conditions, both required. The rate separates systematic deferral
    # from the ordinary kind every healthy pass does; the recent window proves
    # the debt is live rather than closed history still visible in the log.
    # Corpus check: every project that defers at this rate already keeps notes,
    # so this is the shape of a project deferring with nowhere to put it.
    # No working-notes conjunct: an empty file must not silence a signal about
    # systematic deferral. Once the ledger exists, deferrals_unclosed takes
    # over and measures closure as a ratio.
    if (
        rate >= DEFERRAL_RATE_THRESHOLD
        and recent >= RECENT_DEFERRAL_THRESHOLD
        and not ledger
    ):
        add(
            "deferrals_uncaptured",
            f"{scorecard_deferrals} of {len(rows)} passes recorded a deferral "
            f"({rate:.0%}, {recent} in the last {RECENT_WINDOW}), with no "
            "structured record of what would close them",
            "capture them at closeout so each gap carries a revisit condition "
            "(PASS_WORKFLOW.md#proof-debt)",
        )

    unclosed = [
        r for r in ledger
        if (r.get("status") or "open").strip() == "open"
        and not (r.get("revisit_condition") or "").strip()
    ]
    open_rows = [r for r in ledger if (r.get("status") or "open").strip() == "open"]
    unclosed_ratio = len(unclosed) / len(open_rows) if open_rows else 0.0
    if open_rows and unclosed_ratio > MAX_UNCLOSED_DEFERRAL_RATIO:
        add(
            "deferrals_unclosed",
            f"{len(unclosed)} of {len(open_rows)} open deferrals "
            f"({unclosed_ratio:.0%}) have no revisit condition",
            "state what evidence would close each one in "
            "inventory/deferrals.csv, or mark the row closed",
        )

    # A runtime-gated deferral is a scheduling claim: the classification
    # procedure requires it to become a trace plan naming the expected signal
    # and promotion criteria. Parked instead of scheduled, it is an absorbing
    # state — and it is the most attractive deferral available, because it is
    # unfalsifiable from the desk. Runtime-gated has a narrow definition: the
    # value depends on live input, RNG, timing, scenario, or emulator state.
    # Preferred source is the operator's explicit promotion in the ledger. The
    # fallback reads scorecard prose, which is the same inference capture no
    # longer makes — kept only so a project with no ledger yet is not blind,
    # and the action text leads with re-classification for that reason.
    if ledger:
        # Once a ledger exists it is the whole truth. An `or` here would fall
        # through to the prose scan whenever no row is promoted — so a project
        # capturing everything correctly as static, with no runtime gaps at
        # all, would be warned permanently about prose it has superseded.
        runtime_deferrals = [
            r for r in ledger if (r.get("kind") or "").strip() == "runtime"
        ]
    else:
        runtime_deferrals = [
            r for r in rows if RUNTIME_RE.search(r.get("notes", ""))
            and DEFERRAL_RE.search(r.get("notes", ""))
        ]
    has_trace_doc = any(
        TRACE_DOC_RE.search(f.name) for f in doc_root.glob("*.md")
    ) if doc_root.is_dir() else False
    if len(runtime_deferrals) >= RUNTIME_DEFERRAL_THRESHOLD and not has_trace_doc:
        add(
            "runtime_deferrals_unscheduled",
            f"{len(runtime_deferrals)} deferral(s) are recorded as needing "
            "runtime evidence, but no trace plan exists",
            "author a trace plan naming the expected signal and promotion "
            "criteria, or re-classify: a gap is runtime-gated only when the "
            "value depends on live input, RNG, timing, scenario, or emulator "
            "state (QUALITY_REVIEW.md#static-vs-runtime-gaps)",
        )

    # The repeated-deferral escape rule: re-triaging the same dead end pass
    # after pass is the shape that fossilises a placeholder.
    repeats = {}
    for r in ledger:
        # Keyed on subject: pass focus is unique per pass, so keying on it
        # meant this signal could never fire.
        subject = (r.get("subject") or "").strip()
        if subject and (r.get("status") or "open").strip() == "open":
            repeats[subject] = repeats.get(subject, 0) + 1
    worst = sorted(repeats.items(), key=lambda kv: -kv[1])
    if worst and worst[0][1] >= 3:
        subject, n = worst[0]
        add(
            "deferral_repeat",
            f"'{subject}' has been deferred {n} times without closing",
            "narrow or switch corridors rather than re-triaging the same gap "
            "(PASS_WORKFLOW.md#raw-ram-queue, repeated-deferral escape)",
        )

    return signals


def _cli(argv: list[str]) -> int:
    """Report proof debt for one project's doc root. Always exits 0."""
    import argparse
    import sys

    ap = argparse.ArgumentParser(description="Report proof-debt signals.")
    ap.add_argument("doc_root")
    ap.add_argument("crosswalk")
    ap.add_argument(
        "--coverage",
        action="store_true",
        help="report how much of the work the authored ledgers account for",
    )
    ap.add_argument(
        "--crosswalk-only",
        action="store_true",
        help="report only crosswalk currency (mapped terms against closed passes)",
    )
    args = ap.parse_args(argv)

    if args.coverage:
        doc = Path(args.doc_root)
        asm = next((p for p in (doc.parent.parent / "asm").glob("*.asm")), None)
        if asm is None:
            print("error: no asm found for coverage report", file=sys.stderr)
            return 0
        print("Provenance coverage (work accounted for by the authored ledgers):")
        for name, got, total, note in provenance_coverage(
            asm=asm,
            renames=doc / "inventory/renames.csv",
            crosswalk=Path(args.crosswalk),
            deferrals=doc / "inventory/deferrals.csv",
        ):
            pct = f"{100 * got // total}%" if total else "n/a"
            print(f"- {name}: {got}/{total} ({pct}) — {note}")
        return 0

    if args.crosswalk_only:
        total, mapped = crosswalk_mapped(Path(args.crosswalk))
        passes = max(
            (int(r["pass_id"]) for r in scorecard_rows(Path(args.doc_root) / "PROGRESS_SCORECARD.md")),
            default=-1,
        )
        if not total or passes < 5:
            return 0
        if not mapped:
            print(f"warn: {args.crosswalk}: {total} reference terms, none mapped to code after {passes} passes")
            print("warn: see agent_playbook/DOCUMENTATION.md#terminology-crosswalk")
        else:
            print(f"OK: crosswalk currency {mapped}/{total} terms mapped after {passes} passes")
        return 0

    doc = Path(args.doc_root)
    signals = collect(
        scorecard=doc / "PROGRESS_SCORECARD.md",
        crosswalk=Path(args.crosswalk),
        semantic_claims=doc / "SEMANTIC_CLAIMS.md",
        renames=doc / "inventory/renames.csv",
        working_notes=doc / "WORKING_NOTES.md",
        deferrals=doc / "inventory/deferrals.csv",
        doc_root=doc,
        acknowledgements=doc / "inventory/proof_debt_acknowledged.csv",
    )
    if not signals:
        print("OK: no proof debt (evidence artifacts are keeping pace with the work)")
        return 0
    for s in signals:
        print(f"warn: {s['text']}")
        print(f"warn:   -> {s['action']}")
    return 0


if __name__ == "__main__":
    import sys as _sys

    _sys.exit(_cli(_sys.argv[1:]))
