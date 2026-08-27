#!/usr/bin/env python3
"""Capture a pass's deferrals into a durable ledger at the moment they are made.

A deferral is normally correct: a corridor pass that reaches the edge of its
evidence should stop rather than guess. The failure is not deferring, it is
deferring with no record of what would close the gap, so the next pass to reach
the same edge starts from nothing and defers again. Repeated indefinitely, that
is how a structural placeholder fossilises while every individual pass remains
defensible.

The operator already writes the deferral, in the closeout notes ("left broad
RAM ownership out of scope"). This turns that sentence into a ledger row at the
moment it is written, rather than asking a later audit to reconstruct it from
pass history. `revisit_condition` starts empty and is the operator's to fill:
the proof-debt signal keeps raising it until they do.

The ledger is deliberately not WORKING_NOTES.md. Those notes are curated prose
under a maturity line budget, and appending every deferral would turn them into
the pass log the documentation rules forbid. A CSV ledger also makes repeat
deferrals queryable, which is what the repeated-deferral escape rule needs.

Exit status is 0 unless the ledger cannot be written.
"""

from __future__ import annotations

import argparse
import csv
import re
import sys
from pathlib import Path

HEADER = [
    "pass_id", "corridor", "subject", "kind", "deferral",
    "revisit_condition", "status",
]

# Words that describe the act of deferring, or are too generic to identify
# what was deferred. Removing them leaves the subject.
_STOP = {
    "left", "leave", "leaves", "out", "of", "scope", "the", "a", "an", "and",
    "or", "for", "to", "in", "on", "at", "with", "plus", "later", "further",
    "deferred", "defer", "defers", "revisit", "pending", "still", "needs",
    "need", "unresolved", "broad", "broader", "exact", "stable", "full",
    "remaining", "other", "its", "their", "this", "that", "these", "those",
    "dynamic", "proven", "until", "before", "after", "while", "keeping",
    "kept", "keep", "preserved", "preserve", "preserving", "is", "are", "was",
    "were", "be", "been", "as", "by", "from", "into", "per", "via", "not",
    "no", "any", "all", "some", "more", "most", "well", "yet", "now",
}


def _normalise(word: str) -> str:
    """Crude singularisation so `identities` and `identity` share a key."""
    w = word.lower()
    if w.endswith("ies") and len(w) > 4:
        return w[:-3] + "y"
    if w.endswith("sses") or w.endswith("shes"):
        return w[:-2]
    if w.endswith("s") and not w.endswith("ss") and len(w) > 3:
        return w[:-1]
    return w


def subject_key(sentence: str) -> str:
    """A stable key for what a deferral is about.

    `deferral_repeat` needs to recognise the same gap across passes. Keying on
    the pass focus cannot do that — focus lines are unique per pass, so the
    signal built to break a defer-forever loop could never fire. This keys on
    the deferral sentence instead, reduced to its distinctive nouns.

    Approximate by construction: it will merge some distinct gaps and miss some
    genuine repeats. That is the right trade against a key that never matches.
    """
    words = [
        _normalise(w)
        for w in re.findall(r"[A-Za-z][A-Za-z0-9_]*", sentence)
        if len(w) > 2
    ]
    content = [w for w in words if w not in _STOP]
    # The first distinctive nouns carry the subject; sorting makes the key
    # order-insensitive so clause reordering still matches.
    return "-".join(sorted(dict.fromkeys(content))[:3]) or "unclassified"

# Captured deferrals are always `static`. Inferring `runtime` from words like
# "dynamic" reproduces the exact misclassification the runtime rule exists to
# prevent: an identity or liveness gap described as "dynamic feature-id
# meanings" is desk-resolvable cross-corridor work, and stamping it runtime
# would demand a trace plan for evidence already sitting in the ROM.
#
# Promotion to `runtime` is an explicit operator act (`--kind runtime`, or
# editing the row), which is the point: asserting that evidence cannot be had
# from the desk should cost a deliberate decision, not a word choice.

# One definition of "this sentence describes a deferral", shared with the
# signal that reads the resulting ledger. Two copies of a regex drift exactly
# like two copies of a rule: measured against one real scorecard, the two
# definitions that existed before this consolidation matched 49 rows and 41.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from proof_debt import DEFERRAL_RE  # noqa: E402


# What was deferred, not what was accomplished. A closeout note is mostly a
# list of work done with the gap as a trailing clause, so capturing the whole
# sentence buries the subject under accomplishments and makes the ledger
# unqueryable.
_CLAUSE_RES = [
    re.compile(r"\bleft\s+(.+?)\s+(?:out of scope|for (?:a )?later|for now)\b", re.I),
    re.compile(r"\b(.+?)\s+(?:remains?|stays?|stayed)\s+(?:out of scope|deferred|unresolved)\b", re.I),
    re.compile(r"\bdeferr?(?:ed|ing)\s+(.+?)(?:[.;]|$)", re.I),
    re.compile(r"\b(.+?)\s+(?:still needs?|needs? a later|awaits?)\s+(.+?)(?:[.;]|$)", re.I),
]


def deferral_sentences(notes: str) -> list[str]:
    """The individual gaps a note defers, one string each.

    A single clause routinely defers several things ("left A, B, and C out of
    scope"), and each is a separate gap that a later pass may close
    independently, so the list is split rather than stored whole.
    """
    out: list[str] = []
    for sentence in re.split(r"(?<=[.;])\s+", notes.strip()):
        s = sentence.strip()
        if not s or not DEFERRAL_RE.search(s):
            continue
        clause = None
        for rx in _CLAUSE_RES:
            m = rx.search(s)
            if m:
                clause = m.group(1).strip()
                break
        if clause is None:
            out.append(s.rstrip(".").strip())
            continue
        for item in re.split(r",\s*(?:and\s+)?|\s+and\s+|\s+plus\s+", clause):
            item = item.strip(" .,;")
            if len(item) > 3:
                out.append(item)
    return out


# `subject :: revisit condition [:: kind]`, one per line or separated by `;`.
# `::` is chosen because it does not occur in ordinary closeout prose and
# survives shell quoting without the `$`-expansion hazards recorded in the
# process-friction notes.
def explicit_entries(spec: str) -> list[dict[str, str]]:
    """Parse operator-supplied deferrals, bypassing prose extraction entirely.

    Prose parsing is a fallback, not the contract. When the operator states the
    gap and what would close it directly, nothing has to be inferred from a
    sentence written for a human reader — which removes both the brittleness
    and the incentive to phrase notes for the parser.
    """
    out: list[dict[str, str]] = []
    for raw in re.split(r"[;\n]", spec):
        entry = raw.strip()
        if not entry:
            continue
        parts = [f.strip() for f in entry.split("::")]
        subject = parts[0]
        if not subject:
            continue
        kind = parts[2].lower() if len(parts) > 2 and parts[2] else "static"
        if kind not in ("static", "runtime"):
            # Downgrading a typo to static would silently suppress the
            # trace-plan signal, which is the opposite of what the operator
            # asked for by typing a third field at all.
            raise ValueError(
                f"unknown deferral kind {parts[2]!r} in {entry!r}; "
                "expected 'static' or 'runtime'"
            )
        out.append({
            "deferral": subject,
            "revisit_condition": parts[1] if len(parts) > 1 else "",
            "kind": kind,
        })
    return out


def existing_rows(path: Path) -> list[dict[str, str]]:
    if not path.is_file():
        return []
    with path.open(newline="", encoding="utf-8") as fh:
        return [dict(r) for r in csv.DictReader(fh)]


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("ledger")
    ap.add_argument("--pass-id", required=True)
    ap.add_argument("--corridor", default="")
    ap.add_argument("--notes", default="")
    ap.add_argument(
        "--explicit",
        default="",
        help="operator-stated deferrals as `subject :: revisit condition "
        "[:: static|runtime]`, one per line or `;`-separated; when given, "
        "prose extraction is skipped",
    )
    ap.add_argument(
        "--kind",
        choices=("static", "runtime"),
        default="static",
        help="runtime asserts the evidence cannot be had from the desk; it "
        "obliges a trace plan and must be chosen deliberately",
    )
    args = ap.parse_args(argv)

    if args.explicit:
        try:
            entries = explicit_entries(args.explicit)
        except ValueError as exc:
            print(f"deferral_capture: {exc}", file=sys.stderr)
            return 2
    else:
        entries = [
            {"deferral": s, "revisit_condition": "", "kind": args.kind}
            for s in deferral_sentences(args.notes)
        ]
    if not entries:
        return 0

    ledger = Path(args.ledger)
    rows = existing_rows(ledger)
    # Re-running closeout for the same pass must not duplicate its rows, and
    # editing NOTES between runs must not either — hence the subject key rather
    # than the sentence, which changes when the prose is reworded.
    already: set[tuple[str, str]] = set()
    for row in rows:
        row_pass_id = row.get("pass_id", "")
        subject = row.get("subject", "").strip()
        if subject:
            already.add((row_pass_id, subject))

        # Operators may replace an auto-generated subject with a curated stable
        # key while retaining the human description of the underlying gap. A
        # later closeout rerun must recognise that row instead of recreating the
        # generated key beside it.
        deferral = row.get("deferral", "").strip()
        if deferral:
            already.add((row_pass_id, subject_key(deferral)))

    added = 0
    for entry in entries:
        subject = subject_key(entry["deferral"])
        key = (str(args.pass_id), subject)
        if key in already:
            continue
        rows.append(
            {
                "pass_id": str(args.pass_id),
                "corridor": args.corridor,
                "subject": subject,
                "kind": entry["kind"],
                "deferral": entry["deferral"],
                "revisit_condition": entry["revisit_condition"],
                "status": "open",
            }
        )
        already.add(key)
        added += 1

    if not added:
        return 0

    ledger.parent.mkdir(parents=True, exist_ok=True)
    with ledger.open("w", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=HEADER, lineterminator="\n")
        writer.writeheader()
        for r in rows:
            writer.writerow({k: r.get(k, "") for k in HEADER})

    print(
        f"project-pass-closeout: captured {added} deferral(s) from this pass into "
        f"{ledger}"
    )
    if any(not r.get("revisit_condition") for r in rows if r.get("status") == "open"):
        print(
            "project-pass-closeout: fill in revisit_condition for each — what evidence "
            "would close the gap — so the next pass to reach it does not start from zero"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
