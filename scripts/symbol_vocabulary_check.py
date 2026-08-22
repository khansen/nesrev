#!/usr/bin/env python3
"""Advisory report on noun phrases that dominate the symbol table without
appearing in the terminology crosswalk.

The stale-placeholder audit looks for address- and ordinal-coded names
(`State03`, `Page0600`, `AddrC000`). It cannot see the other species of
placeholder: a plausible-sounding generic noun phrase that satisfies every
naming rule while identifying nothing. A phrase of that shape contains no
digits and no address, reads as a semantic name, and passes every regex — but
if it heads two hundred symbols and matches no reference-document term, the
project has invented private vocabulary for a concept it has not identified.

That is mechanically detectable: rank multi-word noun phrases by how many
distinct symbols they head, then subtract anything the crosswalk already
accounts for. What remains is a candidate list for an identity pass, not a
defect list — some projects legitimately name structures the manual never
mentions.

Exit status is always 0.
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import defaultdict
from pathlib import Path

# A crosswalk this well mapped is evidence the project names what the
# reference material names, so a partial match is probably a real subsystem.
WELL_MAPPED_RATIO = 0.5


def crosswalk_mapped_ratio(path: Path) -> float:
    """Fraction of crosswalk rows carrying a real asm symbol."""
    total = mapped = 0
    in_table = False
    for raw in _read_lines(path):
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
    return mapped / total if total else 0.0


def _read_lines(path: Path) -> list[str]:
    try:
        return path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeDecodeError):
        return []


LABEL_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*):")
UNRESOLVED_RE = re.compile(r"^L[0-9A-F]{4,5}$")
CAMEL_RE = re.compile(r"[A-Z]+(?=[A-Z][a-z])|[A-Z][a-z0-9]*|[a-z0-9]+")

# Leading verbs describe the action, not the subject; the subject is what we
# are testing for identity.
VERBS = {
    "init", "update", "render", "run", "handle", "resolve", "queue", "set",
    "check", "advance", "clear", "load", "write", "read", "get", "apply",
    "copy", "build", "draw", "start", "tick", "try", "select", "dispatch",
    "reset", "return", "compute", "prepare", "seed", "arm", "commit", "abort",
    "accept", "adjust", "append", "classify", "clamp", "cycle", "enter",
    "exit", "find", "flush", "hide", "latch", "move", "name", "open", "pick",
    "poll", "push", "pop", "restore", "save", "scan", "send", "show", "skip",
    "split", "step", "stop", "store", "switch", "take", "test", "toggle",
    "wait", "walk", "process", "refresh", "promote", "emit", "make", "add",
    "sub", "negate", "choose", "assign", "count", "mark", "trigger", "spawn",
}
# Connectors carry no subject information.
CONNECTORS = {
    "by", "from", "and", "to", "for", "with", "of", "in", "on", "at", "or",
    "then", "the", "a", "an", "into", "per", "via", "as", "if", "not",
}


def words(symbol: str) -> list[str]:
    return [w.lower() for w in CAMEL_RE.findall(symbol)]


def subject_runs(symbol: str) -> list[list[str]]:
    """Contiguous runs of subject words, with verbs/connectors removed."""
    toks = words(symbol)
    while toks and toks[0] in VERBS:
        toks = toks[1:]
    runs: list[list[str]] = []
    current: list[str] = []
    for t in toks:
        if t in CONNECTORS or t.isdigit():
            if current:
                runs.append(current)
                current = []
            continue
        current.append(t)
    if current:
        runs.append(current)
    return runs


def phrases(symbol: str, max_len: int) -> set[tuple[str, ...]]:
    out: set[tuple[str, ...]] = set()
    for run in subject_runs(symbol):
        for size in range(2, max_len + 1):
            for i in range(len(run) - size + 1):
                out.add(tuple(run[i : i + size]))
    return out


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


def crosswalk_vocabulary(path: Path) -> set[str]:
    vocab: set[str] = set()
    if not path.is_file():
        return vocab
    in_table = False
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not (line.startswith("|") and line.endswith("|")):
            in_table = False
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        if _is_crosswalk_header(cells):
            in_table = True
            continue
        if not in_table or not cells:
            continue
        for token in re.findall(r"[A-Za-z][A-Za-z0-9]*", cells[0]):
            vocab.add(token.lower())
    return vocab


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("asm")
    ap.add_argument("crosswalk", nargs="?", default="")
    ap.add_argument("--min-symbols", type=int, default=40,
                    help="distinct symbols a phrase must head to be reported (default 40)")
    ap.add_argument("--max-phrase-words", type=int, default=3)
    ap.add_argument("--dominant", type=int, default=100,
                    help="symbol count at which a phrase family is reportable (default 100)")
    ap.add_argument("--top", type=int, default=8)
    args = ap.parse_args(argv)

    asm = Path(args.asm)
    if not asm.is_file():
        print(f"error: no such asm file: {asm}", file=sys.stderr)
        return 0

    labels = []
    for raw in asm.read_text(encoding="utf-8", errors="replace").splitlines():
        m = LABEL_RE.match(raw)
        if m and not UNRESOLVED_RE.match(m.group(1)):
            labels.append(m.group(1))

    counts: dict[tuple[str, ...], set[str]] = defaultdict(set)
    for sym in labels:
        for ph in phrases(sym, args.max_phrase_words):
            counts[ph].add(sym)

    vocab = crosswalk_vocabulary(Path(args.crosswalk)) if args.crosswalk else set()

    ranked = sorted(
        ((ph, len(syms)) for ph, syms in counts.items() if len(syms) >= args.min_symbols),
        key=lambda kv: (-kv[1], -len(kv[0])),
    )

    # Suppress a shorter phrase when a longer reported phrase subsumes it at a
    # comparable count, so one family reports once.
    kept: list[tuple[tuple[str, ...], int]] = []
    for ph, n in ranked:
        joined = " ".join(ph)
        if any(joined in " ".join(o) and n <= m * 1.6 for o, m in kept if len(o) > len(ph)):
            continue
        kept.append((ph, n))

    def coverage(ph: tuple[str, ...]) -> str:
        hits = sum(1 for w in ph if w in vocab)
        if not vocab:
            return "no crosswalk"
        if hits == len(ph):
            return "in crosswalk"
        if hits:
            return "partly in crosswalk"
        return "not in crosswalk"

    dominant = [(ph, n) for ph, n in kept if n >= args.dominant]
    if not dominant:
        top = kept[0][1] if kept else 0
        print(
            f"OK: no symbol phrase dominates the vocabulary "
            f"(largest family {top} symbols, threshold {args.dominant})"
        )
        return 0

    # A large family the crosswalk already accounts for is a healthy subsystem
    # name, not private vocabulary. Only unaccounted families are reportable.
    # A project whose crosswalk is largely mapped has demonstrated it names
    # what the reference material names. A partial match there is far more
    # likely to be a real subsystem than private vocabulary, and reporting it
    # anyway is the false positive that trains an operator to scroll past.
    mapped_ratio = crosswalk_mapped_ratio(Path(args.crosswalk)) if args.crosswalk else 0.0
    def reportable(ph: tuple[str, ...]) -> bool:
        cov = coverage(ph)
        if cov == "in crosswalk":
            return False
        if cov == "partly in crosswalk" and mapped_ratio >= WELL_MAPPED_RATIO:
            return False
        return True

    unaccounted = [(ph, n) for ph, n in dominant if reportable(ph)]
    if not unaccounted:
        names = ", ".join(
            f"{''.join(w.capitalize() for w in ph)} ({n})" for ph, n in dominant[: args.top]
        )
        print(f"OK: dominant symbol families are accounted for in the crosswalk: {names}")
        return 0

    print(
        f"warn: {asm}: {len(unaccounted)} noun phrase(s) head {args.dominant}+ symbols "
        "each without a matching crosswalk reference term"
    )
    for ph, n in unaccounted[: args.top]:
        camel = "".join(w.capitalize() for w in ph)
        print(f"warn:   {camel}: {n} symbols ({coverage(ph)})")
    print(
        "warn: a family this large is the project's private name for a concept the "
        "reference material probably names differently — candidate for an identity pass"
    )
    print("warn: see agent_playbook/PASS_WORKFLOW.md#identity-pass")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
