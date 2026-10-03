#!/usr/bin/env python3
"""Select current authored references without rewriting historical evidence."""
from __future__ import annotations

import re
from pathlib import Path

from process_friction import read_receipts, project_paths
from scorecard_lifecycle_check import read_scorecard


class AuthoredHistory:
    def __init__(self, scorecard: Path, pass_id: int | None = None,
                 *, root: Path, project: str):
        self.scorecard = scorecard.absolute()
        _, rows = read_scorecard(scorecard)
        self.pass_id = max(row[1] for row in rows) if pass_id is None else pass_id
        if self.pass_id not in {row[1] for row in rows}:
            raise ValueError(f"{scorecard}: scorecard pass {self.pass_id} not found")
        self.historical_lines = {line for line, row_pass, _ in rows if row_pass < self.pass_id}
        # Validate before granting the canonical receipt path an exemption.
        read_receipts(root, project)
        _, self.receipts = project_paths(root, project)

    def lines(self, path: Path) -> list[tuple[int, str]]:
        if path.absolute() == self.receipts:
            return []
        omitted = self.historical_lines if path.absolute() == self.scorecard else set()
        return [(number, line) for number, line in
                enumerate(path.read_text(encoding="utf-8").splitlines(), 1)
                if number not in omitted]


SYMBOL_RE = re.compile(r"`(@@?[A-Za-z_][A-Za-z0-9_]*|[A-Za-z_][A-Za-z0-9_]*)`")


def document_symbols(history: AuthoredHistory, paths: list[Path]) -> list[str]:
    """Keep the existing docs-check token policy, selecting only current lines."""
    symbols = set()
    for path in paths:
        for _, line in history.lines(path):
            for symbol in SYMBOL_RE.findall(line):
                if symbol in {"AudioMacroDescNN", "UNK_"}:
                    continue
                if (symbol.startswith("@@")
                        or ("_" in symbol and re.search(r"[A-Z]", symbol))
                        or (re.match(r"[A-Z]", symbol) and len(symbol) >= 5)):
                    symbols.add(symbol)
    return sorted(symbols)
