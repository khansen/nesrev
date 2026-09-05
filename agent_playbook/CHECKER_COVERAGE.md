# Declaration Checker Coverage

These checks validate explicit source annotations, not all game data or
semantic ownership. A successful exit does not prove skipped content correct.

## Consumer annotations

`scripts/used_by_xref_check.py` reads full-line `; Used by:` comments attached
to global label or equate declarations. It accepts bare or singly backticked
consumer identifiers beginning with an uppercase letter or underscore,
comma/`and` lists, and `via`/`through` qualifiers.
Only the first sentence is interpreted. General prose, unsupported syntax,
and unattached annotations appear as `NOT CHECKED`; `Consumer:` annotations
and inline instruction comments are outside this check's scope.

The coverage summary counts:

- `annotations`: discovered `Used by:` comments, including empty/unattached ones;
- `parsed_annotations`: comments with at least one concrete consumer;
- `checked_annotations`: comments reaching xref ownership validation;
- `skipped_annotations`: discovered minus checked;
- `partial_annotations`: checked comments with unsupported fragments;
- `parsed_consumers`: concrete consumers, deduplicated within each comment.

Checked counts mean validation attempted, not ownership proved. Missing or
unresolved consumer symbols fail even when a dispatch qualifier cannot be
resolved. Unproved edges involving concrete producers and owner mismatches
remain advisory by default and hard under `--strict`; unsupported syntax and
qualifiers without a concrete known producer stay uncovered in either mode.
Existing symbolic pointer-table proofs use xref-v2
edges, not guessed source relationships. A zero-check run never reports
annotation synchronization.

## PPU packet line layout

`scripts/ppu_packet_line_check.py` discovers `Format:` declarations mentioning
PPU packets without requiring a substring in the label. It checks single
canonical `zero-terminated PPU ... packet` declarations against the
[packet layout contract](DATA_RECOVERY.md#ppu-packet-streams).

`format_candidates` counts discovered PPU packet format declarations;
`checked_streams` counts supported declarations examined, and `skipped_formats`
counts the rest. `declared_streams` retains its earlier meaning of supported
canonical declarations and equals `checked_streams`. Counts are declarations,
not inferred numbers of streams inside grouped data. Address-high flags,
grouped declarations (including plural `packet streams` after the canonical
prefix), and other unsupported formats are `NOT CHECKED`.
Unannotated data is outside the scan. The field name `ppu_hi` alone does not
indicate that the format puts control flags in the address byte.

Declared suffix entries share the parent's terminator and can own payload
fields while the parent is checked. Same-address aliases, unannotated or
declaring the same canonical format, and inline `.DB` bodies are accepted.
Each entry retains field ownership established by preceding aliases and parent
streams. A named field explicitly declared inside the current stream can divide
a packet; the fragments must add up to its
header-derived length. An unrelated label cannot supply missing payload or
hide a missing terminator. Checking stops when packet alignment is lost,
avoiding spurious interpretation of payload zeros as stream terminators.

The process wrapper runs this as an advisory scan. Standalone `--strict`
returns 68 for detected layout defects; unsupported formats remain explicit
coverage gaps, not hard failures or silently validated streams.
