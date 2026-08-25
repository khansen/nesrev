# TOOLING Playbook

This playbook is the canonical home for xasm, NESrev, and project-wrapper tooling — listing/xref options, structured analysis workflow, NESrev regeneration controls, inventory commands, parity-drift diagnostics, the consolidated command reference, exit-code interpretation, and auxiliary-script hygiene. The root `AGENTS.md` keeps only the Mandatory Routing Table entry that names this file.

## Ownership

This playbook owns commands, tool options, and diagnostic procedures:

- xasm listings and xref options
- data-consumer, data-coverage, and index-pattern analysis
- the static-analysis scanner (dead code, latent bugs, micro-optimizations)
- the orphan-opcode hidden-code scanner
- the vocabulary-drift detectors
- NESrev regeneration controls
- inventory commands
- parity-drift diagnostics
- the canonical command reference
- tool exit codes and debugging
- auxiliary-script hygiene

Other playbooks link to exact tooling sections here rather than copying command
blocks. Minimal root lifecycle commands may appear in `AGENTS.md`; every other
command example lives only here.

## Playbook Sections

<a id="xasm-options"></a>
## xasm Listings and Xref Options

The `xasm` assembler provides `--listing=FILE` to map CPU addresses and
emitted hex bytes to source lines. This is the primary tool for diagnosing
binary drift.

**Prefer JSON format** (`--listing-format=json` or `ndjson`) over plaintext
listings. JSON listings are machine-parseable, handle continuation rows as
first-class records, and can be processed with `jq`/Python instead of
fragile text parsing. Reserve plaintext `.lst` for quick human inspection
only.
```sh
# Preferred: machine-readable listing
xasm --pure-binary --listing=Game.lst.json --listing-format=json Game.asm

# Fallback: human-readable plaintext
xasm --pure-binary --listing=Game.lst Game.asm
```

<a id="xasm-structured-analysis"></a>
## xasm Structured Feature Workflow

Use structured `xasm` outputs through the wrapper workflow. Ad-hoc `xasm`
commands are for debugging only.
### Warm-Up and Closeout

```sh
make project-regenerate-asm PROJECT=<slug>
make project-next-pass PROJECT=<slug>
make project-pass-start PROJECT=<slug>
make project-pass-closeout PROJECT=<slug>
```

Optional `KEY=value` arguments (append to the same line):
`project-regenerate-asm` accepts the five hint inputs at
[#nesrev-controls](#nesrev-controls) plus `ALLOW_TRAILING_BYTES=1`
(audited trailer override); `project-pass-start` accepts `PASS=<id>`
and `TARGET=<corridor_anchor_or_notes_plan>`; `project-pass-closeout`
accepts `PASS=<id>`, `VERIFY_MODE=strict|relaxed`, `FOCUS=<text>`,
`NOTES=<text>`, `DEFERRALS=<...>`, and `REWORK_ITEMS=<count>`.
When invoking a newer closeout script from a tool-bearing worktree against a
different project checkout, set `PROJECT_PASS_CLOSEOUT_REPO_ROOT` to the
project checkout so project files resolve there while helpers come from the
tool location.
`project-next-pass` invokes `project-pass-prep` when generated pass cache is
missing or stale; prep output goes to stderr so `FORMAT=json` stays clean.
Run `make project-pass-prep PROJECT=<slug>` directly only for an explicit cache
refresh or tooling debug. The top bucket is not a pass decision;
`project-pass-start` records the operator's selected corridor objective and
rejects missing or stale `next_pass.json`.
Direct `project-pass-prep` runs and closeout refresh the factual columns in
`raw_ram_review.csv`; closeout uses the raw-RAM refresh-only path rather than a
full prep rerun. Ordinary `project-next-pass` is read-only for that tracked
ledger, including its auto-prep path, so a clean closeout commit does not become
dirty just because the next briefing was generated.

### Project-Pass Review Packet

`make project-pass-review-packet PROJECT=<slug> BASE=<base> HEAD=<head>`
emits a Markdown packet for external project-pass review. Run it from a clean
worktree checked out at `HEAD`; the wrapper refuses tracked dirty state or a
different checkout so gate evidence cannot describe the wrong commit. Redirect
stdout to an ignored path or pass `OUT=<packet.md>`. The packet contract lives
in [`PROJECT_PASS_REVIEW_PACKET_SPEC.md`](../PROJECT_PASS_REVIEW_PACKET_SPEC.md).

The packet includes range-level rename and unresolved-label deltas, the
complete `BASE..HEAD` commit list, project diff, authored-ledger deltas,
proof-debt and crosswalk output, `project-next-pass`, and the
verify/process/docs gates, with each command labelled by the exact SHA it
describes. Use `ALLOW_UNRESOLVED_LXXXX=1` when the reviewed pass used the
relaxed semantic-pass verification mode.

### Agent Review Handoff

`python3 scripts/agent_review.py` is the local v1 path for pass-by-pass
handoff between already-running agent sessions. The user still starts Codex,
Claude, and any worker loops manually; the script records
`.agents/current.json`, points each role at the packet/review artifacts, and
lets a watcher notify the next role after `READY_FOR_REVIEW`,
`CHANGES_REQUESTED`, `READY_FOR_REREVIEW`, or `APPROVED`.

Minimal flow:
```sh
python3 scripts/agent_review.py start-pass --project <slug> --pass-id <id>
python3 scripts/agent_review.py watch --role reviewer --notify <notifier> --once
python3 scripts/agent_review.py request-changes --review <review.md>
python3 scripts/agent_review.py reready --response <response.md> --head HEAD --generate-packet
python3 scripts/agent_review.py approve --review <review.md>
python3 scripts/agent_review.py archive --pass-id <id>
```

`start-pass` is the normal post-commit handoff entry point. It defaults to
`BASE=HEAD~1`, `HEAD=HEAD`, and `RUN_ID=<project>-pass-<id>`, creates
`.agents/runs/<run_id>/implementation.md`, initializes state, generates and
validates the packet, writes the reviewer prompt, and prints status. The Make
wrapper is equivalent:
```sh
make project-pass-review-start PROJECT=<slug> PASS=<id>
```

Use lower-level `init` plus `ready --generate-packet` only when a non-default
range, run id, or hand-authored implementation note is required. `init` writes
the runtime-state patterns to `.git/info/exclude`, because the review head may
predate the branch's tracked `.gitignore`. Long-running `watch` processes may
be started before `init`; they wait for state instead of exiting. If the worker
script is invoked from outside the checked-out tree, the generated prompts use
that external script path instead of assuming `scripts/agent_review.py` exists
at the review head. Run the loop from a checkout that has the project sources
and required untracked reference files; when that checkout predates the worker
script, invoke the script by absolute path from a tool-bearing worktree.
`start-pass`, `ready`, and `reready` validate the packet before handoff: the
packet must name the current review head and its Project Verify Gate must
report exit status 0. When a generated strict packet fails only because
unresolved `LXXXX` labels are still expected for the project, the worker
regenerates it once with `ALLOW_UNRESOLVED_LXXXX=1` and records that relaxed
mode for later rounds. If parity evidence is missing or red, fix the local
project inputs or regenerate from a worktree with the required untracked
reference files before notifying the reviewer.

After approval, `archive --pass-id <id>` writes the durable judgement record to
`projects/<slug>/docs/reverse_engineering/reviews/pass-<id>.md`. It archives
only review verdict/findings and implementer responses. The archive records
project, pass id, scorecard row, path, and review-time SHA range; the durable
key is project plus pass archive path because rebases may orphan SHAs. Packets,
prompts, `.seen` files, and `current.json` stay ignored under `.agents/`;
regenerate packets from the review-time range only while those SHAs remain
reachable. The archive command requires a clean tracked tree, then creates the
tracked follow-up review artifact; commit that artifact before starting the
next handoff, because `ready` and `reready` also refuse tracked dirty state.

The watcher invokes `<notifier> <role> <status> <prompt-file>` and also passes
`AGENT_REVIEW_*` environment variables. A tmux adapter, queue adapter, or
agent-specific worker can be layered on that contract; the state file remains
authoritative and the watcher must not infer verdicts from chat text.
Reviewer prompts route the reviewer through the `Review a committed project
pass` row in `AGENTS.md` before asking for a verdict, so the handoff does not
rely on ambient session memory of the repository rules. That route includes
`TOOLING.md` because packets, gates, and handoff commands are part of the review
surface.

For tmux handoff, put the already-running implementation and reviewer agents
in tmux panes, find their pane ids, and run one watcher per role:
```sh
tmux list-panes -a -F '#{pane_id} #{session_name}:#{window_index}.#{pane_index} #{pane_current_command}'
export AGENT_REVIEW_TMUX_REVIEWER=%12
export AGENT_REVIEW_TMUX_IMPLEMENTER=%13
python3 scripts/agent_review.py watch --role reviewer --notify scripts/agent_review_tmux_notify.sh
python3 scripts/agent_review.py watch --role implementer --notify scripts/agent_review_tmux_notify.sh
```

`scripts/agent_review_tmux_notify.sh` loads the prompt file into a tmux buffer,
uses tmux bracketed paste, and sends Enter by default. This is intended for
paste-aware agent TUIs that enable bracketed paste; do not target an ordinary
shell or other non-paste-aware program with a multi-line prompt. Set
`AGENT_REVIEW_TMUX_SUBMIT=0` to paste without the final submit Enter during
dry runs. The adapter does not start, supervise, or detect readiness of agent
sessions; keep target panes idle at the agent prompt before enabling automatic
submission.

### Evidence Order (Mandatory)

1. **Generated pass artifacts** (`inventory/pass/`) — use first for corridor selection, consumer identification, pass resumption, and cluster sizing.
2. **Structured xasm outputs** (JSON/NDJSON listing, xref, audit) — use when pass cache lacks the needed fact.
3. **Raw asm source** — only for final edits, scope checks, declaration-site comments, and control-flow confirmation.
Do not use broad `rg` sweeps or ad-hoc KPI scripts when pass artifacts already provide the information. If you must fall back, report what was missing and why.

When the pass cache lacks assembled facts, materialize a temporary JSON listing
before opening broad source regions. Keep it outside tracked project files or
under an ignored scratch path, query it for CPU/output offsets, emitted bytes,
record boundaries, directives/opcodes, continuation records, and source-line
coordinates, then open only the source ranges identified by those records.
```sh
xasm --pure-binary -o "${TMPDIR:-/tmp}/<slug>-analysis.o" \
  --listing="${TMPDIR:-/tmp}/<slug>-listing.json" --listing-format=json \
  projects/<slug>/asm/<slug>.asm
```

### xasm Feature Summary

- `--compare`: fast first-mismatch diagnosis with source mapping; use before full `make project-verify`.
- `--listing-format=json|ndjson`: machine-parseable listing; continuation rows are first-class records.
- `--xref`: generate before rename sweeps. Default: `--xref-include-locals=false --xref-include-anon=false`. Use `--xref-include-owner=true` for lexical ownership.
- `--Werror=unused-equ`: hard blocker during constantization/symbolization. Remove unused `.EQU` in same pass.
- `--audit-raw-addresses`: find residual raw addresses. Preferred wrapper: `make project-audit PROJECT=<slug> FORMAT=json`. Shell-quote `$` in ROM ranges.
<a id="data-consumer-analysis"></a>
## Data-Consumer, Data-Coverage, and Index-Pattern Analysis

`make project-pass-prep` emits baseline parity status, both xref summaries,
owner-enriched xref, and three structured-analysis outputs into
`docs/reverse_engineering/inventory/pass/`. Compatible outputs are bundled into
one xasm process so the wrapper does not repeat the same parse/assemble work;
the filtered generic-label xref summary stays separate because summary context
is computed after the include filter is applied. Only `data_consumers.json` is
loaded by `make project-next-pass` (consumer rollups for generated evidence);
`index_patterns.json` and `data_coverage.json` are manual evidence artifacts.

### Index-pattern analysis

```sh
xasm --pure-binary -o Game.o \
    --analyze-index-patterns \
    --index-patterns-output=docs/reverse_engineering/inventory/pass/index_patterns.json \
    --index-patterns-format=json \
    Game.asm
```

Produces `index_patterns.json` — one record per indexed access site,
including `table_label`, `routine`, `site_addr`, `access_kind`
(`read`/`write`), `access_pattern` (`base`, `base_plus_const`,
`paired_byte_reads`, …), `index_register`, `displacement`, and
`index_value_source_kind`. Useful for finding shared lookup tables,
stride-indexed records, and pointer-table consumers without hand-grepping.

### Data-consumer analysis

```sh
xasm --pure-binary -o Game.o \
    --data-consumers \
    --data-consumers-output=docs/reverse_engineering/inventory/pass/data_consumers.json \
    --data-consumers-format=json \
    Game.asm
```

Produces `data_consumers.json` — one record per data label, aggregating
direct symbol-span accesses: `read_site_count`, `write_site_count`,
`distinct_routine_count`, `observed_constant_displacements`,
`access_patterns`, plus per-site arrays of `read_sites`/`write_sites`
with `routine`, `site_addr`, `displacement`, and `addressing_mode`
(`absolute_x`/`absolute_y`/...). Indirect ZP-pointer consumers are
*not* tracked here — they require manual trace.

### Data-coverage analysis

```sh
xasm --pure-binary -o Game.o \
    --analyze-data-coverage \
    --data-coverage-output=docs/reverse_engineering/inventory/pass/data_coverage.json \
    --data-coverage-format=json \
    Game.asm
```

Produces `data_coverage.json` — for each data label: `declared_start`,
`declared_end_exclusive`, `declared_size`, `covered_ranges`,
`covered_size`, `uncovered_ranges`, `uncovered_size`, `access_count`,
and `has_indexed_accesses_without_exact_coverage`. Useful for spotting
declared spans whose interior bytes have no direct reader (potential
mis-split blobs or hidden consumers).

Prefer these structured outputs over ad-hoc grep when planning a pass;
see also [Evidence Order](#xasm-structured-analysis).

<a id="static-analysis"></a>
## Static-Analysis Scanner

`make project-static-analysis PROJECT=<slug>` runs `scripts/static_analysis.py`
and writes the project's `docs/reverse_engineering/STATIC_ANALYSIS.md` (direct
form: `python3 scripts/static_analysis.py <asm> --doc-out <md> [--title T]
[--json J] [--print]` — the script is not marked executable, so invoke it via
`python3`). It assembles the source with xasm and reads the JSON listing — never
regex over source text — so instruction identity, addressing mode, and operand
values are the assembled truth. It builds a control-flow graph keyed by ROM
**output offset** (globally unique, unlike CPU addresses, which repeat across
mapper banks), resolves relative branches by offset arithmetic, and runs backward
liveness of registers {A,X,Y} and flags {Z,N,C,V}. Every finding is verified
against liveness on every path.

The generated doc groups findings into five sections:

- **A. Correctness / latent bugs** — two wrong-register symptoms.
  (1) *Uninitialised-index overrun*: an index register *live-in* to a tight
  fixed-count copy/fill loop (read before the routine writes it) overruns its
  buffer. The scan proves only that the index is unset *inside* the routine, so
  findings split by confidence: a **wrong-register init** (`LDX` where `LDY` was
  meant) is a confirmed defect regardless of caller, while a no-typo case is a
  **call-contract review candidate** — the index is an input register, and the
  tool checks the direct `JSR` callers to report whether they establish it.
  (2) *Suspected wrong-register load/store*: a **dead `LD? #imm` immediately
  before a `ST?` that reads a different register** is the fingerprint of a
  load/store register mismatch — the immediate lands in one register but the store
  writes another, so `#imm` is discarded and a stale register is stored (e.g. a
  leftover `$F4` reaching `PPUSCROLL` because `LDY #0` sat before `STA`, or a
  `LDA #imm` sitting before an `STX`). Fix is either `LD<store-reg> #imm` or
  `ST<load-reg>`.
  (3) *Suspected shift/carry confusion*: a **dead carry-setter (`CLC`/`SEC`/`CMP`)
  discarded by a following accumulator `ASL`/`LSR`** — the shift folds a `0` into
  the vacated bit, not the carry, so `ROL`/`ROR` was likely meant (harmless where
  the carry was never needed, a real bug where the carry-dependent path is now
  dead). (2) and (3) are promoted out of the dead-instruction category.
- **B. Dead instructions** — every register/flag the instruction defines is dead
  on exit and it has no side effect.
- **C. Micro-optimizations** — `AND #$80` collapsible to `BMI`/`BPL` (only when
  **both A and Z** are dead after the branch, since dropping the `AND` changes
  Z), a redundant `CMP #$00` after a flag-setting op, and a register→A transfer
  before a compare replaceable with `CPX`/`CPY`. The doc splits the **bit-7** case:
  a **fixed-bit-7 register** test (`LDA PPUSTATUS` — bit 7 = vblank, or `$4015` —
  bit 7 = DMC IRQ) is the idiomatic wait, a clean win that needs no comment; a
  **software-flag** test is a trade-off — `BMI`/`BPL` hard-codes bit 7 (it breaks
  if the flag's layout moves) and drops the named mask, so it needs a comment
  naming the bit. This fixed-bit-7 set is distinct from the side-effect-read set:
  `$2007`/`$4016`/`$4017` also read with side effects, but their bit 7 is data or
  open bus, so a bit-7 test there is a software-flag trade-off, not a clean win. The compare-to-zero case splits the same way: a literal `#$00`
  is a clean drop, but a **named zero-valued sentinel** (`CMP #FOO_END`, `FOO_END
  == 0`) is a trade-off — only redundant while the constant is `0`, and dropping
  it loses the name, so it wants a comment. The transfer rewrite carries no such
  cost.
- **D. Redundant reload after store** (lower confidence) — only when **both** the
  store and the reload instruction are *unlabeled*, so the pair has a single
  fall-through entry. A labeled reload may be entered with a different A; a labeled
  *store* may be entered with N/Z set by another instruction (e.g. via `BNE`),
  making the reload needed to refresh the flags. Labels come from the
  listing (their own records), so this is checked structurally. When the stored
  value's producer is a `JSR` (the finding names the subroutine), removability is
  **non-local**: it holds only if the callee returns with N/Z set on `A`, so it
  must be verified against the callee's flag-return contract, not the call site.
- **E. Tail-call candidates** — an assembled `JSR target` immediately followed by
  a ROM-contiguous `RTS`. This is detected from xasm instruction records and
  output offsets, not source-text matching, so comments, labels, blank lines, and
  formatting cannot create false adjacency. It is a source-annotation worklist:
  the parity source keeps `JSR`/`RTS`, while a non-parity build could usually use
  `JMP target` only after the callee's stack/return-address contract is reviewed.
  If the `RTS` is itself labeled or shared, the report notes that only the call
  path is a tail-call shape.

Category-C candidates whose affected value liveness could not prove dead on every
path (e.g. live at an `RTS`, so possibly a return value) are simply not reported —
they were report noise. They remain in the `--json` output under `excluded` for
tuning/debugging the liveness only.

Every finding carries an `annotated` flag: true when the finding's **flagged
instruction** (its own line — the dead instruction, the reload instruction, the
compare, ...) carries an inline comment (`;`). Only that line is checked, never
the surrounding context (a comment on a producer/branch is usually unrelated
prose and must not mask the finding). This is a heuristic proxy for "already
handled", not a semantic claim, so the report describes the observable ("has an
inline comment"), not "annotated". The report leads with a **Source-annotation
status** block that counts the findings with no inline comment and lists them per
category — the worklist for a source-annotation sweep — and marks the rest
*(flagged instruction has an inline comment)*. Idiomatic category-A/C forms that
need no comment (e.g. a fixed-bit-7 vblank wait, a literal compare-to-zero) still
appear in the worklist until a comment is added or the reviewer judges none is
warranted.

Conservative by construction, so reported items are a floor rather than guesses:
`JSR`/`RTS` use all registers and flags, and absolute `JMP`/`JSR` targets plus
non-ROM-contiguous fall-through (the `.DB $2C` opcode-skip idiom) are treated as
unresolved (full live-out). Hardware-register read side effects and memory-operand
shift/rotate flag semantics come from the listing's addressing mode, not a guess.
Categories B–D are **mod-only**: applying them breaks byte parity, so they serve
an article on hand-written 6502 and future relocatable mod builds, while the A
findings are genuine ROM defects. Extend the tool by adding a detector that
consumes the shared CFG + liveness in `analyze()` / `find_overruns()`, then re-run
the wrapper to regenerate the doc.

<a id="orphan-opcode-scan"></a>
## Orphan Opcode Hidden-Code Scan

`make project-hidden-code-scan PROJECT=<slug>` runs
`scripts/orphan_opcode_scan.py` and writes
`docs/reverse_engineering/inventory/pass/orphan_opcode_candidates.csv`. The
output is ignored generated evidence, not a gate or committed report. Optional
knobs are `MIN_SIZE=12`, `THRESHOLD=22`, and `MAX_START_OFFSET=64`; use
`MIN_SIZE=1` when auditing short table-tail stubs.

The scanner assembles with xasm and reads `.DB` bytes, CPU addresses, and output
offsets from the JSON listing. Symbolic `.DB` operands and semantically named
labels therefore keep their assembled address context. The wrapper passes the
reference ROM for mapper-aware candidate labels when the ROM is present; direct
script runs can use `--ref-nes` or `--mapper`. It tries official 6502
instruction runs at candidate offsets inside each span, then joins project
context from `WARNING_BASELINE.txt`,
`codeentries.txt`, `dataranges.csv`, `inlinecalls.csv`, and
`data_blob_dispositions.csv` when present. It may emit multiple rows for one
span; `is_best=yes` marks the best offset, while lower-scoring table-tail stubs
can still appear. Review each row manually: text, PPU packets, CHR/tile data,
pointer tables, padding, and mixed code/data overlays can all score as
opcode-like. Durable conclusions belong in NESrev recovery controls,
`WARNING_BASELINE.txt`, or data-disposition ledgers.

### Control-flow target validation

Byte identity proves provenance, not executability. A candidate is only
executable where its own absolute `JSR`/`JMP` operands land on instruction
starts in the bank mapped at run time, so the scanner resolves every such
operand against the listing before treating a run as strong evidence: for a
candidate in bank N, `$8000-$BFFF` resolves in bank N and `$C000-$FFFF` in the
fixed bank. For non-banked mapper-0 images, `$8000-$FFFF` resolves through the
single PRG image; 16 KiB NROM mirrors `$8000-$BFFF` to the same offsets as
`$C000-$FFFF`. Without mapper context, banked target validation can remain
unknown. `target_valid` reports the outcome.

- `yes` — every target resolves to an instruction start.
- `no` — at least one target lands on a `.DB`/`.DW` record or inside another
  instruction. Such runs are disqualified from score-based filtering however
  clean the decode looks; `--all` still lists them.
- `unknown` — nothing resolved invalid but something could not be resolved: a
  RAM destination (normal for a copied ROM-to-RAM image), a fixed-bank
  candidate calling the switched window, `JMP (indirect)`, or no absolute
  target at all. Unknown is unproven, never treated as valid.

`resolved_targets` counts validated targets, `invalid_targets` names each
failure as `$ADDR:reason@bankN`, and `target_validation_notes` explains
anything unresolved. `score` still measures decode coherence alone; validity is
the separate axis, and `is_best` prefers a validated run over a higher-scoring
unvalidated one. Sort by `target_valid` then `score` when triaging.

<a id="vocabulary-drift"></a>
## Vocabulary-Drift Detectors

Two advisory detectors report a placeholder shape the existing audits cannot
see. The [stale-placeholder sweep](REVIEW_AUDITS.md#stale-placeholder-audit)
matches address- and ordinal-coded names such as `State03` or `Page0600`. It
cannot match a plausible generic noun phrase, which satisfies every naming rule
while identifying nothing — and reads as resolved, so later passes build on it.
Both crosswalk header spellings are accepted; matching only the canonical one
read thirteen projects as empty tables and silently disabled the check.

Both detectors always exit `0`, and both are opt-in: they run only when
`PROOF_DEBT_REQUIRED="1"` is set in `project.conf`. Legacy projects stay silent,
because these checks read authored ledgers that postdate most of the corpus and
would otherwise report a debt the project never had the chance to incur. New
scaffolds opt in. Both run at `project-next-pass`, before corridor selection,
and again in `project-maturity-summary` alongside coverage.

```sh
python3 scripts/proof_debt.py <doc_root> <crosswalk.md> [--crosswalk-only]
python3 scripts/symbol_vocabulary_check.py <asm> [crosswalk.md] [--dominant N] [--top N]
```

`symbol_vocabulary_check.py` ranks multi-word noun phrases by distinct symbols
headed, ignoring leading verbs, connectors, and `LXXXX` labels. A phrase heading
`--dominant` symbols (default 100) reports only when the crosswalk does not
account for its words — a large family the crosswalk names is a healthy
subsystem. Families are annotated `in`, `partly in`, or `not in crosswalk`.

Neither result is a defect alone; read them as the trigger for
[PASS_WORKFLOW.md#identity-pass](PASS_WORKFLOW.md#identity-pass).

`proof_debt.py` reports the ratio signals described at
[PASS_WORKFLOW.md#proof-debt](PASS_WORKFLOW.md#proof-debt). `--crosswalk-only`
narrows the report to crosswalk currency alone.

`--coverage` answers a different question: not whether a ledger exists, but how
much of the work it accounts for. The KPI suite measures the assembly and never
the evidence about it, so a named label with no reasoned rename row is a
decision nobody can trace. Both modes are derived from ledgers that already
exist and store nothing of their own.

Re-run the corpus backtest before changing the signal set. A detector whose
fire rate is unknown may be loud enough to train the operator to scroll past
the region where every other signal appears, which is worse than not having
it.

<a id="nesrev-controls"></a>
## NESrev Regeneration Controls

NESrev is the disassembler. It is driven through the
`make project-regenerate-asm` wrapper, optionally fed five recovery
control files that compose. For reproducible projects, keep active
controls under `projects/<slug>/config/nesrev/` and name them in
`project.conf`; the base wrapper command then reloads them
automatically. Use these controls when the linear-trace pass leaves
code unreachable behind indirect dispatch, mis-decodes data blobs, or
fails to recover inline-call payloads.

### Hint file formats

```sh
# codepointers.csv — pipe-delimited. Mapper 0 rows use start = raw PRG
# offset (hex), count = number of pointers. MMC1 rows may instead use
# bank|addr|count when banked CPU context is clearer. Use for contiguous
# CODE-pointer tables: NESrev labels each target AND traces it as code.
# For MMC1 fixed-bank tables whose entries are $8000-$BFFF addresses, each
# entry seeds that CPU address in every non-final PRG bank; the table word
# remains raw because no single label exists.
# start|count
# 0x0008|30
# bank|addr|count
# 0|$8100|12

# datapointers.csv — same shape as codepointers.csv, but targets are DATA
# records. NESrev labels each target so the .DW line reads symbolically, but
# does not trace the bytes at the target as code. Use when a few "lucky"
# records would otherwise mis-decode as plausible instructions (5-byte audio
# period/envelope tables, etc.).
# start|count
# 0x2813|30

# codeentries.txt — one canonical ROM CPU address per line, or bank|addr for
# MMC1 switched-window entries. # and ; start comments. Use for SCATTERED code
# entry points reached via indirect dispatch where the pointer is loaded from
# individual `LDA #imm / STA ZP_PTR` pairs rather than a contiguous table.
# For executable ROM-source images copied into RAM/PRG-RAM, add translated ROM
# source addresses here, not runtime RAM execution addresses.
# $C22F   ; channel 0 command handler (reached via JMP [$00EB])
# $D187
# bank|addr
# 0|$8120
# 7|$C000

# inlinecalls.csv — pipe-delimited; callee CPU address + payload layout
# descriptor for inline-call patterns (JSR followed by inline bytes the
# callee consumes from the return address). Layout tokens include `u8`,
# `bytes(N)`, `counted8`, `ptr16(data)`, `ptr16(code,+1)`, and repeat
# shorthand such as `ptr16(code)*31`. Use callsite rows when one helper
# has variable record lengths. MMC1 rows
# may use bank|callee|layout for switched-bank callees, or
# bank|callsite|callee|layout when the JSR site is in a specific bank.
# callee|layout
# $C8BB|u8,ptr16(data)
# $C963|bytes(6)
# $EA05|counted8
# callsite|callee|layout
# $C120|$C27C|ptr16(code)*3
# bank|callee|layout
# 0|$8120|u8
# bank|callsite|callee|layout
# 0|$8027|$C27C|ptr16(code)*2

# dataranges.csv — pipe-delimited; explicit data-byte regions NESrev should
# treat as opaque payload rather than trying to decode as instructions. MMC1
# rows may use bank|addr|length for switched-bank data.
# start|length
# $CD20|14
# $D5B6|34
# bank|addr|length
# 0|$9000|32
```

### Wrapper invocation

The reproducible command is always:

```sh
make project-regenerate-asm PROJECT=<slug>
```

Set active paths in `projects/<slug>/project.conf`:

```sh
NESREV_RECOVERY_STATUS="configured"
NESREV_CODEPOINTERS_FILE="projects/<slug>/config/nesrev/codepointers.csv"
NESREV_CODEENTRIES_FILE="projects/<slug>/config/nesrev/codeentries.txt"
NESREV_DATAPOINTERS_FILE=""
NESREV_INLINECALLS_FILE=""
NESREV_DATARANGES_FILE=""
```

Use `NESREV_RECOVERY_STATUS="none"` only after discovery finds no
required controls. The scaffold's `pending` value blocks intake so a
plain linear-trace result cannot be committed accidentally.

`CODEPOINTERS=`, `DATAPOINTERS=`, `CODEENTRIES=`, `INLINECALLS=`, and
`DATARANGES=` command-line values override the
matching configured path for one run. Use overrides to experiment, then move accepted
inputs into `config/nesrev/` and `project.conf` before intake or
commit. Controls under the ignored `reference/` tree are not
reproducible build inputs.

### Configuration notes

- In this repo, local `NESrev` consumes the raw PRG, not the `.nes`
  container.
- `codepointers.csv` / `datapointers.csv` `start` is a raw PRG offset, not a
  `.nes` file offset and not a CPU address.
- `codeentries.txt`, `inlinecalls.csv` callees, and `dataranges.csv`
  starts are CPU addresses in the canonical project ROM range
  (`$C000-$FFFF` for NROM-128 and MMC1 fixed-bank code,
  `$8000-$FFFF` for NROM-256). MMC1 `$8000-$BFFF` targets require
  bank-qualified `codeentries.txt` rows, pointer evidence from within the
  same switched bank, or an explicitly configured code-pointer table whose
  ambiguous entries should be probed across all non-final PRG banks.
- `inlinecalls.csv` resolves `ptr16(code)` targets in the callsite's bank
  context. It cannot currently express a fixed-bank inline payload whose
  `$8000-$BFFF` targets belong to a bank selected immediately before the
  dispatcher call. The failure is a hard ConfigException: `adjusted pointer
  target $XXXX is outside canonical ROM space`. Recover the target routines
  with bank-qualified `codeentries.txt` rows (`bank|addr`); only the inline
  payload's pointer bytes stay unsymbolized. Use `dataranges.csv` plus
  warning-baseline rationale until NESrev supports a target-bank override for
  inline payload pointers.
- Pick the right hint:
  - contiguous table → code routines: `codepointers.csv`
  - contiguous table → fixed-size data records: `datapointers.csv`
  - scattered indirect-dispatch entries with no static table: `codeentries.txt`
  - JSR-with-inline-payload patterns: `inlinecalls.csv`
  - data ranges NESrev keeps eagerly decoding as instructions: `dataranges.csv`
- All five may be present at once; they compose.
- Seed any new entries discovered during the re-run; NESrev will surface
  additional unreachable labels as it traces deeper.
When to run NESrev regeneration during a Code-Pointer Recovery Pass is
recovery-strategy guidance — see
[DATA_RECOVERY.md#code-pointer-recovery](DATA_RECOVERY.md#code-pointer-recovery).

<a id="inventory-commands"></a>
## Inventory Commands

Inventory snapshots in `docs/reverse_engineering/inventory/` are
machine-readable summaries of symbols, pointer targets, KPIs, and other
project state. Refresh them before closing any pass that touched
symbols, constants, pointers, or counts.

### Refresh wrappers

```sh
# Canonical wrapper — refreshes all inventory snapshots for the project.
make project-inventory PROJECT=<slug>

# Equivalent script form (occasionally used inside other wrappers).
scripts/refresh_inventory.sh <slug>
```

For *when* to refresh the inventory during a pass, see
[PASS_WORKFLOW.md#pass-closeout](PASS_WORKFLOW.md#pass-closeout). The
canonical authored-artifact catalog (`renames.csv`,
`pointer_targets.csv`, `embedded_pointer_targets.csv`,
`split_pointer_targets.csv`, `branch_literal_sites.csv`,
`constants_catalog.csv`, `data_extent_assertions.csv`,
`data_format_targets.csv`, `data_blob_dispositions.csv`, `unknowns.md`, etc.) lives at
[AGENTS.md#intermediate-artifacts](../AGENTS.md#intermediate-artifacts);
the generated cache under
`docs/reverse_engineering/inventory/pass/` is documented at
[PASS_WORKFLOW.md#generated-vs-authored-artifacts](PASS_WORKFLOW.md#generated-vs-authored-artifacts).

`pointer_targets.csv` reports source owners for actual `.DW` pointer tables.
Inline return-table payloads are attributed to their dispatching callsite, not
to a synthetic table label, and the terminal three NES CPU vector words are
excluded so they are not misattributed to the preceding data label.

`embedded_pointer_targets.csv` reports relocatable pointer fields that remain
inside `.DB` records as adjacent `<label,>label` operands. It is a sibling
ledger, not a replacement for `pointer_targets.csv`: use it for fixed-stride
records whose other fields must stay byte-sized, such as source-pointer fields
mixed with bank, VRAM address, and count bytes. `project-verify` checks the
ledger when it exists, so reverting such fields to raw low/high bytes fails
until inventory and source agree.

`split_pointer_targets.csv` reports relocatable targets in paired low/high byte
tables (`FooPtrLoTable` `<Target` plus `FooPtrHiTable` `>Target`). The sync
check requires equal counts, symbolic entries, and identical per-index target
expressions; it is shape-specific, not a general embedded-pointer detector.

`data_format_targets.csv` is an authored maturity worklist for core data-format
families. New scaffolds enable `DATA_FORMAT_TARGETS_REQUIRED=1`; process checks
validate schema and canonical family coverage, and maturity checks additionally
reject rows still marked `not_yet_reviewed` or `queued_static_pass`.

`data_blob_dispositions.csv` is a per-label worklist for long or opaque spans.
New scaffolds enable `DATA_BLOB_DISPOSITIONS_REQUIRED=1`. `project-process-check`
validates existing ledgers and prints advisory candidates from
`inventory/pass/data_coverage.json`; maturity blocks opted-in projects when
candidate spans lack rows, rows remain `not_yet_reviewed` or
`queued_static_pass`, or structural rows lack consumer, pointer-search, extent,
artifact, or reflow evidence. Exact labels or glob patterns are allowed only
for genuinely repeated same-format spans.

`data_extent_assertions.csv` pins the byte size of a fixed-size table that a
consumer indexes with a masked or fixed-count index (`AND #mask` / `CPX #count`
before `LDA Table,Y`). Two scripts pair with it: `data_extent_assertions_check.sh`
(in `project-verify`) *validates* listed rows — it fails if an asserted table's
assembled size drifts; `data_extent_missing_scan.py` (advisory, in
`project-process-check`) *detects omissions*. The scan is a pure join of two
cached pass-prep artifacts and never assembles: it reads `index_upper_bound` /
`index_bound_kind` from `index_patterns.json` (xasm resolves the mask/compare
bound, tied to the read's index register, with symbolic mask/count constants
resolved — see `xorcyst/XASM_INDEX_BOUND_ANALYSIS_SPEC.md`) and `declared_size`
from `data_consumers.json`, then flags any table whose proven bound equals its
declared size and which lacks an assertion row. It never fails the gate; it only
surfaces candidates for the operator to add or disposition. Only the two direct
idioms xasm proves are covered (a mask reaching the index register indirectly,
or a bound held in a variable, is not proven), so a clean scan is a strong
signal but not an exhaustive guarantee.
Disposition values are `not_yet_reviewed`, `queued_static_pass`, `documented`,
`absent_not_applicable`, and `runtime_gated`.

`project-process-check` also runs a non-mutating inventory integrity guard. If
any generated inventory snapshot exists (`constants_catalog.csv`,
`pointer_targets.csv`, `embedded_pointer_targets.csv`,
`split_pointer_targets.csv`, `branch_literal_sites.csv`, or `unknowns.md`), the
guard regenerates those snapshots into a temporary directory and fails when the
project copy is stale; run `scripts/refresh_inventory.sh <slug>` and commit the
synchronized output.
It also validates active `raw_ram_review.csv` `top_readers` / `top_writers`
owners still resolve to live labels, catching stale owner columns after renames
that bypassed closeout. Owner tokens should name a global label, or a scoped
named local label written as `Global@@local`. Anonymous `@` owner tokens are
allowed because they cannot be made unambiguous in ledger prose; inactive
historical rows are not retroactively normalized by this guard.

Projects may opt into the raw `.DB` embedded-pointer audit with
`EMBEDDED_POINTER_AUDIT_REQUIRED=1` in `project.conf`. The audit finds
little-endian runs of CPU addresses (values in the $8000-$FFFF PRG address
space, not ROM file offsets) in raw byte spans — both monotonic pointer arrays
and non-monotonic pointer structs — scoped to the per-bank PRG window inferred
from each bank's `.ORG` (so NROM-128 mirror addresses are rejected). A
run becomes a hard failure only with a consumer proof: either a xasm
paired-byte-read plus a ZP `PtrLo`/`PtrHi` store that is later dereferenced
(pointer arrays, alias-aware), or a block-copy into a ZP base that is
dereferenced (structs). The run counts alone are advisory because CHR/pixel data
and scalar tables can look pointer-like. Planned refinements and the validation
corpus live in
[EMBEDDED_POINTER_AUDIT_SPEC.md](EMBEDDED_POINTER_AUDIT_SPEC.md).

<a id="base-readability-gate"></a>
New clean-room project scaffolds set `BASE_READABILITY_REQUIRED=1` in
`project.conf`. Legacy projects default off and may opt in after a base pass
reaches zero. When enabled, `project-verify` runs
`base_readability_kpi.sh --strict`, which hard-fails when hex `#$00`/`#$01`
appear in index-register (`LDX`/`LDY`/`CPX`/`CPY`) or unit-step
(`ADC`/`SBC #$01`) quantity contexts, where the
[Literal Base Readability](ASM_STYLE.md#literal-base-readability) rule requires
decimal. The check does not mechanically inspect `LDA`/`AND`/`ORA`
immediate-zero sites because that opcode class includes real machine-oriented
exceptions, such as hardware-register payloads, address low bytes, tiles,
sentinels, masks, or pointer bytes. Review those sites semantically before any
broader conversion. Run without `--strict` for a non-failing count.

<a id="pointer-table-relocation-gate"></a>
`pointer_table_body_check.py <asm>` flags labels named as a pointer table
(`...PtrTable`, `...Pointers`, ...) whose body is still a raw numeric `.DB` lo/hi
run — un-relocated embedded pointers the audit's consumer proof cannot see. It
skips already-symbolic bodies (`.DW`, `.DB` with `<`/`>`) and non-PRG words, so
headers and misnamed tables do not fire. `project-verify` and
`project-maturity-check` run this check in strict mode for every project; a
non-zero count is a regression. Recipe:
[REVIEW_AUDITS.md#pointer-byte-consolidation-audit](REVIEW_AUDITS.md#pointer-byte-consolidation-audit).

### Raw-address audit

```sh
# Project wrapper (preferred): runs xasm --audit-raw-addresses with the
# project's configured ROM range and writes machine-readable findings.
make project-audit PROJECT=<slug> FORMAT=json
```
### KPI and assertion scripts

Each KPI script reads the asm plus an inventory config and prints a metric
(definition count, doc coverage, etc.) plus a per-line breakdown. Assertion
scripts read reviewed inventory ledgers, such as table-span assertions. They
are read-only; failures should drive an edit and re-run rather than config
tweaks.
```sh
bash scripts/branch_literal_kpi.sh Game.asm docs/reverse_engineering/inventory/kpis.conf
bash scripts/comment_quality_kpi.sh Game.asm docs/reverse_engineering/inventory/kpis.conf
bash scripts/constant_kpi.sh Game.asm docs/reverse_engineering/inventory/kpis.conf
bash scripts/data_label_doc_kpi.sh Game.asm docs/reverse_engineering/inventory/kpis.conf
bash scripts/data_extent_assertions_check.sh Game.asm docs/reverse_engineering/inventory/data_extent_assertions.csv
bash scripts/embedded_pointer_targets_check.sh Game.asm docs/reverse_engineering/inventory/embedded_pointer_targets.csv
bash scripts/global_code_label_doc_kpi.sh Game.asm docs/reverse_engineering/inventory/kpis.conf
bash scripts/inferred_kpi.sh Game.asm docs/reverse_engineering/inventory/kpis.conf
bash scripts/procedure_doc_kpi.sh Game.asm docs/reverse_engineering/inventory/kpis.conf
bash scripts/raw_address_kpi.sh Game.asm docs/reverse_engineering/inventory/kpis.conf
python3 scripts/embedded_pointer_audit.py Game.asm
```

KPI gates are floors, not finish lines — see
[QUALITY_REVIEW.md#kpi-interpretation](QUALITY_REVIEW.md#kpi-interpretation),
which extends the guiding principle at
[AGENTS.md#guiding-pass-philosophy](../AGENTS.md#guiding-pass-philosophy).

<a id="parity-drift"></a>
## Parity-Drift Diagnostics

When a parity check fails, the listing bridges ROM offsets to source lines:

1. Identify the differing ROM offset (e.g., from `cmp -l` or `make project-compare`).
2. Convert to CPU address (NROM-128: `CPU_ADDR = $C000 + ROM_OFFSET`; NROM-256: `CPU_ADDR = $8000 + ROM_OFFSET`; MMC1 fixed bank: use `$C000 + (ROM_OFFSET - fixed_bank_offset)` for offsets in the final 16 KB bank).
3. Look up that address in the listing (with JSON: `jq` filter on `.addr`; with plaintext: text search).
4. Troubleshoot: check hex bytes against reference, look for mis-sized instructions (Absolute vs Zero Page), floating labels from size discrepancies upstream, or raw operands that need symbolization.
<a id="command-reference"></a>
## Command Reference

Compact index of every command documented in this playbook plus a few
debug-only recipes not big enough to warrant their own section.

### xasm

- Assemble + listing (preferred JSON form): [#xasm-options](#xasm-options)
- Wrapper workflow (regenerate-asm, pass-prep/next/start/closeout):
  [#xasm-structured-analysis → Warm-Up and Closeout](#xasm-structured-analysis)
- Feature summary (`--compare`, `--xref`, `--Werror=unused-equ`,
  `--audit-raw-addresses`): [#xasm-structured-analysis → xasm Feature
  Summary](#xasm-structured-analysis)
- Debugging command catalog (one-line forms of the above):
  [#exit-codes → Debugging Commands](#exit-codes)
- Exit-code interpretation: [#exit-codes](#exit-codes)

### Structured pass-prep analysis

- Index patterns, data consumers, data coverage:
  [#data-consumer-analysis](#data-consumer-analysis)
- Project-pass review packet (`make project-pass-review-packet PROJECT=<slug>
  BASE=<base> HEAD=<head>`):
  [#xasm-structured-analysis → Project-Pass Review Packet](#xasm-structured-analysis)

### Static analysis

- Dead code, latent bugs, micro-optimizations
  (`make project-static-analysis PROJECT=<slug>`): [#static-analysis](#static-analysis)
- Orphan opcode hidden-code candidates
  (`make project-hidden-code-scan PROJECT=<slug>`):
  [#orphan-opcode-scan](#orphan-opcode-scan)

### Vocabulary drift

- Crosswalk currency and symbol vocabulary:
  [#vocabulary-drift](#vocabulary-drift)

### NESrev regeneration

- CSV hint formats + wrapper invocation:
  [#nesrev-controls](#nesrev-controls)

### Inventory and KPIs

- Refresh wrappers (`make project-inventory`, `scripts/refresh_inventory.sh`):
  [#inventory-commands → Refresh wrappers](#inventory-commands)
- Raw-address audit wrapper: [#inventory-commands → Raw-address audit](#inventory-commands)
- KPI script suite (full list): [#inventory-commands → KPI scripts](#inventory-commands)

### Parity drift

- 4-step diagnosis procedure: [#parity-drift](#parity-drift)

### Anti-placeholder doc check

**Must return no matches** — fails the docs-quality gate otherwise:
```sh
rg -n "Format: packed byte data block \\(structure documented by nearby consumer code\\)\\.|Used by: routines that reference this label in gameplay/render/audio paths\\." Game.asm
```

### Mismatch debugging recipes

Used after `make project-verify` or `make project-compare` reports drift:

```sh
# First differing byte (raw file compare)
cmp -l extracted_prg.bin Game.o | head

# Hex bytes around a mismatch
# -j <ROM_OFFSET> -N <BYTE_COUNT>
od -An -tx1 -j 60 -N 16 Game.o
```

**Run xasm and verify sequentially, not in parallel** — concurrent runs
produce stale/intermediate `Game.o` that triggers false parity failures.
### Search recipes

```sh
# Unresolved generic labels
rg -n "\bL[0-9A-F]{4,5}\b|^L[0-9A-F]{4,5}:" Game.asm

# Unknown symbols
rg -n "\bUNK_" Game.asm

# Indirect control-flow sites (likely pointer consumers)
rg -n "JMP \\(|JMP \\[|\\[[A-Za-z0-9_]+\\]" Game.asm
```

### Mass symbolization

A full strategy, not a one-liner: it requires a preflight match-count,
asm-only scoping, `.EQU` exclusion, data-table exclusion, and a
post-edit prose sweep. See
[PASS_WORKFLOW.md#batching-and-commit-boundaries → Mass symbolization decision tree](PASS_WORKFLOW.md#batching-and-commit-boundaries)
for the complete decision tree and the mechanics above for the
in-place edit script checklist.

<a id="exit-codes"></a>
## Tool Exit Codes and Debugging

### Exit Codes

- `2`: CLI misuse.
- `3`: file I/O failure.
- `4`: audit findings (`--audit-level=error`).
- `5`: compare mismatch.

### Debugging Commands

```sh
xasm --pure-binary --listing=Game.lst.json --listing-format=json Game.asm
xasm --pure-binary --xref=Game.xref.json --xref-format=json --xref-include-owner=true Game.asm
xasm --pure-binary --audit-raw-addresses '--audit-rom-range=$C000-$FFFF' --audit-output-format=json Game.asm > Game.audit.json
xasm --pure-binary --Werror=unused-equ Game.asm
xasm --pure-binary --compare=reference_prg.bin Game.asm
make project-comment-audit PROJECT=<slug> FORMAT=text
```

Use `$8000-$FFFF` as the raw-address audit range for NROM-256 projects.
Use `$C000-$FFFF` for NROM-128 and MMC1 fixed-bank projects.

<a id="script-hygiene"></a>
## Auxiliary-Script Hygiene

To prevent repository clutter and noise in `git status`, avoid placing
ad-hoc or temporary helper scripts (e.g., Python analysis scripts,
one-off scrapers) directly in project or script directories.
### Temporary script placement

- Place all temporary scripts in the `tmp/projects/<slug>/` directory at
  the project root (creating it if necessary).
- This ensures isolation when multiple agents are working on different
  projects in parallel.
- If a script becomes a permanent part of the project's workflow, move
  it to the official `scripts/` directory or the project-specific
  `scripts/` folder (create `projects/<slug>/scripts/` — and analogously
  `tools/` or `notes/` — on demand; the scaffold no longer pre-creates
  them) and document it in `QUICK_REFERENCE.md`.
### Session-end cleanup

- Before closing a project session, identify any unmanaged scripts in
  `projects/<slug>/` and move or delete them.
- Do not stage or commit temporary scripts to the repository.
### Script quality gate
Deterministic output, explicit error messages, no fragile quoting, works
under `set -euo pipefail`, documented in `QUICK_REFERENCE.md`.

### Mass-replacement mechanics

Cross-referenced from
[PASS_WORKFLOW.md#batching-and-commit-boundaries → Mass symbolization decision tree](PASS_WORKFLOW.md#batching-and-commit-boundaries).
When that decision tree says to drive a sweep with Perl, follow these
mechanics:

- **Use Perl, not sed.** `sed` word boundaries are inconsistent
  across OS. Pattern shape:
  `s/(?<!\w)INST\s+\\\$0{0,3}ADDR\b/INST SYMBOL/gi`.
- **Handle variable leading zeros.** Account for 0-3 leading zeros
  (`$DA`, `$0DA`, `$00DA`).
- **Recursive definition guard.** Exclude `.EQU` lines
  (`unless /\.EQU/`) to prevent `ZP_VAR .EQU ZP_VAR`.
- **Exclude data tables.** Only symbolize executable instructions
  and indirect operands, not `.DB`/`.ASC` content.
- **Replacement impact gate.** Preflight grep to count matches.
  Scope explicitly (asm-only or docs-only). After replacement, scan
  `Format:`/`Used by:`/`Index:` fields for collateral rewrites.
- **Perl string quoting.** Use single-quoted strings for `$`
  literals in Perl hash values. Anti-pattern: `'RAM_Base+\$28'`
  (backslash). Correct: `'RAM_Base+$28'`.
### Multiline doc/ledger edits

Do not write `renames.csv` rows, markdown bullet lists, or scorecard
rows via shell-constructed strings that embed literal `\n`. Use
`apply_patch` or another file-safe editor so each logical row/bullet
is written as an actual line in the target file.
### Dollar-sign text safety

Do not use shell interpolation to inject documentation text
containing `$` literals (for example `$0203`, `$C000`, `$0A`) into
markdown, CSV, or asm comments. Use single-quoted patch content or a
file-safe editor so `$` remains literal and cannot expand to shell
variables or process names.
### Anonymous back-label conversion

Anonymous back-labels (`-`) are optional, not default. Apply only
when all readability checks pass: loop is short and linear (head and
back-branch close together); no intermediate conditional branches
that reduce readability; no cross-scope visibility requirement; scope
audit confirms only backward branches within the same global
procedure reference the label; place `-` on the same line as the
first instruction (`- LDA $00`, not on a standalone line); use Perl
(not sed) for multi-line transformations.

<a id="runtime-trace-tooling"></a>
### Runtime trace tooling

Runtime tracing is a standard evidence lane, not an ad-hoc last resort. Use it
when static analysis cannot prove a behavior because the answer depends on live
input, timing, RNG, scenario state, or emulator-visible external state.

Commit durable trace infrastructure when it is repeatable and project-local:

- capture runners under `scripts/run_trace_*.sh`
- emulator Lua scripts under `tools/trace/`
- analyzers under `scripts/analyze_*_trace.sh` or equivalent
- synthetic fixtures under `tools/trace/fixtures/`
- reduced evidence summaries under `docs/reverse_engineering/`
- command references in `docs/reverse_engineering/QUICK_REFERENCE.md`

Do not commit raw capture logs, savestates, emulator movies, screenshots, GUI
probe scripts, or one-off crash/debug experiments unless the user explicitly
asks for a curated fixture. Put volatile output under a project `tmp/` path and
ignore it.

Trace scripts must install the watches themselves. The operator may drive the
scenario by playing live input or replaying a movie, but they should not have to
open a debugger UI, set manual breakpoints, or copy watch lists by hand.

<a id="trace-helper-roms"></a>
### Trace helper ROMs

Using a small local mod to set up a runtime scenario is an approved trace
strategy. Prefer a helper ROM when the static question is blocked by long setup
time, late-game phase access, RNG, repeated deaths, or awkward player
positioning. The point is to make the evidence capture short and repeatable,
not to change the behavior under test.

Rules for trace helpers:

- Keep the patch minimal and scenario-oriented: phase select, direct phase
  entry, fixed spawn script, player/enemy positioning, or input-release gates
  are appropriate setup changes.
- Treat helper asm as relocatable source, not as a byte-for-byte patch budget.
  It is fine to expand or shrink setup procedures, insert wrapper routines,
  remove or shorten irrelevant setup/data/music/title-stream content, and let
  labels/vectors move, as long as the helper ROM still assembles to the
  project's configured PRG size (for the NROM-128 projects this is 16 KB) and
  the CPU vectors remain the final vector words. Do not waste time scavenging
  exact padding bytes unless the build actually needs it.
- Preserve the code path being measured. Do not patch the routine, RAM field,
  state transition, collision path, or data consumer whose semantics the trace
  is meant to prove.
- If size pressure forces trimming, trim only content outside the evidence
  path (for example title-screen PPU bytes, music data, unused helpers, or
  unrelated late-game data) and document why that content cannot affect the
  measured path. If the trimmed content might affect the behavior under test,
  lower the confidence or pick a different helper strategy.
- Document the setup in the trace plan and reduced evidence summary: helper ROM
  name, changed setup conditions, and why the behavior under test is still the
  stock path.
- Treat `projects/*/mods/` as local experiment space. Do not commit helper
  mods unless the user explicitly asks for that specific mod to become a
  curated fixture or reusable tool.
- If the helper ROM changes more than setup, lower the confidence or use the
  capture only as a harness/debug signal until a stock-path capture corroborates
  it.

Use the templates in `agent_playbook/templates/trace/` when a project needs a
new harness. The default split is:

- **FCEUX frame-poll backend**: stable baseline for transition graphs,
  milestones, and per-frame context. Avoid FCEUX write callbacks unless the
  exact local build has been proven stable; they may enter debugger execution
  paths and crash some builds.
- **Mesen precision backend**: optional writer-PC backend when per-transition
  ownership matters. Prefer script-installed memory callbacks/watchpoints over
  manual debugger breakpoints.

Every analyzer must be validated on a committed synthetic fixture before real
capture evidence is used for naming. Reduced summaries should include the
scenario gate/milestones, verdict, transition table, and interpretation notes
that tie the captured signal back to the specific static uncertainty.

### Headless/GUI constraints

If runtime tracing requires a GUI, do not block progress. Implement a
local-user runnable script that launches the emulator with the trace script
already loaded. Validate the analyzer with synthetic logs and mark the evidence
gap as "capture pending" until a real capture lands.
