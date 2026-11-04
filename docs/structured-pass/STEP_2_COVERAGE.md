# Step 2 operation coverage

Status: scope baseline v1, prepared for independent plan review. No step-2
operation is implemented by this document. The proposed PR split below needs
agreement before implementation; it does not narrow the rollout's exit criteria.

Baseline: PR #175 merged as `ea2fd0de2`, with service head `40203e10d` and the
official XORcyst 2.1.0 pin. Step 1 is complete. Step 2 completes the operations
needed for normal parity-preserving passes; step 3 changes default launchers and
requires separately authorized real sessions. The [rollout plan](ROLLOUT_PLAN.md)
remains the authority for those completion decisions.

## Scope and evidence

This checklist maps the [High-Value Pass Contract](../../AGENTS.md#high-value-pass-contract),
[Reviewer Simulation Checklist](../../AGENTS.md#reviewer-simulation-checklist),
canonical artifacts, existing service routes, classified historical findings,
the completed prototype pass and the current project-debt register to operations.
It includes recovery hints, shared documents and runtime work: none can be
silently excluded to make a rename-only rehearsal count as a normal pass.
Behavior-changing mods and new-project intake are outside this parity-pass scope.

The local planning evidence pins the project commit, input hashes, relevant
archive excerpts and predecessor query commits. It does not modify those inputs.
The historical census has 307 indexed archives, of which 22 were fully
inventoried in its first batch, yielding 84 classified items. Full classification,
causal attribution and most semantic replays remain incomplete. These figures
describe that frozen inventory, not the current number of reviews or a measured
benefit. No completeness, efficiency or quality-improvement claim follows.

The existing 23-source producer corpus and 64-rename rehearsal establish useful
regression baselines. They do not establish the new operations. In particular,
the completed real prototype pass required a disclosed batch-shape hint, and
the replay is mechanical rather than an independent semantic review.

### Reading the checklist

`Retain` means an existing route must remain covered; `extend` means only part
exists; `new` means no supported editing/profile route exists at the baseline.
These are implementation inventories, not fresh test results. Operation names
below describe proposed contracts; exact wire names belong to their slice spec.
Each row's positive and negative cases are acceptance obligations, not tests
already written. Completion requires a test/result reference for both columns.

Every row has one of these generation and writer contracts:

- **R (read):** both roles may request bounded evidence from an explicitly named,
  integrity-checked generation. Every fact, page and continuation identifies it.
  A cross-project comparison names each separately pinned generation. Reads
  cannot mutate a candidate, manufacture a verdict or run caller-selected code.
- **C (candidate):** the implementer proposes typed changes with record/path
  preimages and a reason; the service alone writes the checkout. Confirmation
  pins the entire preview. Re-certification, semantic contracts, canonical gates
  and complete reference-PRG parity precede publication. Amendment clears prior
  validation, and new publication adds an uncovered review edge.
- **W (wrapper):** fixed service-configured wrappers write their owned artifacts
  inside the candidate transaction. The receipt pins the input generation,
  command, tool hashes, allowlisted environment, actual exit and output hashes.
- **E (evidence):** a trusted supervisor runs a fixed job with pinned inputs,
  bounded resources and an isolated worker where code is authored. Its immutable
  evidence identifies source generation, tool/script/input hashes and outcome.
  Changing an input invalidates reuse; a capture never grants approval.
- **H (handoff/application):** only the existing reviewer authority records
  verdicts; the trusted coordinator computes live coverage and applies the exact
  approved manifest under the existing locks. No implementer-editable approval.

All C/W changes have before/after review in live and retained sessions, including
additions and deletions. Stable record IDs follow explicit provenance, not value
or text coincidence. Splitting/merging data statements records operand-level
correspondence; deleted IDs are tombstoned and inserted records receive new IDs.
Wrong-generation reads, stale confirmations, conflicting edits, malformed
requests and role violations must fail without losing the session. New operations
must preserve interrupted recovery and all-edge review coverage.

## Reads and decision evidence

| ID / status | Read contract; writer / generation | Positive acceptance | Failing-direction acceptance |
| --- | --- | --- | --- |
| R1 — retain | `inspect`, `navigate` symbols/records/uses/comments; R | Every selected global, local, anonymous and EQU declaration and bound use is reachable; lexical blocks include their attached comments. | Same-spelled locals, anonymous chains and same-CPU-address segments cannot be interchanged; missing is distinct from zero uses. |
| R2 — new | RAM reads/writes and aliases by address or declaration; R | Include direct, indexed, RMW, pointer-byte and unresolved-indirect categories, counts and paged examples; show native address, segment and output offset separately. | Equal-valued mask is not an alias; unresolved indirect destination is not a proven access; wrong bank and wrapped indexing cannot disappear into an exact-address group. |
| R3 — extend | Constant/value context and outgoing control/data references; R | Q04 keeps direct/through-EQU uses and per-owner context; selected native control-flow and data edges are reachable from a record. | Wrong same-valued declaration and a missed state reader are exposed by defective/corrected replay; arithmetic and alias paths do not double-count uses. |
| R4 — extend | Q09 and current prose/ledger mentions, plus artifact reads; R | Cover source comments and every admitted current artifact, with paged locations and explicit history exclusions. | A surviving old name in current prose is visible; history stays readable but cannot be rewritten as a repair; oversized matches have a usable continuation. |
| R5 — extend | Scope/unused-symbol, prior-reuse and policy/readability evidence; R/W | Native use/scope inventories and wrapper findings support the mandatory reviewer checklist; approved analogue inputs have separate identities. | Zero direct references does not prove dead code or safe localization; uncertain fall-through/indirect reachability is explicit. Human naming, comment-value and maturity judgments cannot become automatic green verdicts. |
| R6 — new | Data operands, extents and fixed decoders over retained bytes; R/E | Read byte/word/string operand ranges, layout, pointer targets and decoder results with generation-qualified provenance. | Repeated origins, overlapping CPU banks, embedded pointer widths or a guessed record boundary cannot be silently resolved; malformed decoder input refuses. |

R2 and R3 supply writer/reader evidence for per-value state decisions, ownership,
hardware masks and field constants. They do not assert dynamic reachability or
semantic identity. R5 preserves the playbook's Tier 2 prose/judgment checks; it
does not create a speculative quality-query suite. Each enabled Tier 1 query
needs a classified defective/corrected replay and applicable holdout, or a
documented absence of a recoverable historical case plus a neutral control.

## Source edits

| ID / status | Read and mutation contract; writer / generation | Positive acceptance | Failing-direction acceptance |
| --- | --- | --- | --- |
| S1 — retain | R1/R4; bound rename plus typed rename rows; C/W | Global/local/EQU renames preserve all selected uses, unrelated declarations/bindings and ledger prefix, including a 64-name batch. | Independently remove each of the five binding/declaration guards and stale-source-prose guard; designated parity-preserving controls must fail. |
| S2 — new | R1/R2/R3; insert an EQU/label, replace a selected expression, remove a proven-unneeded declaration; C | Typed expressions refer to declaration IDs; preview groups every selected occurrence by owner. Cover hardware masks, field offsets, selector offsets, low/high pointers, bounds and label math. | Same-value wrong binding, implicit broad replacement, use-before-scope error, live-declaration deletion and unintended width/encoding changes refuse; untouched bindings remain identical. |
| S3 — new | R1/R5; localize a global label into an explicit scope; C | Re-certify all uses, neighboring scope ownership and retained source reconstruction; repeated local names in other scopes remain separate. | An out-of-scope or through-EQU use, collision, accidental anonymous/local rebinding or unsupported reachability claim refuses. Zero xref count alone is insufficient. |
| S4 — new | R6; regroup data operands and insert proven boundary labels; C | Reflow DB/DW/string operands by reviewed format while preserving operand identity, byte order, references, segment and physical extent. | Swapping same-valued operands, splitting a word/string incorrectly, crossing an ORG or dropping a hidden reference fails despite matching aggregate bytes. |
| S5 — extend | R1/R4; create/replace/delete comment and whitespace units; C | Inline/header comments and formatting can change without dummy renames or document writes; invalid source bytes remain exact unless explicitly repaired. | A replacement that consumes a statement, newline or next label, a stale byte preimage, or a comment that injects code refuses. |
| S6 — new | R6/R5; typed recovery hints and controlled regeneration; C/W | Admit configured code/data pointers, entries, inline payloads and data ranges; fixed regeneration shows the full diff and preserves reference PRG and existing authored work. | CPU address used as PRG offset, wrong bank, contradictory hints, arbitrary config execution or regeneration overwriting unrelated edits refuses. |

The service serializes typed expression requests and asks XORcyst to resolve
them. It must not add a consumer assembler parser or evaluator. The confirmed
declaration IDs and selection form the postcondition; byte parity alone cannot
accept an accidentally different binding. A semantically mistaken *requested*
name or constant still requires reviewer judgment: a machine check cannot prove
the author's meaning. Historical wrong-meaning fixtures must expose the decisive
context rather than teach the service an answer key.

S6 may admit only declarative, schema-checked configuration. Shell configuration,
tool selection, policy weakening and permission settings stay operator-owned.
If normal work requires a missing producer fact or grammar, record the exact
XORcyst prerequisite and obtain its separate contract/review. Do not fill it with
source parsing or count the blocked row complete.

## Documents, ledgers and trusted writes

| ID / status | Read and mutation contract; writer / generation | Positive acceptance | Failing-direction acceptance |
| --- | --- | --- | --- |
| D1 — extend | R4; authored document create/update/delete; C | Cover canonical docs, working notes, current project-root docs, authored inventory Markdown and explicitly registered shared docs. Review scattered edits, additions and deletions in both sessions. | Reviews, tool configuration, source, generated files, symlinks, case aliases and canonical-document deletion remain protected; an unregistered shared path refuses. |
| D2 — new | R4/R6; typed authored CSV row create/update/delete; C | Cover blob/format dispositions, policy baseline, extent assertions and proof-debt dispositions; key changes are explicit and duplicate/glob contracts are checked. | Wrong row preimage, duplicate key, wrong file schema, rename breaking a disposition glob or forged evidence/gate output refuses. |
| D3 — new | R2/R4; typed raw-RAM judgments; C/W | Update authored status/name/notes, with address identity and pass context fixed; the existing refresh path regenerates factual columns. | Caller-supplied counts/owners/active flag, mirror conflation, row rekeying or fabricated pass IDs refuses. |
| D4 — extend | R4; scorecard inputs and deferral lifecycle; C/W | Focus/notes and explicit closeout inputs remain usable; a fixed deferral operation can resolve/reopen a row while retaining its prior version and evidence. | Direct gate/KPI edits, whole-file mixed replacement, fabricated new-row greens or alteration of historical closeout rows outside the dedicated writer refuses. |

The ownership manifest is a write boundary, not merely a review label. It must
be complete before widening a path allowlist. File and field ownership is:

| Artifact/content | Permitted writer |
| --- | --- |
| Source units and typed expressions | Service applying C operations only |
| Authored Markdown, including registered project-root/shared docs | Typed document service; each path registered, with preimage and review |
| `data_blob_dispositions.csv`, `data_format_targets.csv`, `policy_baseline.csv`, `data_extent_assertions.csv` | Typed row service using the repository's exact schemas and keys; semantic claims remain reviewable author input |
| `proof_debt_acknowledged.csv` | Typed disposition service; session supplies pass ID; rationale, scope and revisit condition are required and existing proof-debt checks still apply |
| `renames.csv` | Bound-rename transaction; pass ID and old/new names come from the selected edit, reason/confidence are authored |
| `raw_ram_review.csv` | Judgment operation owns `status`, `proposed_symbol`, `notes`; service derives `last_pass_reviewed`; address is the immutable selector; trusted refresh owns `active`, counts and top readers/writers |
| Scorecard | Author supplies only `focus`/`notes`; service derives pass identity and pending/unmeasured seeds; wrappers supply all measured/gate cells |
| `deferrals.csv` | Existing closeout writer appends; new fixed lifecycle writer applies explicit row transitions and retains provenance, with no general replacement route |
| Six generated inventories listed by `service.GENERATED_RELATIVE` and generated pass cache | Their existing fixed generators only; any added artifact needs an explicit writer entry |
| `config/nesrev/` hints and approved declarative configuration | S6 typed service plus existing validators; execution/policy settings remain operator-owned |
| Registered project trace/decoder tools | W2 sandboxed tool workflow; no executable is admitted as an ordinary document |
| Review archives, verdict history, receipts and retained store | Existing handoff, wrapper and retention authorities only |
| Supplied references, ROMs, producer/configuration pins, credentials, Git and unrelated projects | No implementer mutation; operator preparation/trusted application only |

Root/shared documents need path-specific ownership and lock/preimage checks at
application, including overlap with another pass. They are not granted by a
generic `../` escape. Published artifacts carry every admitted path and its
reviewed version. The existing artifact schema/pins must be versioned if new
provenance cannot be represented without ambiguity; old evidence is never
rewritten or opened with weakened identity checks.

## Wrappers, runtime evidence and completion

| ID / status | Read and mutation contract; writer / generation | Positive acceptance | Failing-direction acceptance |
| --- | --- | --- | --- |
| W1 — extend | Next-pass, explicit pass-start, verify/process/docs, inventories, prior reuse, comment audit, recovery and review packet; R/W | Agent receives bounded wrapper evidence and actual diagnostics; pass choice is explicit. Long jobs return a durable job ID/status rather than relying on an expiring bridge call. | Stale next-pass input, inherited environment override, failed gate followed by a successful summary, caller-selected command or dead worker cannot create green results. |
| W2 — new | Registered trace-tool edits, fixed capture/decoding, and media reads; C/E | A sandboxed authored tool consumes issued records/approved runtime inputs; supervisor supplies ROM/emulator inputs and retains logs, screenshots/audio, provenance and failure details. Restart can inspect completed evidence. | Worker source/Git/store/credential reads, network/host escape, verdict writes and child-process escape fail; timeout, incomplete capture, wrong generation/bank or missing dependency cannot be promoted. |
| W3 — retain/extend | Publication, review windows, verdicts, restart and approved local application; C/H | Mixed operations cross a window boundary, reopen after editor deletion, receive repair/reapproval and apply under locks with all canonical gates. | Missing earlier approval, revocation during apply, stale base, dirty/overlapping destination, changed archive or failed export cannot commit or lose evidence; partial-application recovery is documented and tested. |

W2 requires a tested OS boundary on the selected platform, inherited by child
processes, with default-deny source-bearing host access. Disabling a bridge method
or relying on a role string is insufficient. The trusted supervisor may possess
source and emulator inputs; the authored worker receives only the narrow issued
inputs. There is no general host-shell endpoint. Real media must still be
inspectable by both roles. Runtime observations remain distinguishable from
static facts and assisted scenarios from ordinary-input coverage.

Fixed jobs record cancellation, timeout, failure and cleanup explicitly. A
positive emulator failure remains a failure; validated completion followed by
supervisor-initiated signal shutdown follows the existing runner contract.
Supported capture results must be tested against the actual configured emulator,
not just a fake. These requirements do not authorize new game captures here.

## Disposition of the earlier analysis-query work

The spec tip `cb856e558` is an ancestor of implementation tip `e937c92ef`.
Preserve both as source material until extraction is accounted for. Do not merge
the CLI and its legacy bundle adapter wholesale into a second agent interface.

| Earlier capability/contract | Step-2 disposition |
| --- | --- |
| Symbol definition, direct references, source context | Compare against R1; keep useful coverage tests, use current model records and scoped local/anonymous identities |
| RAM access categories and alias proofs | Port into R2 from producer facts; retain direct/indexed/RMW/pointer/unknown distinctions and bank tests |
| Through-EQU and arithmetic/control classification | Reuse relevant R3 cases; do not lose references omitted by an older xref profile |
| Batched queries, unequal page shares, input identity and negative lookup changes | Reuse as R1–R4 boundary cases with generation-pinned continuations and the current wire ceiling |
| Fresh per-invocation assembly and disposal | Keep as historical design context; service generations already have retained certified facts, so do not reassemble on every read |
| Local-label refusal and ad-hoc source excerpts | Superseded by current producer scopes/lexical records; no raw-source escape route |
| Two-second fresh-CLI target | Preserve with that experiment; step-2 service measurements use the separately stated workload/limits below, not a claimed result for the old CLI |
| Agent A/B trials and default-guidance quality claims | Still unperformed; any comparative claim needs its separately authorized, frozen protocol. Functional service rollout is not evidence that the earlier efficiency gate passed |

Before deleting the old branches, produce an extraction ledger listing each old
test/requirement as retained with a new test ID, superseded with a reason, or
explicitly deferred. Preserve their commit IDs and recoverable Git history.
This planning change deletes neither branch.

## Replay and measurement contract

Freeze the concrete input hashes and expected outcomes before implementing the
corresponding operation. Public fixtures use neutral symbols; private replays
remain outside tracked master tooling. The local case manifest separates:

- **H1–H4:** existing classified seed pairs for value-coincidence constants,
  a missed state reader, stale rename prose and a false localization blocker.
  Use them for R3/S2, R2/R3, R4, and R5/S3 respectively. Snapshot availability is
  not a successful replay; recover expectations and review them first.
- **H5–H7:** recorded cases for data extent/representation, mixed ledger/doc
  obligations and the completed service pass. Capture the exact needed
  operations from the record, including deferred work; do not treat a recorded
  debt item as an already approved naming decision.
- **B1:** producer corpus, including the largest source/model and the largest
  reference/instruction inventory. Measure both if they are different sources.
  Preserve bank/segment cases, not only the quickest flat source.
- **B2:** the existing full 64-rename/long-ledger/scattered-document rehearsal,
  plus a mixed-source-edit run spanning more than seven publications. Exercise
  repair, all-window coverage, restart, retained review and disposable application.
- **B3:** neutral adversarial fixtures for wrong bindings, equal values, repeated
  locals/origins, byte/word/string boundaries, ownership, path aliases, failed
  jobs and permissions. Required removed-guard controls must fail independently.

For each replay retain: row IDs, defective/base and corrected/input hashes,
expected records/edits/unknowns, actual requests, all pages, gate results,
resource measurements and removed-guard result. A response that merely matches
another consumer is not an independent oracle. Reviewers must be able to change
the candidate in the bad direction without changing the expected result.

The following are **proposed operating limits to freeze at plan acceptance**,
not measurements or permissions to consume these resources now. Before coding,
measure the unchanged service on the same pinned B1/B2 workloads. If these limits
are infeasible, revise this baseline with the evidence before implementation;
do not relax them after seeing a new implementation's result.

| Measurement | Limit / method |
| --- | --- |
| Serialized bridge response | At most 24 KiB including MCP/JSON escaping. No skipped evidence; partial views name recoverable positions. Check every operation and both session types. |
| Existing workload review volume | At most 1 MiB total on B2's 64-rename case; count all pages and metadata, and no loss of rows/uses/reasons. Added operation content is reported separately. |
| Bounded read page | At most 10 s on an already loaded generation and 120 s including cold integrity checking/model loading; one cold run plus five timed warm runs after warmup, report every run. Jobs exceeding client-call deadlines use status/poll, never an unreported timeout. |
| Complete candidate amendment | At most 300 s from accepted amendment through fresh certification, all required gates and review readiness on B1; five serial runs after one warmup, maximum observed time reported. Do not omit checks to meet it. |
| Affected existing wrappers | Median increase at most 5% on the largest applicable input, following the existing [performance contract](../../PROJECT_CI_PERFORMANCE_PLAN.md#non-regression-requirement). Baseline and changed runs use the same inputs, tools and environment. |
| Temporary disk | At most 2 GiB peak for one candidate plus its before/after review; at most 4 GiB peak for a serial multi-window/corpus campaign. Sample allocated bytes at most 1 s apart; report sampling limits and before/after free blocks. |
| Retained growth | At most 256 MiB per publication and 2 GiB across the eight-publication B2 run, excluding the separately measured once-retained toolchain/base. Count actual retained bytes, not an estimate from compressed input. |
| Capture jobs | Default cap 300 s and 512 MiB output per job; explicit bounded profile required. Job status/cancel returns within 5 s; worker children are gone within 5 s after termination escalation. A cap hit is incomplete evidence. |
| Admission and cleanup | One canonical shared heavy-run lock for both roles/copies. Estimate covers peak allocation plus at least 2 GiB reserve on every affected volume. No hardlinked mutable files. No new scratch checkouts or live children after success, refusal, cancellation or injected crash recovery. |

Retain immutable receipts, pinned inputs/tools and selected artifacts outside
system temporary directories. Do not remove the coordinator, original stores,
fingerprinted source checkouts or old captures as test cleanup. Any reclamation
of prior evidence requires a hash-to-retained-location inventory and verified
restoration first. Prefer lazy restoration of selected states and copy-on-write
where available; do not require a platform-specific clone command for correctness.

## Proposed delivery split and exit gates

Step 2 is too broad for one reviewable implementation PR. Propose three dependent
slices, preserving every row above and the rollout's original completion gates:

1. **2A — source operations and query reuse:** R1–R3, R5–R6 and S1–S5.
   Land typed edit/provenance contracts with neutral controls and private
   defective/corrected replays. Existing D/W operations support the rehearsals;
   missing artifact routes remain explicit, not bypassed by direct edits.
2. **2B — artifact and wrapper coverage:** R4, S6, D1–D4 and W1. Land the full
   ownership manifest, mixed rows, registered shared documents, recovery inputs
   and bounded jobs. Exercise real wrappers and every affected corpus schema.
3. **2C — runtime evidence and integrated acceptance:** W2–W3 and all-row
   regression/rehearsal, with sandbox/capture acceptance and measured limits.
   W2's sandbox feasibility is checked before authored-code execution is enabled.

Each slice needs its own reviewed wire contract, positive and failing-direction
tests, affected wrapper measurements, focused/full regressions, independent
review and green Linux/macOS CI before an authorized merge. Fresh claims name
the tested commit; unchanged earlier evidence is marked carried forward. If a
producer change is needed, its separate reviewed release/pin is a prerequisite.

Step 2 closes only when every applicable row has implementation, positive,
negative and replay/result references; all numeric limits pass; the multi-batch
rehearsal completes through services; and the authorized PRs are merged. An
unsupported operation is an open row. Genuine non-applicability needs specific
evidence; changing the normal-pass scope needs an owner decision. Publish the
remaining census/holdout gaps explicitly rather than calling them complete.

Step 3 remains separate: actual client restrictions, owner-selected model/budget,
an authorized representative real corridor without operator repair hints, and
default launcher rollout. Planning and deterministic tests authorize no real
inference, project pass, release or remote publication. `projects` remains local.
