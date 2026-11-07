# Step 2 operation coverage

Status: scope baseline v4, revised after review of `dac80f116`. No step-2
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
| S1 — retain | R1/R4; bound rename plus typed rename rows; C/W | Global/local/EQU renames preserve all selected uses, unrelated declarations/bindings and ledger prefix, including a 64-name batch. | Independently remove `declarations_renamed`, `every_bound_use_preserved`, `unselected_bindings_preserved`, `unselected_declarations_preserved`, `reference_inventory_preserved` and `no_stale_source_prose`; designated parity-preserving controls must fail. |
| S2 — new | R1/R2/R3; insert an EQU/label, replace a selected expression, remove a proven-unneeded declaration; C | Typed expressions refer to declaration IDs; preview groups every selected occurrence by owner. Cover hardware masks, field offsets, selector offsets, low/high pointers, bounds and label math. | Same-value wrong binding, implicit broad replacement, use-before-scope error, live-declaration deletion and unintended width/encoding changes refuse; untouched bindings remain identical. |
| S3 — new | R1/R5; localize a global label into an explicit scope; C | Re-certify all uses, neighboring scope ownership and retained source reconstruction; repeated local names in other scopes remain separate. | An out-of-scope or through-EQU use, collision, accidental anonymous/local rebinding or unsupported reachability claim refuses. Zero xref count alone is insufficient. |
| S4 — new | R6; regroup data operands and insert proven boundary labels; C | Reflow DB/DW/string operands by reviewed format while preserving operand identity, byte order, references, segment and physical extent. | Swapping same-valued operands, splitting a word/string incorrectly, crossing an ORG or dropping a hidden reference fails despite matching aggregate bytes. |
| S5 — extend | R1/R4; create/replace/delete comment and whitespace units; C | Inline/header comments and formatting can change without dummy renames or document writes; invalid source bytes remain exact unless explicitly repaired. | A replacement that consumes a statement, newline or next label, a stale byte preimage, or a comment that injects code refuses. |
| S6 — new | R6/R5; typed recovery hints plus non-writing `project-regenerate-check` evidence; C/W | Admit configured code/data pointers, entries, inline payloads and data ranges; retain the bounded diff against temporary generator output without replacing authored assembly. | CPU address used as PRG offset, wrong bank, contradictory hints, arbitrary config execution or any write of generated assembly over the authored file refuses. |
| S7 — new | R1/R6; decode data to instructions, or explicitly revert instructions to data, over an exact emitted byte range; C | Preserve bytes, length, segment and every label's byte position; map/rebind all references into the range or refuse. Required S6 hint changes accompany the same candidate. | A changed byte, crossed ORG/bank, referenced label moved off its opcode byte, dangling interior target or hint contradicting the representation refuses. |

The service serializes typed expression requests and asks XORcyst to resolve
them. It must not add a consumer assembler parser or evaluator. The confirmed
declaration IDs and selection form the postcondition; byte parity alone cannot
accept an accidentally different binding. A semantically mistaken *requested*
name or constant still requires reviewer judgment: a machine check cannot prove
the author's meaning. Historical wrong-meaning fixtures must expose the decisive
context rather than teach the service an answer key.

S6 may admit only declarative, schema-checked recovery configuration. Shell
configuration, executable selection and permission settings stay operator-owned;
gate-policy changes have only the dedicated D5–D7 writers below.
`project-regenerate-asm` overwrites the authored file and is not an S6 operation.
`project-regenerate-check` exits zero on ordinary drift: retain and review its
actual hunks, never treat that exit as proof of parity or reconciliation. No
automatic merge of raw generator output into mature source is proposed.

S7 is the in-place recovery route. Its preview includes the original physical
range, byte preimage, new instruction/data records, label positions and every
affected binding. Decoding uses a fixed producer/decoder over retained bytes,
not a consumer parser of assembly text; candidate assembly is re-certified by
XORcyst. An interior reference must still select the same physical byte, even
when the new instruction cannot host a label there; unrepresentable targets
refuse. Bytes and authored units outside the selected range stay unchanged.
Reverting code to data also requires an explicit representation rationale and
review; it is not a way to suppress warnings or improve KPIs. The existing
[parity-safe decode protocol](../../agent_playbook/DATA_RECOVERY.md#orphan-opcode-decode)
and its warning/constantization pre-assessment apply to the whole candidate.

If normal work requires a missing producer fact or grammar, record the exact
XORcyst prerequisite and obtain its separate contract/review. Do not fill it with
source parsing or count the blocked row complete.

## Documents, ledgers and trusted writes

| ID / status | Read and mutation contract; writer / generation | Positive acceptance | Failing-direction acceptance |
| --- | --- | --- | --- |
| D1 — extend | R4; authored document create/update/delete; C | Cover canonical docs, working notes, current project-root docs, authored inventory Markdown and explicitly registered shared docs. Review scattered edits, additions and deletions in both sessions. | Reviews, tool configuration, source, generated files, symlinks, case aliases and canonical-document deletion remain protected; an unregistered shared path refuses. |
| D2 — new | R4/R6; typed authored CSV row create/update/delete; C | Cover blob/format dispositions, policy baseline, extent assertions and proof-debt dispositions; key changes are explicit and duplicate/glob contracts are checked. | Wrong row preimage, duplicate key, wrong file schema, rename breaking a disposition glob or forged evidence/gate output refuses. |
| D3 — new | R2/R4; typed raw-RAM judgments; C/W | Update authored status/name/notes, with address identity and pass context fixed; the existing refresh path regenerates factual columns. | Caller-supplied counts/owners/active flag, mirror conflation, row rekeying or fabricated pass IDs refuses. |
| D4 — extend | R4; scorecard inputs and deferral lifecycle; C/W | Close every open row of the exact subject atomically, changing only status; reopen by appending a new current-pass row with the same subject, preserving all closed rows. Closing evidence lives in the receipt and closing-pass records below. | Closing only a subset of the subject's open rows, editing a closed row, reopening by rewriting one, duplicate `(pass_id, subject)`, direct gate/KPI edits, whole-file mixed replacement or fabricated new-row greens refuses. |
| D5 — new | R4/R5; typed `WARNING_BASELINE.txt` curation from fresh assembler diagnostics; C/W | Add only a current warning with specific rationale; remove entries whose warnings disappear, including through another edit, in the same candidate; rename entries with their warning identity. | A baseline entry for a nonexistent warning, stale entry retained after another edit resolves it, deletion while its warning persists or generic/empty rationale refuses. |
| D6 — new | R4/R5; measured `inventory/kpis.conf` ratchet updates; C/W | Tighten through a fixed calibration writer using current emitted metrics; update its associated rationale comment in the same candidate with a checked preimage, preserving unrelated keys/comments and admitting comment text only; an increase requires the matching reviewer-visible `intentional-kpi-regression:` or `kpi-measurement-change:` marker and measured basis. | Unmarked loosened `MAX_*`, fabricated count, stale metric basis, unknown key, injected shell text, or a rationale-comment edit touching a key line or unrelated comment refuses. |
| D7 — new | R1/R3/R4; typed allowlist entries plus unconditional migration of the constant gate to explicit scope-qualified occurrence sets; C/W | The writer and gate suppress exactly the same reviewed producer occurrences or hardware declarations. Disposition every legacy row and retain before/after counts; no spelled-key fallback. | A new same-key occurrence elsewhere must be counted; a nonexistent/stale site, ambiguous legacy match, wrong value, absent reason or unmigrated key must not suppress a warning/count. |
| D8 — new | R4; declarative runtime questions and schema-checked fixture-data writer under `runtime_evidence_check.py`; C/W | Match subjects, dispositions, trace plans and tracked acceptance/single-signal refusal data atomically; before W2 use only fixed reviewed/committed tool profiles and their registered inert data schemas. | Missing acceptance data or a single-signal refusal for any required signal, untracked fixture, unsupported data schema, fake capture result or executable/command injection refuses. |
| D9 — new | R4; fixed process-friction import/triage operation; W | Existing `process_friction.py` owns `process_friction_receipts.json` and receipt-backed queue blocks; retain source/destination identity and rationale. | Direct receipt edits, forged candidate hash or removal of receipt-backed queue content outside the wrapper refuses. |

The ownership manifest is a write boundary, not merely a review label. Before
any allowlist widens, replace the classifier's unlisted-path `authored` fallback
with refusal. Every admitted path/field needs an explicit owner; a filename
extension alone grants no access. Test an unregistered Markdown, CSV, text and
JSON path through every write route, including case/symlink variants. The rows
below are requirements, not a claim that the current classifier enforces them.
File and field ownership is:

| Artifact/content | Permitted writer |
| --- | --- |
| Source units and typed expressions | Service applying C operations only |
| Authored Markdown, including registered project-root/shared docs | Typed document service; each path registered, with preimage and review |
| `data_blob_dispositions.csv`, `data_format_targets.csv`, `policy_baseline.csv`, `data_extent_assertions.csv` | Typed row service using the repository's exact schemas and keys; semantic claims remain reviewable author input |
| `proof_debt_acknowledged.csv` | Typed disposition service; session supplies pass ID; rationale, scope and revisit condition are required and existing proof-debt checks still apply |
| `renames.csv` | Bound-rename transaction; pass ID and old/new names come from the selected edit, reason/confidence are authored |
| `raw_ram_review.csv` | Judgment operation owns `status`, `proposed_symbol`, `notes`; service derives `last_pass_reviewed`; address is the immutable selector; trusted refresh owns `active`, counts and top readers/writers |
| Scorecard | Direct authored cells are only `focus`/`notes`; service derives pass identity and pending/unmeasured seeds. Typed closeout also accepts author-supplied `REWORK_ITEMS`, which the wrapper records; it is not an independently measured count. Wrappers alone write gate/measurement/result cells |
| `deferrals.csv` | Existing closeout writer appends; dedicated subject-closing writer changes every matching `open` row to `closed` atomically, changing only status; reopening appends a new row with the same subject. Closed rows and original keys are immutable |
| `WARNING_BASELINE.txt` | D5 writer admits only current assembler warnings with rationale and removes every resolved entry in the same candidate |
| `inventory/kpis.conf` | D6 fixed measurement/calibration writer; no generic file edit or client-supplied measurement; increases require the specific current-row marker and reviewed justification |
| `inventory/constant_magic_allowlist.csv`, `inventory/hardware_local_allowlist.txt` | D7 typed writer and migrated gate share explicit producer occurrence/declaration identity and reasons; legacy rows need migration disposition before use |
| `inventory/runtime_evidence.json` | D8 declarative question writer under the existing validator; W2 supervisor supplies any new capture/result artifacts, never an authored success flag |
| Registered runtime-question fixture data paths | D8 schema-checked data writer; typed create/update/delete with preimages, question references and retained bytes. Track fixtures in the isolated candidate before validation; executable or code-bearing fixtures require W2, never D1/D8 |
| `inventory/process_friction_receipts.json` and receipt-backed blocks in `PROCESS_FRICTION.md` | Existing process-friction wrapper only; D1 cannot replace/remove those blocks |
| Six generated inventories listed by `service.GENERATED_RELATIVE` and generated pass cache | Their existing fixed generators only; any added artifact needs an explicit writer entry |
| `config/nesrev/` hints and approved declarative configuration | S6 typed service plus existing validators; execution/policy settings remain operator-owned |
| Registered project trace/decoder tools | W2 sandboxed tool workflow; no executable is admitted as an ordinary document |
| Review archives, verdict history, receipts and retained store | Existing handoff, wrapper and retention authorities only |
| Supplied references, ROMs, producer/configuration pins, credentials, Git and unrelated projects | No implementer mutation; operator preparation/trusted application only |

Root/shared documents need path-specific ownership and lock/preimage checks at
application, including overlap with another pass. They are not granted by a
generic `../` escape. Known shared documents are `projects/PROJECT_DEBT_PLAN.md`
and `projects/PROGRAMMING_STYLE_COMPARISON.md`: D1 grants only the selected
project's registered section, retaining other sections and shared framing.
Changing a shared heading or cross-project section requires a separate registered
scope; it cannot piggyback on a project pass. Published artifacts carry every admitted path and its
reviewed version. The existing artifact schema/pins must be versioned if new
provenance cannot be represented without ambiguity; old evidence is never
rewritten or opened with weakened identity checks.

D5–D7 never accept an edit merely because it makes a gate green. Preserve the
warning/metric/occurrence inputs, previous and proposed policy, rationale and
resulting counts for reviewer inspection. The mature-project D6 writer is new:
`kpi_ratchet_calibrate.py` currently only accepts intake scaffolds. Extend or wrap
its measurement contract explicitly rather than treating it as an existing
mature ratchet endpoint. Tightening writes measured finite values. Loosening
requires the exact metric and final values/reason in the current scorecard notes,
or the old/new measurement basis, following the
[intentional-regression rules](../../agent_playbook/PASS_WORKFLOW.md#intentional-kpi-regressions).
Neither marker authorizes arbitrary thresholds or executable config changes.
Admission checks use producer facts, not assembly-text scans. If these writers
touch a legacy KPI/allowlist parser's feature, its structured-consumer migration
is part of that slice under Tooling Rule One, with wrapper non-regression tests.

D7 unconditionally includes migration of `constant_kpi.sh` suppression matching
and its assembler-fact collection to producer records in 2B. Its existing
`(label, mnemonic, immediate)` keys can match multiple sites, including bare
local names across routines and global-label matches across local blocks.
Keeping that matcher behind a more precise writer is not acceptable. The new
gate and writer share a versioned explicit occurrence-set contract qualified by
source, segment, owner scope and statement/operand identity. Generation-qualified
record IDs and proven one-to-one successor mappings keep approved sites stable
across edits; a new same-key site never joins the set automatically. Missing or
ambiguous mappings refuse rather than rebinding by name/value or widening a set.

Every legacy row receives a recorded migration disposition: one current site
maps with its reason; multiple sites require an explicit reviewed selection and
reason for each; zero sites require retirement with rationale, not a dormant
wildcard. The migrated gate refuses undispositioned legacy rows; it must not
silently treat them as an empty suppression set. Version the
authored schema and update all gate callers/readers together; retain original
rows and before/after match sets in migration evidence, without rewriting old
receipts. Test repeated `@@local` names, global-key fanout and an S2/S7-added
same-key site that must increase the unsuppressed count. Also test no-match rows
and stale mappings. Hardware allowlists must retain their actual declaration
identity rather than borrowing the immediate-key rule. This migration is a D7
completion prerequisite, not a conditional follow-up.

**D7 project migration and activation.**

The gate/schema change belongs on master; real legacy-row dispositions belong
in a separately reviewed **local `projects` commit**, never in the tooling PR.
Prepare that commit and its migration manifest against a pinned project base,
and rehearse the combined tooling/data transition in a disposable checkout
before activating the gate on local projects. The manifest enumerates every
affected project, old row, reviewed occurrence set or retirement, schema version
and gate revision. Project data is not migrated merely because the tooling PR
merged.

Bring in the migrated gate and apply the reviewed disposition commit in the
**same coordinated rebase** of local `projects` onto the new master. No pass or
measurement may start at an intermediate gate-only state. Preflight must check
the gate/schema/disposition identities and refuse a missing or incomplete
migration with `D7_MIGRATION_REQUIRED`, even when a project's KPI headroom would
otherwise hide the missing suppressions. Include the failing-direction test:
rebase onto the migrated gate without the disposition commit, then prove pass
and measurement admission both refuse before running work.

Require `project-verify` to pass for every affected project at the pinned
pre-migration base with its legacy gate and at the combined rebased head with
the migrated gate and data. Retain both results, reference-PRG parity and the
suppressed/active occurrence counts. Suppressed sets and counts must be unchanged
except for explicitly reviewed retirements; no threshold increase, fallback key
matcher or cheaper workload may mask drift. A failed verification, unreviewed
count change or incomplete disposition blocks activation. These are future D7
acceptance checks, not a rebase or project edit authorized by this plan revision.

D8 may create and update synthetic fixture data for an already registered tool
profile, and delete it only when no question in the candidate still refers to
it; older retained versions keep their referenced bytes. The profile pins an
inert data schema and bounded formats/paths; extensions
alone do not make a file safe. Reject code, imports, evaluation directives,
command fields and executable deserialization. A profile without such a schema,
or a new signal needing analyzer code changes, remains open until its separately
reviewed profile/W2 prerequisite; no general file write is implied. Fixture data
is not part of the immutable executable/import closure.

Stage admitted new fixture files in the isolated candidate's Git index before
running the existing tracked-file checks; never stage them in the main checkout
as a validation workaround. Retain and review their hashes, bytes, schema and
question links with the manifest/trace-plan edits. Each question needs acceptance
fixtures plus at least one refusal check naming exactly each required signal as
missing; multi-signal refusal alone cannot cover those signals. Require the
existing validator's coverage checks and execute the registered analyzer's
acceptance/refusal cases through the permitted tool path. Missing one signal's
refusal must fail. Synthetic outcomes test the analyzer, never establish a real
capture or close a runtime gap by themselves.

Deferral row identity remains `(pass_id, subject)`, but the closing operation
selects the exact subject and every currently open row with that subject under
one lock/preimage check. Change only their status, preserving original pass IDs
and all other fields; already-closed rows remain byte-identical. Reject a partial
close or a stale row-set preimage that omits a newly added open row. Record the
closing pass, subject, complete selected keys and before/after row hashes,
resolution rationale and evidence references in the retained operation receipt;
link it from the closing pass's scorecard/notes and review archive. No resolution
column or new ledger schema is introduced.

Reopening appends a new current-pass `open` row with the identical subject and a
revisit condition; an existing key refuses rather than rewriting a closed row.
`deferral_repeat` counts only open rows: a full close reduces that count to zero,
and reopening starts it at one, not at the lifetime number of deferrals. Further
open rows count toward the existing three-strike threshold. The signal's scope
fingerprint still covers the subject's rows, so ledger changes invalidate prior
acknowledgements when the signal recurs. Preserve the existing
[three-strikes contract](../../agent_playbook/PASS_WORKFLOW.md#proof-debt), with no
change to the signal here. Closing/reopening runtime subjects also updates D8
question coverage atomically; it cannot leave the validator's subject sets
inconsistent.

## Wrappers, runtime evidence and completion

| ID / status | Read and mutation contract; writer / generation | Positive acceptance | Failing-direction acceptance |
| --- | --- | --- | --- |
| W1 — extend | Next-pass, explicit pass-start, verify/process/docs, inventories, prior reuse, comment audit, recovery and review packet; R/W | Agent receives bounded wrapper evidence and actual diagnostics; pass choice is explicit. Long jobs return a durable job ID/status. Any analyzer subprocess follows W2, including packet portability and maturity checks; before W2 only the pinned tools below run. | Stale next-pass input, inherited environment override, failed gate followed by a successful summary, substituted analyzer/import, caller-selected command or dead worker cannot create green results. |
| W2 — new | Registered trace-tool edits, fixed capture/decoding, and media reads; C/E | Every process executing project-authored code is isolated, including wrapper-launched analyzers and FCEUX running authored Lua; trusted supervision retains generation-qualified inputs and outputs. | Analyzer and real-emulator Lua source/credential reads are denied; Git/store access, network/host escape, verdict writes and child-process escape fail. Timeout, incomplete capture, wrong generation/bank or missing dependency cannot be promoted. |
| W3 — retain/extend | Publication, review windows, verdicts, restart and approved local application; C/H | Mixed operations cross a window boundary, reopen after editor deletion, receive repair/reapproval and apply under locks with all canonical gates. | Missing earlier approval, revocation during apply, stale base, dirty/overlapping destination, changed archive or failed export cannot commit or lose evidence; partial-application recovery is documented and tested. |

W2 requires a tested OS boundary on the selected platform, inherited by child
processes, with default-deny source-bearing host access. Disabling a bridge method
or relying on a role string is insufficient. The supervisor may possess source
and emulator inputs, but it must not execute candidate-authored code in its own
trust domain. The emulator itself is a W2 worker when it loads authored Lua;
Lua `io` access and its child processes are subject to the same filesystem
boundary. An analyzer launched by `project_pass_review_packet.sh`,
`runtime_evidence_portability.py` or the maturity path in
`runtime_evidence_check.py` is also a worker, regardless of its trusted parent.
A scrubbed environment and timeout do not constitute this boundary.

Before W2 lands, project-tool edits stay disabled. Wrappers may execute only
operator-registered, previously reviewed and committed tool versions, with
their executable/import closure, interpreter, command template and lookup paths
pinned and checked before invocation. Merely committing candidate code does not
make it trusted. D8 can select only those registered profiles and declarative
inputs; it cannot supply a new command or a code-bearing fixture. A changed or
unregistered dependency refuses instead of executing it or skipping the check.
This is a limited bridge using trusted code, not completion of W2. Once W2 lands,
all project analyzers and emulator/Lua execution use it, including reused tools.

The isolated worker receives only its issued records, runtime/media inputs and
output area; no source-bearing checkout, import path or supervisor credential.
Test both a Python analyzer and a Lua script opening source/credential canaries,
with the latter running on the real configured emulator. Exercise the analyzer
through both review-packet and maturity entry points, not only a direct worker
test. There is no general host-shell endpoint. Real media must still be
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

The initial Step 2A draft preceded the concrete replay/workload freeze. Treat it
as provisional: complete and independently review the applicable expectations,
holdouts and mechanical selections before resuming it, and record this sequencing
deviation. Freeze a recorded holdout selection rule before examining its results;
do not backdate the freeze or derive semantic expectations from draft output.

Freeze the concrete input hashes and expected outcomes before implementing the
corresponding operation. Public fixtures use neutral symbols; private replays
remain outside tracked master tooling. The local case manifest separates:

- **H1–H4:** existing classified seed pairs for value-coincidence constants,
  a missed state reader, stale rename prose and a false localization blocker.
  Use them for R3/S2, R2/R3, R4, and R5/S3 respectively. Snapshot availability is
  not a successful replay; recover expectations and review them first.
  Freeze every R6-required H4 source/artifact change and derived expectation,
  with explicit exclusions for the correction commit’s unrelated changes.
  Its 2A result covers the scope proof/preview and localization edit, including
  supporting source/system-doc prose and localization ledger rows. Rework-count
  and R6 wording inputs may use the existing scorecard route in 2A, but must
  preserve its policy audit marker and KPI-regression note until the coupled
  2B candidate: update the marker with D2’s policy-row removal, and remove the
  regression note with D6’s measured KPI write. The full canonical replay needs
  these scorecard changes through the existing route, plus D1’s authored
  inventory-Markdown route, remaining D2’s policy-baseline writer and D6’s
  measured KPI writer in 2B. D6 owns the associated KPI rationale comment as
  well as the value; generated owner/count fields come from their refresh
  wrappers. Add `project-policy-baseline-check` to H4’s full replay and pin
  its exact four pre-existing failures from the corrected snapshot: one missing
  live member, one non-live manifest member and the two resulting off-by-one
  reviewed counts. Retain its nonzero exit and full diagnostics; any added,
  missing or changed diagnostic refuses this historical expectation. This is
  an exact baseline comparison, not a green gate or a waiver for normal
  passes; the standard gates still must pass. An interim source result cannot
  close H4 or imply that its coupled supporting obligations passed.
- **H5–H7:** recorded cases for data extent/representation, mixed ledger/doc
  obligations and the completed service pass. Capture the exact needed
  operations from the record, including deferred work; do not treat a recorded
  debt item as an already approved naming decision.
- **H8:** recorded in-place code recovery with a corrected entry hint and warning
  baseline, for S6/S7/D5. Its exact range and bindings need an independent replay
  expectation before implementation; a historical commit alone is not that test.

The accepted staged step-1 preparation covers H1–H4, the seven classified
holdouts and the concrete M8 publications 1–4, 6 and 8. It does not discharge
H5–H8. Preserve that acceptance separately from the sealed evidence. The
remaining historical cases have these slice assignments and prerequisites:

| Case | Slice and expected coverage | Admission prerequisite |
| --- | --- | --- |
| H5 | 2A: R6 operand/extent evidence, S4 representation, D2 extent/blob rows, and associated S2/S5/current-document edits. 2B: any S6 regeneration-hint evidence and authored inventory-Markdown obligations. | Freeze and independently review both recorded boundary cases, exact retained bytes/operands, reference changes, row preimages and supporting artifacts before resuming R6/S4 or the D2 subset. Keep unrelated historical changes excluded explicitly. |
| H6 | 2B: remaining R4 and D1–D4 mixed artifact obligations, with D8 where a runtime question is required. | Pin the documented unresolved obligations before the corresponding writer work; a recorded debt item is not an approved source rename or semantic answer. Any source edit still needs its own reviewed evidence and the applicable 2A operations. |
| H7 | 2A regression: the existing S1/S5, document/scorecard/closeout and repair workflow; 2C: W3 real-client/integrated acceptance. | Freeze the completed pass's exact changes, repair and retained coverage as deterministic regression expectations before its replay. Preserve the disclosed operator hint; neither the old assisted run nor a deterministic replay counts as a new unassisted inference trial. |
| H8 | 2A: D5 warning curation and R4/R5 diagnostic evidence on pinned before/after snapshots. 2B: S6/S7 code recovery, hint/reference mapping and the full coupled source/artifact replay. | Freeze and independently review the fresh warning identities, rationale rows and exact additions/removals before resuming D5. Use independently materialized historical snapshots for that subset; do not claim the 2A writer performs S6/S7. Freeze the full recovery expectations before those 2B operations. |

R1–R3, R5, S1–S3 and S5 work covered by the accepted H1–H4 expectations may
resume on the approved plan base. R6, S4, the D2 extent/blob subset and D5 stay
paused until the applicable H5/H8 expectation review accepts them. Existing
provisional code does not satisfy this prerequisite. The original H5 case
identities remain fixed; any wider review excerpt corrects the recorded
coverage explicitly rather than silently revising the accepted holdout record.

- **B1-S / B1-R:** the largest source/model and the largest reference/instruction
  inventory in the pinned 23-source corpus, respectively. They are different
  sources; both are mandatory. Preserve their bank/segment cases.
- **B2-N:** the existing full 64-rename/long-ledger/scattered-document rehearsal.
  **B2-M** is the new eight-publication mixed-operation workload below, run on
  B1-S, B1-R and B2-N's source, not a replacement for the large-source checks.
  Exercise repair, all-window coverage, restart, retained review and disposable
  application. B2-M does not run on the unchanged service.
- **B3:** neutral adversarial fixtures for wrong bindings, equal values, repeated
  locals/origins, byte/word/string boundaries, ownership, path aliases, failed
  jobs and permissions. Required removed-guard controls must fail independently.

For each replay retain: row IDs, defective/base and corrected/input hashes,
expected records/edits/unknowns, actual requests, all pages, gate results,
resource measurements and removed-guard result. A response that merely matches
another consumer is not an independent oracle. Reviewers must be able to change
the candidate in the bad direction without changing the expected result.

### Workload identities and edit sizes

The private `WORKLOADS.json` names each source path, project commit and source
hash. B1-S's saved capture is 207,955,484 bytes; B1-R's is 205,025,644 bytes.
These are prior producer artifact sizes, not new resource measurements. B2-N
pins the actual saved rehearsal, including its 64 rename rows and two crosswalk
edits. Public tooling uses neutral workload IDs rather than game fixtures.
Freeze the concrete request/selection manifest before the first timed run and
reuse it unchanged; a failed selection is not permission to pick an easier case.

Baselines measured before D7 use the pinned **legacy gate and legacy project
rows**, and must be labelled that way. After the coordinated D7 rebase and
verification above, re-pin B1-S, B1-R and B2-N to the combined migrated `projects`
commit. Record this as a workload **re-pin**, with old/new commits, gate/schema
identities and the reviewed disposition commit, not a new workload. Preserve
source/reference hashes, selected declarations and use counts, edit sizes and
B2-N's saved requests; map generation-qualified IDs to the same source sites
without bypassing identity checks. Any unrelated input or selection change
returns to workload review. Keep the original baseline receipts; the re-pin
neither resets them nor increases the frozen `g`/`L8` allowance. Post-migration
results identify the new gate/data pairing and the controlled schema differences.

| Workload | Sources; operation and edit size |
| --- | --- |
| N64 | B1-S and B1-R each: 64 distinct eligible global/EQU renames, all their uses, 64 ledger rows with 240-character reasons, exactly the mandatory supporting prose defined below, a separately labelled 256-byte replacement of an existing comment, and one authored document with one changed line near its beginning and one appended line (at most 256 UTF-8 bytes each). Eligibility excludes policy-fixed definitions and mentions requiring an unsupported baseline writer, as defined below; sort by `(-use_count, name, declaration_id)` and take 64, including the most-used eligible declaration. If fewer qualify or the selection exceeds operation/response bounds, stop and revise the workload before timing; do not substitute lower-use symbols. |
| B2-N | Saved 64-name map, 66 uses, 64 reasoned ledger rows, two separated crosswalk edits, scorecard and closeout inputs; reproduce the saved requests rather than reselecting symbols on each run. |
| A64 | On each N64 source and B2-N: prepare a rejected candidate by also adding a document line naming a nonexistent symbol, then amend by removing that line while retaining the complete intended edit batch. Time the repair transaction through fresh validation and review readiness; initial setup/failure is separately measured and its disk remains counted until cleanup. |
| M8 | B2-M on each of the three sources: publication 1 repeats N64/B2-N; 2 inserts 8 declarations and replaces 16 expressions; 3 localizes 8 labels; 4 reflows 8 ranges of 16 operands; 5 changes representation of four 16-byte ranges with matching hints; 6 edits 4 comment/layout units and two 256-byte document regions; 7 updates 64 typed ledger/policy rows including a runtime-question/deferral pair using a fixed tool profile; 8 repairs one expression, one comment and one document region. Each includes necessary supporting artifact rows and scorecard/closeout inputs, enumerated separately in the frozen request manifest; the existing 64-rename cap is unchanged. Freeze valid parity-preserving mechanical selections and supporting obligations for publications 1–4, 6 and 8 before resuming 2A, together with the mechanical eligibility, ordering, counts/sizes and no-substitution rules below for publications 5 and 7. Freeze publication 5’s concrete mechanical selections first, before S6/S7 implementation; then freeze publication 7’s against the independently materialized, certified post-6 state before its remaining D2/D3/D8 writers are implemented, with D6/D7 prerequisites explicit if policy changes require them. Its new open deferral uses the existing closeout append, not D4’s new lifecycle writer. The complete eight-publication manifest must be frozen and preflighted before integrated M8 timing; partial slice checks are not full M8 acceptance. Include a refused attempt/repair, window continuation and reopened application. An unrepresentable workload remains a plan issue, not a silently skipped operation. |
| CAP | One fixed neutral ROM/capture fixture per supported real emulator/backend, with a pinned no-op 16-address watch logger for 3,600 frames and at most 512 MiB output; separate malicious analyzer/Lua canaries attempt source/credential reads. Repeat under the same supervisor on B1-S, B1-R and B2-N session roots to test isolation from each source tree. No gameplay or inference is implied. |

### Mechanical rules fixed before resuming 2A

Freeze these rules together with the step-1 selections, before any new-operation
service result or timing. Freeze publication 5's concrete mechanical selection
first, using the original pinned native models and project artifacts, mapped
through recorded edit provenance. Review the S6/S7 wire contracts before building
the post-6 fixture. Its representation and reference spellings must follow those
contracts, whose hashes are recorded; the fixture cannot invent a different form.
Then independently materialize the frozen publications 1–6 as a fixture and
certify that complete state with the pinned producer. Resolve and freeze
publication 7 against that post-6 native model and
artifact state, before implementing its remaining D2/D3/D8 writers. Record its
source/artifact hashes, native model identity and the complete edit mapping from
the original inputs. No service implementation result or timing chooses the
state or selections. A publication-5 refusal stops this sequence for review;
publication 7 may not use an alternative state. Retain the full eligible ranking
and every exclusion with its native/artifact reason.

**Publication 5 (S6/S7):** enumerate sixteen-byte windows of consecutive native
instruction emissions. Each begins at an instruction's opcode byte, ends at a
complete instruction boundary, contains no data emission, belongs to exactly
one segment and has contiguous physical output offsets. The mechanical change
is instruction-to-data representation with the same bytes and label positions.
Keep every bound reference into or out of the window in the selection record;
an unsupported reference mapping is a refusal, not an eligibility exclusion.
Sort by physical output start, then segment ordinal in the native segment array,
then source byte start and native syntax ID. Greedily take the first four
non-overlapping eligible windows, exactly sixteen bytes each.

Exclude any window overlapping a frozen site of publications 1–4, 6 or 8. The
protected set includes declaration/use/expression spans, enclosing emitting
records, zero-width insertion anchors and selected comment/layout units, with
their source-file identities and segment/output positions. Preserve both lexical
and emitted-range protection when mapping sites through earlier publications.
Publication 5 may not move, consume or rewrite those sites. If four windows do
not exist, return the workload to review; do not reselect publications 6 or 8.

Only the S6 hint schema/serialization and S7's representation/reference mapping
await their wire contracts. Those contracts must describe how to represent the
already ranked windows, not introduce new eligibility exceptions. An impossible
mapping, contradictory hint or failed gate returns the workload to review with
the selected windows retained. There is no alternate direction or later/easier
window substituted after refusal.

**Publication 7 (remaining D2, D3 raw-RAM judgments and D8, plus D6/D7 if policy
changes become necessary):** choose 62 existing authored rows plus one runtime question and its
one new open deferral, for exactly 64 primary typed records. Fixtures and any
mandatory supporting rows are counted separately. Existing-row candidates are
from `data_format_targets.csv`, `policy_baseline.csv`,
`proof_debt_acknowledged.csv` and `raw_ram_review.csv`, using the pinned schemas'
exact keys. Here and for the question below, "current native" means the certified
post-publication-6 fixture state, not the original model or an arbitrary live
head. A candidate must resolve to its native declaration(s), a native
scope, or an assembler-reported RAM access: family/glob keys match native
declarations; symbol keys select native declarations; a proof-debt scope must
explicitly name such a declaration/scope; an address key must be observed in
native memory-access facts. Instruction access sites converted to data by
publication 5 are excluded from occurrence sets and cannot establish a row's
address binding. Record each removed site's original native identity,
segment/output position and containing publication-5 range, including any row
that becomes ineligible as a result. No source-text interpretation supplies this
binding. Record the complete resolved occurrence set, not just an equal-valued
symbol. D3 owns authored raw-RAM judgments; the existing refresh path owns their
factual columns.

Exclude row keys already selected for mutation/deletion by the frozen earlier
publications, and generated fields, history and wrapper-owned rows. Sort by
project-relative artifact path, then the exact schema key as UTF-8 bytes; take
the first 62. Append the same fixed sentence, `Mechanical acceptance fixture;
no semantic disposition is changed.`, to the row's authored evidence/rationale/
reason/notes field respectively. Keep key, disposition and other authored fields
unchanged; wrappers derive their own factual fields. Fewer than 62 eligible rows
or a rejected selected row is a workload refusal, not permission to skip it.

For the question/deferral pair, enumerate native direct internal-RAM addresses
below `$0800` with at least one exact read and one exact write; exclude indexed
potential-only and unresolved-indirect destinations. Sort by numeric address,
then segment ordinal, physical offset and syntax ID of the first writer; choose
the first eligible post-6 address and retain all remaining read/write identities.
For that address, also retain the pre-publication-5 occurrence set and the exact
sites removed by publication 5, linked to the frozen ranges. Record addresses
that lose read/write eligibility for that reason; do not reconstruct removed
instruction accesses from their data bytes. Publication 7 cannot change the
frozen publication-5 ranges to recover a preferred address or occurrence. This is a
mechanical evidence fixture and makes no gameplay conclusion. Use the fixed
subject `m8-runtime-fixture` and exactly one new open runtime deferral. Keep it
open unless a separately admitted capture supplies the required evidence. Append
it through the existing typed `closeout.deferrals` route and trusted closeout
writer, with the current pass identity and exact deferral preimage; this workload
does not require D4's new subject-closing/reopening writer. The D8 question and
its validated fixture data accompany that append in the same candidate. A
conflicting existing subject/current-pass row is a refusal, not permission to
rewrite history or silently invoke a different lifecycle operation.

The D8 contract must fix the question/fixture schema, required signal names and
CLI adapter before its implementation. The tool profile must already be
reviewed and committed, support that schema and the selected native sites, and
have acceptance data plus one single-signal refusal fixture per required signal.
Order compatible profiles by repository-relative entry-point path, then closure
hash, and take the first; pin its full executable/import closure. If none is
available, return to review instead of inventing an easier question or analyzer.
New executable logic remains disabled until W2 and needs its separately frozen
expectations before implementation. No real capture or inference is authorized
by this selection rule.

No KPI or allowlist relaxation is part of the mechanical row mutation. If a
selected record or its supporting obligations require D6/D7, record that explicit
dependency and return to workload review; do not change the row selection to
avoid it. The D7 project/gate migration and re-pin requirements remain intact.

For either publication, cost, use count, response volume and observed performance
are never exclusion reasons. A later rule change follows the existing correction
procedure: preserve the previous rules/selections and any failed packet, retain
the old/new diff, and obtain review before trying the replacement. The early
whole-M8 representability check is deferred, not claimed complete. All eight
publications, their supporting obligations and the frozen limits still apply.

The frozen publication-3 instances can have supporting remaining-D2 policy-
baseline obligations. Such rows must be frozen with the source selections;
they are not silently added to 2A or omitted from a candidate. Where needed,
the full publication-3 service run remains open until the corresponding 2B
writer is available. Canonical preflight of independently materialized
fixtures is still required before resuming 2A; it uses unchanged wrappers
and does not claim new-service acceptance. Preserve the selections and
record the dependency, rather than substituting labels.

The frozen checker must refuse every count other than 8 declarations,
16 expression sites, 8 localized labels, 8 data ranges and 4 layout units.
The r3 proposal selected only 6 of 8 B2-N localizations; the r4 complete-
group rule reaches 8 and adds two- and three-label groups. Retain the
r3/r4 selection diff. That rule correction preceded service execution
against these selections and is not evidence that the draft supports them.


For N64, derive `use_count` from all producer-bound references, and retain the
eligible ranking, excluded declarations with concrete policy or unsupported-writer reasons,
selected IDs and each selected use count in the frozen request manifest. Assert
that the highest-use eligible declaration is included and that no lower-ranked
selection displaced a higher-ranked eligible one. Preview/readiness time,
temporary disk and retained growth use this same high-use edit set. B2-N stays
unchanged as the small existing review-volume regression.

Define policy-fixed from the unchanged `scripts/check_symbol_naming.py`, not a
handwritten list of failures. Apply the checker's rules to the mechanically
renamed definition of every declaration in each source's whole ranking and
record the checker hash, proposed spelling and actual refusal for each exclusion.
In particular, its canonical hardware-register rule requires the canonical
spelling for a direct `$XXXX` EQU at an address in
`CANONICAL_HARDWARE_REGISTERS`; its PPUCTRL pattern-table rule requires the
canonical spelling for matching `$08`/`$10` bit constants. Use producer spans
to select and rename the definition; the unchanged checker supplies naming
policy. Do not recover assembler facts with a new source parser. Cost and use
count are never exclusion reasons. Preserve the previous ranking, failed packet
and old/new selection diff when applying a reviewed eligibility correction.

Mandatory supporting prose is exactly the current-prose mentions of the
selected old names reported by the unchanged service's stale-prose obligation,
including its source-comment records and current authored-document mentions.
Freeze those mention identities and the edits that discharge them; refuse an
extra or missing supporting item. Do not substitute the harness's independent
token sweep for the service's obligation set. A mention requiring an unsupported
writer excludes its declaration with a concrete reason. Label the fixed padding
comment and two-region document fixture separately, even if a document also
needs supporting edits. Retain the exact before/after bytes, operation counts
and byte counts for supporting prose and fixtures, and include all their costs
in every measurement.

Before constructing A64's deliberate failure, validate the complete intended
batch through `project-inventory`, `project-verify`, `project-process-check`,
`project-docs-check` and `project-pass-closeout` on the unchanged service and
legacy gate. Retain each actual result and duration as untimed preflight evidence,
outside the acceptance timing samples. Preview acceptance alone is insufficient.
Any refusal returns to workload review; do not inject the deliberate defect or
silently change the selected batch to hide it.

For A64, final verification includes `project-inventory`, `project-verify`,
`project-process-check` and `project-docs-check`, each with its actual exit and
duration. The required `project-pass-closeout` invocation is included too;
its summary is not a substitute for the four named gate results. Start the
repair timer immediately before submitting the first amendment/repair preview
request, including that request's execution and response. Continue through
confirmation, copying, certification, gates and review readiness as defined
below. Report preview time separately as well. Publication and reopened review
are separately timed and included in disk measurements.

For the 300-second amendment limit, review readiness ends when the validated,
published generation's first metadata page is served and exposes the complete
review-page inventory. Exclude the separately timed publication and base-export
work. Sequential delivery of every page is a separate pagination measurement,
not part of this readiness timer. Nevertheless, the sample is accepted only
after every required page has been retrieved with complete coverage and within
the response bounds: a metadata page alone never proves success, and an unreadable
later page invalidates the sample. Report readiness, complete pagination and
reopened review separately; do not hide partial pagination behind the readiness
result. An unreadable required page is a workload failure, not an environmental
invalidity eligible for the repeats below.

### Declared baseline conditions and sample validity

The owner has confirmed AC power, lid open, full wake held throughout the
campaign with `caffeinate -dims`, and no system sleep. The 300-second claim is
limited to those conditions; unattended lid-closed operation requires a
separately declared series. Run one fresh A64 warmup and five serial measured
runs on B1-R, then B1-S, then B2-N. Cooldowns between runs are allowed and are
recorded separately. Preserve earlier series and failures without merging their
samples into this series or changing their original verdicts.

Before each timed sample, observe the kernel thermal budget at its unlimited
value for at least 60 continuous seconds. Record the wait, the raw thermal
events establishing the state, and the machine-specific unlimited value. Unknown
state, missing telemetry or a dead collector prevents admission; absence of a
new log message alone does not establish unlimited state. Thermal limiting that
begins after a valid start is recorded and the run still counts, however slow.

For each sample retain wall-clock timestamps, `time.monotonic()` (awake time on
this host), and a sleep-inclusive clock (`mach_continuous_time` on macOS), with
start/end snapshots and phase boundaries. Use the sleep-inclusive clock for
elapsed limits and sampling gaps; report awake and wall durations alongside it.
Stream the kernel's `Thermal Budget` messages. Record lid, AC/battery and full-wake
state at start/end and monitor transitions throughout, retaining the observation
intervals and power-event log. Record load average. For every gate child process,
including the closeout and regular gates inside the bridge, record before/after
`resource.getrusage(RUSAGE_CHILDREN)` user/system CPU deltas in its waiting
parent, alongside the three clocks. A benchmark-parent reading while its bridge
is still alive is not a substitute for the gate's child accounting. This is
harness instrumentation only; service, gate and workload bytes stay pinned.

Apply these environmental validity rules to fast and slow samples alike. A
sample is invalid only when its start condition was violated, sleep-inclusive
and monotonic elapsed times diverge by more than 1 second, or lid/power state
changes during it (including loss of full wake). Preserve the complete invalid
attempt and its reason. Allow at most two invalid replacement attempts per
workload across its timed phases; a third invalid attempt stops the campaign
for review. A valid readiness result over 300 seconds stops for review, even if
thermal limiting developed during the run. Evaluate validity at the readiness
endpoint before handling a timing failure, so a later event cannot erase one.
For successful readiness, continue monitoring through pagination and retained
review. Missing measurement evidence or a sampling gap over 1 second without
sleep stops for review as an instrumentation failure; it is not another reason
to discard a slow result or consume an environmental repeat.

Earlier B1 read scans may carry forward only with unchanged input/reader hashes,
labelled as prior-protocol awake-time observations rather than new measurements
under these conditions. Correct the old report alongside its immutable packet:
the B1-R scan spans about 19,988 seconds of wall time versus 17,704.6 seconds
awake, including three sleeps; the cause of its cost was not measured. Do not
attribute that cost to Q04 recomputation or thermal state as an established
cause. B2-N's read scan and every future timed run use the new instrumentation
and validity rules. Earlier publication-growth observations remain in the
conservative maximum for `g`; neither `g` nor `L8` is frozen until the required
fresh series and checks complete.

Read workloads edit zero bytes. On **each** B1-S, B1-R and B2-N source, enumerate
all pages of the following fixed request sets. Keep the largest serialized page
for every listed view/subtype, not just the largest page across all queries.
Use maximum supported page limits within the wire contract, retaining all
continuations; refusal to expose required evidence is a failure, not a fast read.

| Row | Request set / page-size workload |
| --- | --- |
| R1 | All declarations via inspect and symbols/records/uses/comments navigation; 40 records per navigation request, including the maximum-use declaration and longest lexical block. |
| R2 | All producer-observed RAM operand addresses and eligible declarations, for every access kind and alias/unknown category; 40 returned sites per page. |
| R3 | Every EQU's Q04 context (64 uses per page) and every statement's outgoing control/data edges (40 edges per page), including through-EQU chains. |
| R4 | Q09 for the workload's full 64-name selection (40 mentions per page), every admitted document (80 lines per page), and every typed artifact view (40 rows per page). |
| R5 | Each named scope/unused/prior-reuse/policy view, paged at 40 evidence records; prior reuse compares the two pinned B1 sources, and B2-N compares with B1-S. Wrapper production time is separate from serving its recorded report. |
| R6 | Every data declaration's operand/extent/pointer view (40 operands per page), and fixed decoding of each selected range up to 4,096 bytes per input chunk; include banked/repeated-origin cases. |

The unchanged service cannot execute new R operations or M8. Record those cells
as unavailable, measure only existing routes for their baseline, and run the
full fixed request sets as the new routes land. Do not disguise a mock/new query
implementation as an unchanged-service measurement. All rows still have fixed
acceptance limits. One cold process run and five warm runs after a warmup are
required for each selected largest page in both live and retained sessions;
**every** run must pass its limit. Report cold/warm and service/wrapper costs
separately, with no averaging away a slow page.

### Proposed operating limits and freeze order

These are proposed limits and a fixed derivation rule, not measured results.
After plan re-review and owner agreement, benchmark the unchanged service before
2A. If its supported workloads fail, revise the plan from that evidence before
implementation. Record input/tool/environment identities and all samples.

| Measurement | Source / operation | Limit / method |
| --- | --- | --- |
| Serialized response | Every R-row request above, A64 review, M8 and CAP status/media metadata on all three roots | At most 24 KiB including MCP/JSON escaping. No skipped evidence; partial views name recoverable positions. Check both session types. |
| Review volume | B2-N's exact 64-rename batch | At most 1 MiB across all pages and metadata, preserving all rows/uses/reasons. Measure N64/M8 volumes too; do not substitute their different content for this regression. |
| Read latency | Each R row's largest page for each view/subtype on B1-S, B1-R and B2-N | At most 10 s warm and 120 s cold, including integrity checking/loading and serialization. Every run passes. Long jobs use status/poll when the client deadline is shorter. |
| Full-amend latency | A64 on B1-S, B1-R and B2-N, with the exact gate set above | At most 300 s per run. One warmup then five serial measured runs from equivalent rejected-candidate snapshots; report all and the maximum. Include mandatory policy/runtime validation, not a reduced gate profile. |
| Existing wrappers | Each affected fixed wrapper on both B1 extremes, and B2-N if it has an additional affected path | Median increase at most 5% under the existing [performance contract](../../PROJECT_CI_PERFORMANCE_PLAN.md#non-regression-requirement). Compare identical source/edit/tool inputs; no claim from a different workload or skipped analyzer. |
| Temporary disk | A64 validation, publication and simultaneous before/after retained review, separately on B1-S, B1-R and B2-N; then M8 on each | At most 2 GiB peak per A64 run; at most 4 GiB per serial M8/corpus campaign. Include editor checkouts, failed attempts, captures, stores' staging files and restored caches. Use an independent sampler process at a nominal period of at most 0.5 s, also sampling allocation/phase boundaries; reject any run with an actual sampling gap over 1.0 s. Report sampling limits and raw before/after free blocks. |
| Retained growth | N64/B2-N publication on each of B1-S, B1-R and B2-N; then every publication and total M8 on each | At most 256 MiB per publication; total M8 must fit the frozen derived limit below and 2 GiB. Measure actual store-byte growth including receipts/tickets/blobs, not model-file size. Retain the toolchain and unedited base once before taking the publication-delta baseline; report that bootstrap separately. Use equivalent fresh stores for repeated measurements. |
| Capture limits | CAP positive/control jobs and malicious canaries on each configured real backend and all three session roots | Cap 300 s and 512 MiB output per job; status/cancel within 5 s, descendants gone within 5 s of termination escalation. A cap hit is incomplete evidence, not success. |
| Admission/cleanup | Every workload above, including injected failure/cancellation/recovery | One canonical shared heavy-run lock for both roles/copies. Estimate covers peak allocation plus 2 GiB reserve on every affected volume. No hardlinked mutable files, leftover scratch checkouts or live children. |

Freeze the M8 growth rule **now**, rather than pretending M8 can be baselined:
let `g` be the maximum measured per-publication retained growth across all
unchanged-service N64/B2-N runs on the three sources. Set
`L8 = ceil_to_MiB(8 * 1.25 * g)`: eight publications plus a 25% margin for new
edit/provenance kinds. The baseline report must substitute measured `g`, record
the numeric `L8`, and freeze it before 2A. If `L8` exceeds 2 GiB, or a mandatory
baseline is unavailable, scope/limits return to plan review before coding.
No new-operation result can be used to enlarge that bound retrospectively.
After implementation, every M8 source must fit both `L8` and the per-publication
limit; the 25% is a budget allowance, not a prediction of compression savings.

Retain immutable receipts, pinned inputs/tools and selected artifacts outside
system temporary directories. Do not remove the coordinator, original stores,
fingerprinted source checkouts or old captures as test cleanup. Any reclamation
of prior evidence requires a hash-to-retained-location inventory and verified
restoration first. Prefer lazy restoration of selected states and copy-on-write
where available; do not require a platform-specific clone command for correctness.

## Accepted unchanged-service baseline

The independent review accepted the completed baseline on 2026-11-06. The
sealed packet manifest is SHA-256
`5cc025a4b8bc7f0499632d674bc515bf4944385164f8bedea1d29c2ed61dd6ed`;
the separate acceptance record is SHA-256
`ee85e00de7ffafd557c7241df0375703703e073833d96edf0fb98294e74df82e`.
Neither record changes the earlier failed or stopped series.

The frozen values are **g = 18,595,840 bytes** and
**L8 = 186,646,528 bytes (178 MiB)**. New-operation measurements cannot raise
these limits. Every M8 source must satisfy L8 as well as the separate 256 MiB
per-publication limit. The 300-second readiness claim applies only to the
AC-powered, lid-open, fully awake conditions above. Full pagination remains a
separate timed and verified requirement.

The owner authorized local Step 2A implementation after baseline acceptance.
Project migration, inference, publication and rollout remain separate decisions.

## Proposed delivery split and exit gates

Step 2 is too broad for one reviewable implementation PR. Propose three dependent
slices, preserving every row above and the rollout's original completion gates:

1. **2A — source operations and query reuse, with required artifact writers:**
   R1–R3, R5–R6, S1–S5, D5 warning curation, and the extent-assertion/blob-disposition
   parts of D2 with their R4 reads. The default-deny ownership manifest lands
   first. Boundary-label insertion/reflow changes its extent/disposition rows in
   the same candidate; localization/declaration changes curate warnings before
   canonical verification. Cases requiring a new allowlist or KPI change remain
   explicitly open until D6/D7 in 2B; S2/S3 are not called complete for those cases.
2. **2B — remaining artifact and wrapper coverage:** remaining R4/D2, S6–S7,
   D1/D3/D4/D6–D9 and W1. Land typed recovery with in-place decode, registered
   shared documents, gate-policy writers and bounded jobs. D7 includes the gate
   matcher/schema migration and every legacy-row disposition, with the reviewed
   local-project commit, coordinated rebase, verification and workload re-pin
   above as activation prerequisites. D8 includes both
   declarative questions and schema-checked fixture data, limited to pinned
   reviewed/committed tool profiles until W2. Runtime deferrals/dispositions,
   manifest/trace-plan references and tracked fixture data change atomically;
   unsupported fixture formats or new analyzer logic remain open.
   Before their corresponding work, freeze and review H6's mixed obligations,
   H5's deferred support and H8's full recovery expectation. Freeze publication
   5's concrete selection before S6/S7 implementation. After reviewing those
   wire contracts, materialize the post-6 fixture and freeze publication 7
   before its remaining D2/D3/D8 work, with D6/D7 prerequisites as specified
   above. These deferred freezes are required 2B checklist items, not completed
   step-1 work.
3. **2C — runtime evidence and integrated acceptance:** W2–W3 and all-row
   regression/rehearsal, with sandbox/capture acceptance and measured limits.
   W2's sandbox feasibility is checked before authored-code execution is enabled.

The dependencies are explicit: S4 needs D2's extent/disposition subset in 2A;
S2/S3 need D5 there and D6/D7 for policy-changing cases in 2B; S7 needs S6 plus
D5–D7 in 2B. D2/D4 runtime transitions need D8 in 2B. W1 packet/maturity checks
may run the restricted committed-tool profiles before 2C; any case needing a new
or changed analyzer, Lua runner, imported helper or executable fixture stays
open until W2. A manifest path cannot bypass that dependency. 2C must then test
the real packet/maturity/emulator entry points through W2, not only a standalone
sandbox probe. Interim slice acceptance never claims these open cases passed.

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
