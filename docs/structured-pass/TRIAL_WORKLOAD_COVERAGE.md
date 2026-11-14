# Retained trial workload: structured-operation coverage

Date: 14 November 2026. Status: offline assessment; implementation and live
work are not authorized by this document. Service baseline:
`ccaeeeae5fe7f16e1dc7a0b4a235b437255f86c1`.

**Follow-up, 14 November 2026:** the subsequently authorized
[feasibility checkpoint is complete](FEASIBILITY_DECISION.md). App Sandbox
worked for the declared worker runtimes, and the reviewer/media smoke passed;
the reviewer's hook-disabled protection remains open. Typed search is the next
service slice to propose, with implementation still subject to owner approval.
The census and recommendation below preserve the assessment that preceded the
checkpoint; they are not a statement that the investigation remains unstarted.

## Assessment at the recorded service baseline

**Search is a material missing capability, and workflow jobs alone cannot
support the next unscripted review.** The first map overstated existing search
coverage and justified a job interface partly by reuse in a worker whose
feasibility is still open. This revision withdraws that ordering.

I recommend **the already-planned early confinement feasibility checkpoint
before committing to a worker-dependent interface**. It must include the actual
reviewer client and reference-media path, not just the Codex implementer. Typed
instruction and document search is the next independent service slice to scope;
its offline design can proceed alongside that checkpoint. Neither is authorized
here. Workflow jobs retain independent value, but their order must be chosen
against the complete path below, not speculative W2 interface reuse.

## Census and interpretation

The census covers all eight retained transcripts: implementer and reviewer in
each of four trial segments. It contains **784 distinct native tool requests**:
501 from the implementer and 283 from the reviewer. The first two reviewer
transcripts contain no tool requests. Every counted request has a result
record; a result can be an error, refusal or incomplete output.

| Segment | Implementer | Reviewer | Total |
| --- | ---: | ---: | ---: |
| 1 | 82 | 0 | 82 |
| 2 | 2 | 0 | 2 |
| 3 | 99 | 141 | 240 |
| 4 | 318 | 142 | 460 |
| Total | 501 | 283 | 784 |

Count actual assistant call records, keyed by native call ID. Exclude replayed
request blobs, attachments, compaction history and result records. The
implementer used 499 `exec` cells and two `wait` calls; many cells contain
several commands, patches or image reads. The reviewer used 126 `Read`, 136
`Bash`, 13 `Write` and eight `Edit` calls. These units are not directly
comparable across roles and do not predict MCP call counts, tokens or time.

The [per-call map](TRIAL_WORKLOAD_COVERAGE.csv) gives every request an anonymous
ID, source line, capability set and disposition. Private supporting records
retain the original call ID, arguments, results, source paths, full hashes and
annotation script. No transcript contents or project identities belong in this
shared assessment.

This is **manual intent mapping against code, not a replay**. “Existing” now
requires a practical route to the requested fact or effect. For inspection,
the audit ceiling is **eight service requests per independently named lookup
or bounded inspection question, including selection and result pages**. A cell
can contain several independent questions; a range sweep or one predicate over
a corpus cannot be split into hundreds of “questions” to fit this ceiling.
A named symbol's references and another symbol's references are distinct
lookups; every address in one requested RAM range is not.

Eight is an explicit assessment threshold, not a service guarantee or an
observed cost. If a route needs a larger scan, lacks the selection predicate,
or has no established bound, record a gap. Reading a requested, small document
or known source block is different from paging through whole files to emulate
a missing search. **A missing search predicate is a gap even when the present
file happens to be short.** Truncated output never establishes absence.
The unchanged existing rows remain contract mappings, conditional on admitted
inputs and response size; this audit did not execute them or measure service
pagination. Acceptance must check their budgets against retained inputs and
reclassify any overflow, rather than silently increase this ceiling.

Reformulation must preserve the evidence obligation. It does not mean the old
command would execute, the model would choose the route unaided, or a whole
pass is supported. The current-project profile requires source and reference
pins, a pass plan and four green baseline gates before admission. Initial
recovery cannot borrow that prerequisite.

Each call retains all annotated needs. Its single disposition is the most
restrictive: unplanned gap, then 2C, then 2B, then existing. A call is
unnecessary only when its whole purpose moves to service/coordinator-owned
transport or checkout bookkeeping. Thus a source read bundled with a capture
does not count as wholly covered. Failed and repeated requests remain in the
denominator. Counts describe this workload, including its detours.

| Disposition | Implementer | Reviewer | Total |
| --- | ---: | ---: | ---: |
| Existing route, conditional on admission and the practical bound | 125 | 151 | 276 |
| Planned in 2B | 70 | 36 | 106 |
| Planned in 2C | 54 | 24 | 78 |
| Unplanned capability/input gap | 130 | 56 | 186 |
| Unnecessary as a native agent operation | 122 | 16 | 138 |

The last row includes staging, commits, polling and ordinary-checkout handoff
troubleshooting. The service still has to perform and retain publication,
cleanup and job outcomes. The row is not a claim that 138 calls' worth of cost
or owner effort would disappear.

## What already exists

The checklist's original `new` labels describe its earlier baseline. Read them
alongside the delivery split: 2A is implemented. Code inspection used the
[bridge declaration](../../scripts/structured_pass/bridge.py),
[source navigation](../../scripts/structured_pass/navigation.py),
[evidence views](../../scripts/structured_pass/evidence_views.py),
[read and review service](../../scripts/structured_pass/rename_service.py),
[ownership registry](../../scripts/structured_pass/ownership.py) and
[current-project admission](../../scripts/structured_pass/current_project.py).

| Map key | Implemented substitution | Checklist rows |
| --- | --- | --- |
| G | `guidance` for root instructions and the seven admitted playbooks | R4 |
| S | `inspect`, `navigate`, `query`, RAM/outgoing/scope/expression/data evidence; fixed byte and little-endian word decoders | R1–R3, R5–R6 |
| D | Registered authored documents, current scorecard/deferrals, Q09 and retained review changes with identities/hashes | R4, D1 |
| E | Typed source/comment/data edits, registered document edits and scorecard/closeout inputs | S1–S5, D1, D4 |
| A | Extent/blob/warning rows and their writers; bound rename-ledger changes | R4, D2, D5 |
| V | Candidate validation, canonical gate status/parity and bounded failure evidence | W1/W3, implemented subset |
| H | Status, review reports, verdicts, reready and closeout; file/CLI transport is reformulated | W3, implemented subset |
| R | Claude reviewer `Read` of explicitly selected, copied reference media | Admitted client route; not general filesystem access |
| N | Native transport and checkout bookkeeping owned by the service/coordinator | No new agent operation |

A named source block, declared-symbol use lookup, single-address RAM query or
Q09 identifier check can use existing routes. `navigate.contains` filters only
symbol names and comment text; `uses` requires a declared symbol. The `ram`
view takes one address. Neither `document` nor `guidance` has content search.
Those are not substitutes for instruction-pattern scans, immediate-value
queries, raw-address range sweeps or free-text document searches.

Packet reads are classified by their requested sections: source/document diffs
often map to existing review pages, while generated findings and runtime-tool
changes need more. Known gate status/head/hash fields map to structured
metadata, not a new packet-text search. A full packet is not automatically
covered because part of it is.

### Search correction across both roles

The second read included native grep/rg, awk, instruction-JSON filters, dynamic
command arrays and whole-source fetches. It did not infer semantics from tool
names alone. The private annotations retain each correction and its reason;
the first map is preserved there for comparison.

| Need | Previously credited examples now marked as gaps | Required route |
| --- | --- | --- |
| Instruction/sequence scans | R3-063, R3-067; also R3-068 and implementer C1-031 | Query native xasm instruction records; return neighboring records when needed. |
| Immediate operands | R4-036, R4-044; implementer C3-022, C3-053 | Mnemonic/addressing-mode/operand-value predicates, not RAM-reference queries. |
| Raw-address sets/ranges | R3-108, R3-111, R4-019; implementer C3-017, C4-049 | One bounded selection over values/ranges. A 256-address page cannot require 256 separate RAM queries. |
| Free-text project documents | R4-033, R4-107, R4-122, R4-123, R4-139; implementer C4-021 | Search registered documents with source identity, positions and bounded context. |
| Guidance and reference search | C2-001, R3-019; C4-013, R4-137 | Extend text search to pinned guidance and admitted extracts; registration remains a separate requirement. |
| Whole-source or other unproved retrieval | C3-023, C4-196; R3-064 | Prove a targeted replacement or add the necessary bounded selection. Do not promise that document search covers ROM-byte patterns. |

All twelve reviewer cases raised in review are corrected. Applying the same
rule to both roles moves **42 calls out of “existing” (26 implementer, 16
reviewer)**. Another twelve move from planned-only classifications to an
unplanned gap. The new search family spans **89 calls (60 implementer, 29
reviewer)**, including previously blocked mixed calls: 29 need instruction
search and 64 need text search, with four needing both. These 89 are not the
reviewer's original 29 existing-labelled grep/rg calls; they cover both roles
and include guidance/reference searches. Eight calls also carry an explicit
unproved-retrieval gap, including whole-source loads and a byte-pattern scan;
this count overlaps search.

The two search contracts should follow Tooling Rule One: instruction selection
uses the native xasm records, never a regex parser over assembly text. Specify
mnemonic, addressing mode, resolved operand value/set/range and bounded context;
keep unresolved values, indexed bases and sequence evidence explicit. Text
search uses registered document IDs, pinned contents and bounded matching and
pagination, without accepting arbitrary host paths. Search over a reference or
analogue does not admit that input implicitly. A generation-bound canonical
raw-address audit might replace some range sweeps; it receives no coverage
credit until its completeness and requested facts are demonstrated.

Important limits remain. `artifact_rows` accepts only extent, blob and warning
rows; factual raw-RAM refresh does not supply a judgment writer. Guidance has
an eight-file allowlist. Analogue support accepts at most two pinned models
with selected evidence views; it is not arbitrary corpus discovery or a
cross-project documentation search. The fixed decoders are not a custom Python
or JavaScript execution facility. These limits come from code, rather than
the existence of similarly named ordinary wrappers.

## Gaps ranked by occurrence and consequence

Counts below are **overlapping capability incidences**. A mixed call can appear
in several rows, including rows whose implementation is not the call's sole
missing dependency. They must not be added to produce a coverage percentage.
The row identifiers refer to the [operation checklist](STEP_2_COVERAGE.md).

| Key / gap | Calls: implementer + reviewer | Plan | Does it stop equivalent work? |
| --- | ---: | --- | --- |
| W — authored computation, runtime tools, captures and media | 82 + 25 = **107** | 2C W2; D8 only covers inert data for already trusted tools | **Yes.** Both roles executed newly authored analysis; later corridors required captures and inspection of their results. |
| B — workflow jobs and generated evidence | 59 + 35 = **94** | 2B W1/R4 | **Yes.** Pass selection/start, independent findings, complete wrapper evidence and packet-only evidence need routes beyond candidate validation. Runtime analyzers still depend on W2. |
| O/Z — instruction and registered-text search | 60 + 29 = **89** | R1–R4 extensions; no complete search contract currently planned | **Yes.** The no-shell unscripted review needs these predicates. O has 29 incidences, Z 64; their union is 89. |
| Q — additional repository guidance/tool contracts | 44 + 9 = **53** | No complete guidance-catalog extension specified | Required instructions must be delivered. Some accesses explain ordinary-workflow detours and may not recur; 53 does not justify exposing every script. |
| X — broader analogue discovery | 33 + 15 = **48** | R5's pinned subset exists; full observed discovery is not specified | **Yes when the comparison needs inputs outside that subset.** Do not silently skip the prior-reuse gate. |
| T — remaining documents, authored rows and deferral lifecycle | 25 + 9 = **34** | 2B D1/D2/D4/R4 | **Yes** for edits/reads beyond registered docs and supported rows, including shared/project-root content. |
| I — fresh intake and reference preparation | 15 + 12 = **27** | Outside the parity-pass scope | **Yes, at the start.** ROM-container checks, initial regeneration and reference extraction cannot be assumed already complete. Low frequency does not make this optional. |
| J — raw-RAM judgments and current row access | 19 + 6 = **25** | 2B D3/R4 | **Yes** for the observed authored judgments. Factual refresh is insufficient. |
| K — recovery configuration and regeneration evidence | 8 + 8 = **16** | 2B S6/S7/W1 | **Yes** when recovery controls or non-writing comparison are needed. S6 does not authorize `project-regenerate-asm`. |
| U — extracted reference text/catalog admission | 13 + 2 = **15** | No complete shared input route specified | **Yes** if the needed extract is outside the admitted document/media set. Copying or extracting it is a declared preparation dependency. |
| P — KPI and allowlist policy | 11 + 3 = **14** | 2B D6/D7/R4 | **Yes** for a candidate requiring those changes. D7 includes the gate/schema migration, not just a CSV writer. |
| F — process-friction records | 10 + 1 = **11** | 2B D9 | Required at affected closeouts; it cannot become an arbitrary receipt edit. |
| M — unproved bounded retrieval | 7 + 1 = **8** | R1/R4/R6 practicality gap | **Unresolved.** Broad source reads and byte/location selection cannot be counted as bounded merely because all bytes exist somewhere in the service. |
| L — attributed historical amendments | 4 + 0 = **4** | No explicit amendment operation | The observed amendments preserve original receipts, but protected archives have no candidate writer. Needs an authority-owned correction route, not generic archive editing. |
| C — durable partial review notes | 0 + 2 = **2** | W3 integration; also a launcher dependency | **Yes for interrupted review.** A partial report must survive without inventing a verdict. |

Frequency and completion priority differ. W2 is the largest missing family and
a demonstrated completion dependency. Intake blocks a fresh start despite fewer
calls. Policy and raw-RAM writes can block publication despite still lower
counts. This trial cannot rank mapper coverage, multi-game concurrency or
automatic quota recovery; those [structural gaps](../PROCESS_BASELINE_PLAN.md#structural-gaps)
remain visible outside the census.

## Ordering and the next decision

Frequency does not select the next implementation automatically. Authored
execution (107 incidences), workflow jobs (94) and search (89) are the largest
missing families. Intake is an earlier hard prerequisite despite fewer calls.
**The next checkpoint should resolve feasibility, not freeze a common job
interface.** The [accepted early-feasibility rule](STEP_2_COVERAGE.md#early-confinement-feasibility)
requires both the macOS worker investigation and the still-open actual-client
and reference-media work before finalizing interfaces that depend on them.

Scope that checkpoint as a small disposable investigation, with an estimated
8–16 active hours to reach a decision, not a promise of a passing boundary.
Name the OS mechanism and supported platform/API first. Test synthetic allowed
Python and real FCEUX/Lua work, denied access and inherited child restrictions,
and timeout/cancellation/cleanup. For the intended client pairing, verify both
roles' structured tools and reference media, launch/resume, and attempts to
escape or change the configuration. The reviewer side is central to the
permission problem that motivated this work. Existing implementer evidence
covers only its pinned setup; it does not close that reviewer row.

No harness ran for this revision. Provider-backed client work needs separate
owner authorization. If the boundary is unavailable, conditional, or needs a
larger investigation, return to the owner with that result. Do not grant wider
host access or begin another revision automatically. The driving agent owns
that checkpoint; the reviewer can raise it independently.

**Typed search is the leading independent feature candidate.** Scope its
instruction and text routes against the retained cases above while feasibility
is being resolved. Search is the only new missing family in 38 calls. That is
a workload ceiling, not a prediction of 38 saved calls, tokens or interventions.
A bounded offline acceptance should compare requested facts with the retained
results, including no-match cases, later pages, unresolved operands, byte-pattern
noncoverage and stale-generation refusal. A later separately authorized,
unscripted review must actually choose these routes and discharge its evidence
obligations without shell fallback. That live acceptance waits for the needed
client, launcher and other coverage dependencies; search alone cannot satisfy it.

Workflow jobs remain useful for pass selection/start, non-writing regeneration
comparison, hidden-code findings and durable results. Their **independent**
value is replacing those named trusted wrapper invocations and preserving
complete generation-bound outputs. The previous claim that they should go
first because W2 will reuse their interface is withdrawn. Keep any W2-facing
interface provisional until feasibility has passed; do not accept caller-chosen
executables, environment overrides or arbitrary command strings.

The previous sixteen job examples remain useful as obligations, not a
self-contained acceptance set. In particular R3-064 also needs byte-pattern
selection (M), and R3-119 searches guidance (Z). The entire B family is the only
missing family in 55 calls, and W in 61. Neither number establishes comparative
cost. Do not run candidate-authored analyzers in a trusted job supervisor;
[W2's boundary](STEP_2_COVERAGE.md#wrappers-runtime-evidence-and-completion)
remains a separate requirement.

## Minimum path to one fresh-game pass through the service

The endpoint here is **supplied ROM/references through intake and one accepted,
closed-out pass**, with required recovery, comparison and runtime evidence and
no ad hoc shell fallback. It is not gold maturity or merely attaching the
service to a project already prepared by ordinary agents. The path below covers
the observed kind of work; the chosen corridor determines which artifact writers
and runtime cases it actually requires. Segments 1, 3 and 4 expose intake or
authored-execution dependencies; segment 2 contains only two orientation calls.

These are rough engineering estimates in **active hours**, not measured costs,
quotes or authorized budgets. Except for the existing launcher estimate, they
are new judgment ranges based on the contract and integration work. They
exclude CI/review waiting and provider elapsed time. Re-estimate after the
feasibility checkpoint and once the chosen pass's obligations are explicit.

| Component | Rough size | Needed result and dependency |
| --- | ---: | --- |
| Early worker and actual-client feasibility | 8–16 h checkpoint | A tested or explicitly rejected boundary, including reviewer/media access. Precedes freezing W2-dependent interfaces; no service implementation is implied by a successful spike. |
| Structured launcher | 8–16 h | Accepted existing scope: admission, profiles, handoff routing, supervised notifier, per-turn messages, visible stops and continuation. Actual-client evidence and separate live authorization are prerequisites to use. |
| Workflow jobs and generated evidence | 8–16 h | Named trusted jobs, complete paged results, failures and cancellation; next-pass/start, hidden-code findings and non-writing regeneration. Keep worker integration provisional until feasibility. |
| Isolated worker execution and runtime integration | 16–40 h after feasible boundary | Authored Python/Lua, real emulator resources, captured outputs/media, fixtures and cleanup behind W2/W3. A fixed decoder may replace some observed helpers; it does not cover later authored traces. |
| Fresh intake contract | 12–24 h | Supplied-input registration, mapper/container checks, reference extraction, initial regeneration, recovery and a transition into normal admission. Intake is outside the current parity-pass roadmap; S6 alone does not provide it. |
| Instruction and text search | 8–16 h | Native instruction predicates and registered-text selection with complete, bounded results. Can be developed offline independently; admission and client delivery are needed for live use. |
| Guidance, reference and analogue extensions | 4–8 h | Pin the needed guidance, extracted text and comparison corpus; extend the narrow current analogue views. Search does not replace these input/authority decisions. |
| Candidate writes and publication closure | 8–24 h, pass-dependent | Required recovery hints, raw-RAM judgments, remaining artifact rows, policy migration, deferrals/friction and any attributed amendments. Reuse 2A edits; do not call these existing merely because the read side works. |
| Integrated independent review and closeout | 8–16 h | Durable partial review, resume, gates, publication/application, evidence retention and one authorized unscripted pass. Missing evidence and ordinary rework remain visible. |

As a serial planning envelope this is **80–176 active hours**, roughly ten to
22 eight-hour days, with substantial uncertainty. Shared implementation may
reduce it; a failed worker boundary or broader intake contract may exceed it.
It is not a commitment to build that whole path. In particular, the launcher
alone is still an 8–16-hour component, not an 8–16-hour fresh-game solution.

Compare this investment with a smaller typed-inspection slice for an already
admitted project and with attended ordinary operation. The latter preserves
existing capability but accepts the measured permission friction. The owner
chooses the next slice and whether fresh-game runs remain paused. No first
slice, however useful, proves that the full fresh-game path is available.

## Launcher dependencies and parked work

Offline service development does not require the launcher first. A usable live
path still needs the [accepted launcher scope](LAUNCHER_DECISION.md): admission
against tested client hashes, isolated profiles, the session handoff store,
supervised notification, exact per-turn messages, authoritative handoff checks,
continuation/extension and honest public errors. Its recorded 8–16-hour estimate
is separate from operation coverage. New adapter bytes require affected offline
checks and a separately authorized live smoke; old preflight evidence does not
certify them. Neither the trial's client versions nor its model/memory settings
are automatically admitted to the structured path.

Keep the ordinary command-spelling draft parked. Do not merge it as reviewer
guidance or resume game passes to validate it. Per-session worktrees and the
article-check inconsistency remain separate follow-ups. Their value for
isolation/concurrency does not turn them into prerequisites for this map.
There is no implementation or new runtime authorization here.

## Evidence identity and limits

The private census checks every source against its existing retained-record
pin. Segment 4 uses the final paused copies, not the earlier partial snapshots.
The following SHA-256 values identify the eight inputs without exposing paths:

| Segment / role | SHA-256 |
| --- | --- |
| 1 / implementer | `8a975e8df2f771a327d961d95465a15716398c1e966b6c00546c63acad1999c1` |
| 1 / reviewer | `c6f8b2c27d0bef551ed1b72bf79066c120796b0cce920c5bc9c832ebfec729c1` |
| 2 / implementer | `6bc51d9619ab342d4eb63e2f5befecce387cbfd10966d36bd249143675363702` |
| 2 / reviewer | `d2f72e3e92514f257a2f0f2e63ee6db2ddd78961083747e8a9bad041aa55fd0f` |
| 3 / implementer | `60ea08bc0bca9a64efa290e48afec3dfe6b8313664079be2566b1c168a0e9da5` |
| 3 / reviewer | `22cf255042ad4d3539f1fd43fe202a4cb748f7c5dee65cc97b74961dd1ae174e` |
| 4 / implementer | `4c96197245b7cb17e86c8b357ed93072f971dc9752439d40e393a3b9b0bd5310` |
| 4 / reviewer | `607c7863b51459d1e8a04be0ac07f3af0d5747b410bf08cf90593013ef7e1297` |

Classification is interpretive and conservative, especially for mixed cells,
corpus discovery and custom computation. Reading bytes is not proof that a
custom decoder's result is available. Conversely, writing a temporary patch
generator does not require a new code-execution route when typed edits express
its entire intended effect. Broad family counts do not prove the proposed
slice is a mathematically optimal investment. Freeze concrete acceptance cases
and refine the mapping when implementing them.

This assessment made no provider calls, ran no project gates or captures, and
changed no project, trial, permission or client state. It supplies a decision
input under the [manifesto](../MANIFESTO.md), not a new completion claim.
