# Typed search: authorized offline scope

**Owner-authorized offline scope, 15 November 2026.** This proposal follows the
[accepted feasibility decision](FEASIBILITY_DECISION.md) and
[retained workload assessment](TRIAL_WORKLOAD_COVERAGE.md). The owner authorized
the bounded offline work below, beginning with the
two-hour translation checkpoint. Provider calls and game passes remain outside
that authorization. The completed feasibility checkpoint and census
landed in [PR #186](https://github.com/khansen/nesrev/pull/186) as `aa6fff061`.
The [translation checkpoint](TYPED_SEARCH_CHECKPOINT.md) records all 89 requests,
the input and predicate gaps, and the decision before implementation.

## Outcome and why this comes first

Give both roles a practical way to find instruction facts and admitted text
through the facts bridge, without shell access, source-file parsing or reading
every page. This advances the [process objective](../MANIFESTO.md): reusable,
dependable inspection across unfamiliar games rather than new permission rules
for one client's command strings.

The census contains **89 search-bearing calls: 60 implementer and 29 reviewer**.
Instruction search occurs in 29, text search in 64, with four containing both.
Search is the only missing capability family in 38 calls; mixed calls retain
their other needs. These are workload counts, not predicted saved calls, tokens,
prompts or hours. Search alone cannot complete an unscripted fresh-game pass.

| Alternative | Value and reason for this ordering |
| --- | --- |
| Ordinary-client spelling guidance or broader shell grants | Might reduce current prompts, but preserves the client-specific classifier dependency the owner chose to leave. |
| Workflow jobs first | Useful for 55 calls with only that gap, but does not provide the search predicates needed by review. It remains a separate slice. |
| Worker integration first | Execution is the sole gap in 61 calls and is necessary for runtime work. Feasibility now supports its boundary, but production integration is larger and not needed to build search. |
| Structured launcher first | Its [accepted scope](LAUNCHER_DECISION.md) has the same 8–16-hour estimate and would make a live structured loop available sooner for static work like the pilots. An unscripted review would still encounter the known search gap, present in 29 retained reviewer calls. |
| Typed search first | Fills the largest unplanned family with a bounded, independently testable service feature. It uses producer facts and existing admission; offline correctness needs neither a new worker nor a live client. Live use still waits for the launcher. |

Recommend search first: the retained workload already establishes the search
gap, so launching an unscripted loop first would largely measure that gap again.
This order trades earlier live operation for closing a known prerequisite offline;
it does not make the launcher optional.

## Bound, ownership and checkpoint

The authorized scope has an **8–16-active-hour estimate**, with an early
translation checkpoint after at most two hours, a progress checkpoint at eight
hours and a hard stop at sixteen.
The estimate remains uncertain; the sixteen-hour bound is the authorized ceiling.
Expected work:
1–2 hours for the case contract, 3–6 for routes, 3–5 for acceptance and failing
controls, and 1–3 for documentation and review corrections. Record actual
active intervals separately from CI, external review and owner waiting time.

The driving agent owns the case ledger, parked list and checkpoints. The reviewer
can call a checkpoint independently; the owner decides changes of scope or
extensions. Allow one implementation review with a bounded correction check;
a second substantive review round returns to the owner. Stop sooner if the same
failure class recurs twice, a producer change or new input-admission contract is
needed, the eight-call practicality limit cannot be met, or a subproblem becomes
a separate project. A stop produces the result and options, not wider access.

At the first checkpoint, translate **all 89 calls** into independently stated
questions, expected witnesses or absence claims, and required inputs. Identify
which are answerable by the proposed routes on currently admitted inputs. List
every mixed or deferred need and its reason. If an intended search-only case
requires widening this contract, return that decision before implementing it.
Do not split a range sweep into hundreds of independent questions to meet the
call limit. Preserve the original census; new acceptance dispositions belong in
a separate ledger.

Expect partial coverage, not 89 supported calls. Unadmitted inputs and other
capability gaps remain deferred. Distinguish a missing historical snapshot from
one that is present but refused by current-project admission; both remain
unverified in the ledger, with the latter's refusal reason recorded. Do not
weaken admission to increase the verified count.

## Proposed contract

Two read-only operation families are offered to both roles. Final field names
are implementation details to settle in the first checkpoint. Reuse existing
generation verification, record identities, document admission and the bridge's
24 KiB response ceiling. No caller-selected executable, raw host path, shell
expression, new input grant or candidate mutation is introduced.

### Instruction search

Query native xasm instruction, expression, evaluation and binding records.
The existing model exposes mnemonic, parsed/final addressing modes, operand
values, locations and memory/control-flow facts. Assembly text may accompany an
existing record view, but it is not parsed to recover those facts.

- Select mnemonic sets, final addressing-mode sets, and integer operand values,
  bounded sets or inclusive ranges. Separate immediate operands from memory
  operands. Include a producer-expression selector for literal versus bound or
  compound operands, so a raw-operand audit does not also flag named aliases.
- Preserve operand evaluation status. Unknown or non-integer values are not
  zero and cannot disappear into a confident no-match claim. Return explicit
  unresolved counts/identities and a bounded way to inspect them. If the pinned
  producer cannot supply a needed fact, record the gap instead of guessing.
- Label indexed values as bases and indirect operands as pointer expressions;
  do not infer runtime destinations or alias proof from equal numeric values.
  Return the native addressing and memory-access facts that support the result.
- Support bounded consecutive-instruction predicates for the retained short
  sequence scans, and bounded neighboring records for interpretation. Define
  adjacency by native record order and byte locations; do not cross data, segment
  boundaries or discontiguous code. Adjacency is not proof of a control-flow path.
  No general graph-query language is part of this slice.
- Return generation, stable record/owner IDs, locations, predicate identity,
  complete match count and deterministic continuation. Reuse existing symbol
  and RAM evidence for questions they already answer in a practical call count.

The first checkpoint fixes maxima for predicate lists, value sets, ranges,
sequence length and context using the retained cases. Do not introduce an
unbounded expression language or extend the assembler to make a case fit.

### Registered text search

Search only content already admitted by the session: authored documents allowed
by the existing document route and pinned guidance on its existing allowlist.
Derive a bounded catalogue from those same identities and admission checks.
An identity may retain its existing canonical relative name; it is not permission
to open any similarly named file. Return the selected document set explicitly.

Use literal text, an any-of list, optional case-insensitive and whole-token
matching, and line prefix selection for heading searches. Whole-token mode
reuses Q09's `[A-Za-z0-9_@]` identifier-boundary rule in
`rename_service.py:mentions`; it is not linguistic word segmentation. The
retained patterns must be translated
by meaning, with complete result comparison; neither broadening a pattern nor
omitting an alternative counts as success. If a required predicate cannot be
expressed within the agreed call bound, record it at the first checkpoint.
Arbitrary backtracking regex execution is not the initial contract.

Results identify the pinned document and content hash, line/match position,
matching term, bounded context and continuation. State the case-folding and
position conventions and test Unicode; exact literal spelling remains available.
Long lines must have explicit bounded slices and continuations, not silent
truncation. Return an explicit complete zero-match result when appropriate.

Reference extraction, additional playbooks, broader analogues, arbitrary CSV
access and protected historical archives do not become admitted because a query
mentions them. Cases needing those inputs remain mixed or deferred, even if a
synthetic text fixture proves that the matching predicate itself works. Existing
Q09 identifier checks retain their separate meaning and enforcement.

### Generation, bounds and completeness

Every search names an explicit available generation. Historical generations
remain valid evidence where the existing service permits them; they must never
be silently replaced with current state. Bind continuations to the generation,
query and selected input hashes. Refuse an old continuation reused with a new
generation or predicate, unknown generations, foreign record IDs and modified
pinned inputs before returning evidence.

Pagination must make progress under the wire ceiling, with stable ordering and
no omissions or duplicates. A later page can contain the only relevant witness.
Distinguish complete zero matches, incomplete pages, unresolved values and
unsupported input/predicate errors. None is a substitute for the others.

The assessment's practicality ceiling stays **eight total service requests per
independent question**, including catalogue selection, context and all necessary
pages. A match count alone is enough only for a count question, not inspection
of every witness. An overflow stays a coverage gap; do not raise the ceiling or
truncate results to improve the reported coverage.

## Offline acceptance

Acceptance uses the retained requests/results and their pinned source snapshots,
not a fresh game pass. Keep identities, arguments and source content private;
commit project-neutral fixtures and an anonymous outcome summary. The service
implementation must not acquire a dependency on the private packet's paths.

| Check | Required evidence |
| --- | --- |
| All 89 calls accounted for | One ledger row per original call, with each independent search need, input availability/admission, proposed request sequence, expected result, measured call count and remaining non-search needs. Separate missing snapshots from present but admission-refused snapshots, retaining refusal reasons. No sampled subset presented as the whole workload. |
| Instruction and sequence scans | Exercise the needs behind R3-063/067/068 and C1-031: indirect/mnemonic selection, expression shape, and consecutive-instruction evidence. Verify native record identities and context. |
| Immediate and range queries | Exercise R4-036/044, C3-022, R3-108/111, R4-019, C3-017 and C4-049. A range is selected directly; immediate, direct, indexed-base and indirect cases stay distinct. |
| Text and guidance | Exercise R4-033/107/122/123/139, C4-021, C2-001 and R3-019. Check term alternatives, case handling, whole-token boundaries (including `_` and `@`), literal punctuation, document selection and positions. Unadmitted inputs are recorded as gaps. |
| No-match and later-page results | Independently verify complete absence where claimed. Include a match only beyond page one, an exactly full page, oversized context and a long matching line. Follow all continuations and compare the complete witness set. |
| Unresolved operands | Use valid producer-derived fixtures with unresolved/non-integer evidence where supported. Demonstrate explicit uncertainty and no false numeric match or absence claim. If such a state cannot be produced, document the producer invariant and test the refusal path rather than inventing valid-looking facts. |
| Stale generation and drift | Reject a stale continuation against a different generation/query/input set, foreign IDs and changed pinned bytes. Retain successful explicitly selected historical reads; reject unknown generations. |
| Integrity and access | Both roles receive only the admitted read operations. Unknown IDs, traversal, unregistered documents and unsupported predicates fail. Search leaves source, candidates, review coverage and verdict state unchanged. |
| Wire and practicality bounds | Measure serialized bridge responses, catalogue/context requests and every page. Reclassify any question needing more than eight requests; do not change the threshold. |
| Failing controls | Demonstrate detection of a dropped later-page match, unresolved value treated as zero, wrong operand mode/base interpretation, stale continuation accepted and an unadmitted document exposed. Reuse existing fixtures/checkers where possible. |

The old shell results are observations, not a complete oracle: some were capped
by `head` or tool output limits. Establish expected complete witnesses from the
pinned native facts/documents independently of the new search implementation.
If the relevant historical snapshot is missing or admission refuses it, mark
that case unverified with the distinct reason; a synthetic analogue checks
behavior but does not retroactively pass the case.
ROM-byte pattern search, whole-source downloads and unrelated computation are
explicit noncoverage, not document-search successes.

Run the affected structured-service tests and the repository's required CI
targets after the final implementation. Record exact checks and failures. No
provider-backed smoke or emulator execution is needed for this offline slice.

## Integration and work deliberately left out

Implementation is on a branch from master `aa6fff061`, which contains the
merged decision PR.
Expected changes are the source/document query helpers, service dispatch and
wire schema, bridge operation declaration, focused fixtures/tests and docs.
Reuse `model.py`, navigation/evidence identity helpers, the admitted document
readers and paging support. No client sandbox, hook or adapter behavior changes
are planned. If exposing search changes a pinned tool declaration, record that
delta and refresh its offline tests/pins; old client acceptance does not
automatically cover the expanded interface.

A later, separately authorized **unscripted** review must actually choose the
routes and complete its evidence obligations without shell fallback or missing
evidence. Scripted success alone cannot establish that. It waits for launcher
admission/delivery and the other capabilities the selected task needs. Fold the
reviewer's hook-disabled check into that next appropriate client smoke, not an
extra live campaign in this slice.

Workflow jobs, worker integration, intake, new reference/analogue admission,
runtime evidence, permission spelling guidance and per-session worktrees remain
outside this implementation. The article-check inconsistency and workspace
isolation stay parked. No ordinary or structured game pass follows automatically.

**Authorization recorded:** the owner approved this offline scope on 15 November
2026. Report at the first translation checkpoint before implementing the routes;
any scope change or extension returns to the owner.
