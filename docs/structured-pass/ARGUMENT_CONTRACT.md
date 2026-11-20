# Client-visible operation arguments

Current status: the [r5 live smoke](FG1_LAUNCHER_ACCEPTANCE.md) used the 19 November
contract successfully. The [readiness result](FG1_READINESS_RESULT.md) adds
role-local published-candidate sources, a multi-round witness and new captured
declaration pins. Those changes have offline evidence; r5 is not relabelled as
live admission of the new pin. The dated records below preserve earlier limits.

18 November 2026. A live admission attempt stopped at `validate`: the client
sent a `candidate` field taken from the preceding response, while dispatch
required `cid`. The facts declaration named the operation but did not deliver
its argument contract. Earlier scripted calls supplied that knowledge in their
prompts. The service correctly refused the call; the launcher remains pending
admission.

## Production contract

[`operation_contract.py`](../../scripts/structured_pass/operation_contract.py)
holds the argument-key tables previously embedded in the base service, rename
service, corridor controller, retained reader and verdict bridge. Those dispatch
paths enforce the same tables now used to generate the declaration. Each
offered operation lists required and optional keys. The image variant of
`input` uses its own enforced no-pagination schema.

This describes outer argument keys, not a new validation engine. Existing
value checks, nested query/edit schemas, role checks, generation checks and
quality gates still apply. `confirm` still returns `candidate`, while
`validate` and `publish` still accept `cid`; this change does not rename the
protocol. Unknown keys remain errors. Known-operation `REQUEST_SCHEMA` results
also return the expected keys from these tables; they remain non-retryable and
do not override a run's no-retry instruction.

The generated contract lives in the tool declaration's
`inputSchema.properties.arguments.description`. The top-level description
points to it. This placement is necessary on the pinned Claude client: the
first offline capture truncated a 4,836-character top-level description at
4,096 characters, losing required contracts. The failed capture is retained.
No live attempt was made with that format.

## Initial argument-key delivery (18 November)

Two final credential-free loopback invocations captured the native Codex
declaration and the Claude API request. Both contain the complete generated
contract, byte-equal to production. All smoke dependencies are present:
`cid`, verdict `ticket` and `report`, the five review keys, report `sequence`,
`input_id`, and `preview_digest`. Read-only roles receive no mutation contracts.

| Service declaration | Operations | Top-level help characters | Argument contract characters | Complete listing bytes |
|---|---:|---:|---:|---:|
| Corridor implementer | 24 | 4,027 | 1,907 | 6,851 |
| Corridor reviewer | 18 | 3,403 | 1,491 | 5,678 |
| Retained reviewer | 12 | 1,211 | 1,060 | 2,884 |

All listings remain below 24 KiB. Tests keep both description fields below the
observed 4,096-character boundary. Codex continues to add an empty `properties`
object to the open arguments schema, as it did in the previously admitted
declaration. The full native diff changes only the top-level help pointer and
the new argument description; tools, features and accepted request shapes are
unchanged.

The native Codex pin is
`c72c1e4fbd8a5f13118438a84dae5472aca7222d29d8a8170b9a39e3f97c5fe5`.
The captured native declaration and Claude facts declaration are retained as
project-neutral test fixtures. New pair preparation derives these service pins:

| Declaration | SHA-256 |
|---|---|
| Corridor implementer | `dcccd3f991f215b51278845847bcfabf556c7289172c8b549625c72fba8cc00e` |
| Corridor reviewer | `3198843c826dcb64910998c68b187168d482e8ccc5a9a3c15cce375b983e2c35` |
| Retained reviewer | `4b1580b4ae15bcbd67f64c690a18d1a891b4ff48a05e0bdd06ec347ff8b5306d` |

There were four native loopback invocations in total: two for the initial
placement and two for the corrected placement, with zero provider calls and
zero tool calls. The Codex endpoint deliberately refused its request after
capture; Claude received a scripted final answer. These prove delivery, not
model understanding, authenticated availability or a successful handoff.

## Initial verification (18 November)

The contract tests compare every offered operation with the schema reached by
its real dispatch method, exercising required keys, optional keys, missing
keys and extra keys before side effects. Separate checks cover the image
variant, client captures, declaration size and expected-key errors. A stale
captured declaration is refused when dispatch changes its candidate key.

The private record contains the full suite, deliberate-fault results, raw
requests and streams, client identities, exact declaration differences, and
process cleanup. The full structured suite passed **389 tests, one opt-in
skip**, in 190.2 seconds. Four in-memory faults failed by assertion: renaming
the dispatch candidate key without changing the declaration, omitting the
review ticket from the declaration, allowing image pagination, and restoring
the old native pin. Playbook and repository-hygiene checks passed. The full
ordinary shell/Java suite was not rerun for this correction.

The record also preserves two preparation corrections: a test fixture
initially omitted a role parameter, and the first capture comparison omitted
Codex's existing empty-properties normalization. Neither changed production
acceptance or repeated a completed invocation.

The next step is code review, then fresh profiles and a newly sealed packet.
That packet must rerun the hook-disabled phase offline with the new declaration
before requesting live authorization. Previous smoke evidence and spent
authorizations remain unchanged. Old profiles cannot be reused with changed
code/declaration pins; use fresh isolated logins, retiring the old ones through
the matching clients after result review. No live smoke or game work is
authorized by this correction.

## Identity sources (19 November)

The packet review found a remaining gap: naming `cid` does not tell the
client to copy the result's `candidate` value. The earlier scripted rehearsal
made that connection itself. The production declaration now supplies a
`sources` map alongside each operation's keys. Paths name values in operation
results, with list selection explicit. This changes help and pins, not dispatch
or the protocol's names.

| Argument | Result source |
|---|---|
| `cid` | `confirm.candidate`; `preview.candidate` for an existing candidate |
| `preview_digest` | `preview.preview_digest` |
| `input_id` | `inputs.records[].id` |
| Ordinary `generation` | `status.generation` |
| Corridor `ticket` | `status.ticket` |
| Corridor review `generation` / `base_generation` | `status.handoff.coverage.pass_head` / `pass_base` |
| Review-report `sequence` | `status.handoff.latest_review.sequence` |
| Retained review `base_generation` | `status.evidence[-2].artifact_id`, paired with the current generation |

The declaration explicitly says to use non-null identities: a new preview
has no candidate, so `confirm.candidate` comes first. Corridor review identities
are retained artifacts, distinct from editable generation IDs. A standalone
retained reader uses the last two entries in its ordered evidence list; its
optional continuation-window metadata is not a universal source of that pair.

One lifecycle test uses these delivered paths to construct real dispatch calls
through input reading, preview, confirmation, validation, publication, review,
request-changes and report retrieval, plus restored review. It checks every
advertised source path for both roles and both profiles against real service
results. Certification uses the pinned assembler; the fixture's quality wrappers
are simulated. This is contract evidence, not another game acceptance run.

Six in-memory faults fail that test: a nonexistent candidate source, an omitted
candidate source, a renamed result field, an editable generation used for review,
the head used as the review base, and a ticket used as the report sequence.
Four fail with errors and two with assertions; baseline and restored code pass.

Two final credential-free loopback captures confirm that both pinned clients
receive the expanded contract exactly. The native diff changes only
`arguments.description`; top-level help, tools and other schema fields are
unchanged. The earlier capture is also retained: a real-result test corrected
the draft retained-reader source before the final capture. Four native capture
invocations in total made zero provider calls and zero tool calls.

| Service declaration | Top-level help characters | Argument contract characters | Listing bytes | SHA-256 |
|---|---:|---:|---:|---|
| Corridor implementer | 4,027 | 3,586 | 8,651 | `d87c994fc1f0c2a334af19651d73933ac27a559338d3bb507eaeabb7ed1e1b0c` |
| Corridor reviewer | 3,403 | 2,804 | 7,070 | `b850383156b85558e40490a0f00b241edb432d7435d5d13ff981a0766794cc23` |
| Retained reviewer | 1,211 | 2,018 | 3,877 | `a0331b6e1f916a1f84b7c98b1a583d49f52c38b9ea588d08df3e3cadca141f0b` |

The new native Codex pin is
`43fb852102975edfb7bda7a4def191e98bd1a29d40a03583bf3c376cb9551584`.
Both committed declaration fixtures come from the final captures. Listings
remain below 24 KiB and both description fields below 4,096 characters.

The full structured suite passed **390 tests, one opt-in skip**, in 187.3
seconds under the shared heavy-run lock. The final captured native declaration
passes admission; the previous declaration is refused. Playbook and repository
hygiene checks passed. The ordinary shell/Java suite was not rerun for this
help-contract correction.

Code review comes before r5. After approval, fresh packet preparation must pin
all declarations, rerun all four loopback phases through the watcher, and seal
the packet for review. No r5 packet, login, provider call or live smoke is part
of this correction. Previous packets and spent authorizations are preserved;
upstreaming still follows admission.
