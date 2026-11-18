# Client-visible operation arguments

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

## Measured delivery

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

## Verification and remaining admission

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
