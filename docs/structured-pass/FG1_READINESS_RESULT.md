# FG-1 readiness: offline result

20 November 2026. The four carried readiness items now have offline evidence.
The implementation is `5ad82de4a`; final code review and both CI platforms remain
before merge. **No unscripted pass or provider call ran.** The proposed next
action is one separately authorized pass, after fresh preparation and an explicit
admission-transition review. The [scope](FG1_PASS_READINESS.md) and
[early checkpoint](FG1_READINESS_CHECKPOINT.md) retain the bounds and earlier
layout-probe refusals.

## Reviewer identities and failure behavior

`status.handoff.published_candidate` exposes `cid`, `revision`, `attempt`,
editable `generation` and retained `ticket` for the published head under review.
Draft and validated successors cannot replace that identity. Artifact-only
handoffs return no candidate metadata. The generated contract points reviewers
to their own status result; implementers continue to use their own confirmation
and validation results.

The lifecycle test uses separate role histories, revision 1 and validation
attempt 2. It reaches round 2 while the latest verdict sequence is still 1,
fetches report 1, then fetches report 2 after the next verdict. Substituting
round for sequence fails that lifecycle assertion without relying on the frozen
client fixture. Wrong, missing, stale and other-role-only sources are also
caught. Published-head selection has draft, wrong-generation, wrong-head and
invalid-metadata controls.

The new lookup is part of the common handoff result builder. Consequently,
malformed publisher state blocks status, verdicts, watcher advancement,
archive and closeout, rather than returning a partial handoff result. Every
caller holds the existing publisher lock; publication updates the current
generation and published candidate together. This deliberate failure behavior
does not add recovery authority or expose unpublished candidates.

Both generated handoff prompts and the review archive contain the metadata.
The application fixture confirms that the applied archive is byte-identical
and carries the same identity as the approved head. `candidate_status` provides
gate results; `validation_evidence` remains an error-detail reader and can
correctly return `EVIDENCE_UNAVAILABLE` after a successful validation.

## Captured declarations and four-phase rehearsal

All four authorized credential-free native invocations passed on their first
attempt, using the copied pinned client packages and loopback endpoints only:

| Phase | Calls | Result |
| --- | ---: | --- |
| Hook-disabled reviewer | 11 | Eight structured restricted-path denials, two successful media reads and successful status. |
| Initial implementer | 9 | Scripted image read, confirmation, validation and publication. |
| Pair reviewer | 6 | Actual notification, media read, complete review and request-changes. |
| Same-thread implementer resume | 2 | Changed notification message and correct report retrieval. |

The real watcher produced two accepted notifications. The pair recorded
`handoff`, `handoff`, `unfinished`, with both workers exiting normally and no
survivors. This recipe intentionally ends unfinished; it is not a semantic pass.
The scripted implementer derives `cid` from the source path in the delivered
contract. It does not provide evidence that an unscripted model interprets the
revised help correctly.

All 13 captured Codex requests and 19 Claude requests contain the expected
declarations. The only semantic declaration difference is
`arguments.description`; tools, other schema fields and permission settings
are unchanged. Both native fixtures were refreshed together.

| Declaration | Top-level characters | Contract characters | Listing bytes |
| --- | ---: | ---: | ---: |
| Corridor implementer | 4,027 | 3,684 | 8,755 |
| Corridor reviewer | 3,403 | 2,975 | 7,245 |
| Retained reviewer | 1,211 | 2,071 | 3,930 |

Listing sizes use the tool-list payload envelope used at the checkpoint; the
JSON-RPC envelope adds 39 bytes. All remain below 24 KiB. Each description is
below 4,096 characters, with only 69 characters free in implementer top-level
help. Existing tests enforce these bounds.

The new native Codex pin is
`1b1480f7ead867322251ccb7abe0e1fc2e5e4e19fd560e5a12300d16316cb750`.
Fresh pair preparation derives these service declaration hashes:

| Declaration | SHA-256 |
| --- | --- |
| Corridor implementer | `4ad9aab417dc934aac9221422be04f99859b1d2e298e5575dbb85c5a1840cee0` |
| Corridor reviewer | `a0359fb62a334fe758918749e18242afcbf5fc9f3ea778a9355e5e8af5ed90b6` |
| Retained reviewer | `cc29f53b38a3d3ce215ef662297163edb34c5ac56cfd54f2e96f4baaa2901b89` |

The accepted [r5 live result](FG1_LAUNCHER_ACCEPTANCE.md) still belongs to its
original pin. Its unchanged access-control, image and handoff mechanisms are
prior live evidence; this new pin has offline delivery and integration evidence.
Real-model use of the revised identity/help contract remains a named live
acceptance item. The recommended transition is to review this distinction and
test it in the separately authorized pass, rather than silently relabel r5.
If transition review requires a fresh live preflight, its budget and authority
must be separate.

## Observed writes and their scope

The real starting layout passed full preparation, including native certification,
generated-only checking and naming-only verification after strict exit 3. It
remains **not strict-green**. The two rejected dummy candidates in the checkpoint
remain rejected. No further invented closeout was attempted on the real project.

Expected changes are expressed relative to sealed layout roots, with the
following evidence and content restrictions. The private record retains exact
file hashes, path templates and their source observations.

| Root-relative class | Evidence | Required restriction at live binding/application |
| --- | --- | --- |
| `session/editor/` candidate attempts, logs, captures and state | Real-layout rejected-candidate before/after diff | Candidate/revision/attempt must exist in state. Enumerate starting-tree files and gate-owned outputs; typed edits and certification constrain contents. No unrestricted checkout glob. |
| `store/` and `session/review-cache/` | Four-phase synthetic native recipe | Content-addressed blobs, publication receipts and restored manifests must agree. |
| `session/handoff/.git/info/exclude` | Actual synthetic handoff initialization | Exactly the preimage plus the standard runtime block, or unchanged if already present. |
| Handoff state, prompts, verdicts, responses and seen markers | Native recipe plus synthetic application history | Bind run, published head, coverage and hashed history. Both prompts carry the reviewed candidate identity. |
| Isolated client profiles and pair messages, notifications, turns and watcher records | Four-phase native recipe | Bind launch/run/thread and allowances; workspaces and sealed inputs stay immutable. Authorization is an owner-only pre-window write. |
| Closeout record, retained observations, archive and friction output | Existing integrated synthetic application fixture | Same approved identity in archive and prompts; unchanged importer and committed receipts. |
| `target/<journal path>` and target Git commit metadata | Synthetic partial-write and post-commit recovery | Exact frozen application write set and hashes, checked preimages, no receipt edits, no unrelated changes and no duplicate commit. |

The native recipe observed 417 additions and five modifications, including the
exclude append. Application observation separately covers partial queue writes,
a failure after commit but before receipt, and recovery without another commit.
The raw histories also retain the response file and the identity-bearing archive.
The path-class check rejects unknown roots/files, traversal, changed media,
credential-file changes, observer-only paths and authorization written during a
run. The exclude append is compared with the production initializer.

These are net phase snapshots, not continuous filesystem tracing. They do not
prove the absence of transient writes. Synthetic quality wrappers and synthetic
source do not establish real-game closeout. Authenticated client homes may differ
from dummy homes; unknown writes still stop. Before the live seal, bind the
actual roots and starting tree; before application, enumerate the actual journal
write set. A path match never substitutes for content or ownership checks.

## Complete pass-operation matrix

| Obligation | Role and existing operation | Identity, evidence and limit |
| --- | --- | --- |
| Current task and declared inputs | Both: `status`, `inputs`, `input`, `guidance` | Own current generation; catalog IDs and hashes. Historical intake evidence stays labelled. Whole-text download may exceed eight pages; the eight-request limit applies to logical evidence questions. |
| Reference illustrations | Implementer fixed-ID `input`; reviewer admitted media `Read` | Sealed page identity; no caller path on facts. PNG at most 3 MiB/2048 px; fetch only needed pages, normally one to three. Eight fetches per conversation is audited guidance, including repeated IDs. |
| Analogue comparison | Both: `navigate`/`evidence` with captured analogue selector | Only the two operator-selected models. Revalidate local semantics. Manual selection is recorded, not credited to agents. |
| Control/data-flow and instruction search | Both: `navigate`, `inspect`, `query`, `search` | Generation/query-bound continuations; unresolved differs from no-match. Fixed 24 KiB response and eight-request practicality limits. |
| RAM ownership | Both: `evidence` views `ram_compact`, `ram_shared` | Expand constants, columns and selection, fetch shared set once per generation, retain all unknowns. Earlier measured cold reads were eight requests for both selected bytes; unscripted expansion remains unproven. |
| Semantic and canonical-document changes | Implementer: typed `preview`, `confirm`, `validate`, `publish` | Own confirmation identity, preview digest, expected preimages and field ownership. Include scorecard and closeout operations; pass 1 needs its authored analogue decision. |
| RAM judgments | Implementer typed `raw_ram_judgments` | Existing rows only, expected file/row versions; only status, proposed name and notes. No factual-column or identity edits. |
| Independent review | Reviewer: `status`, `candidate_status`, `review`, verdict | Own published identity; full coverage head/base and every review page; current ticket. Successful gates are in candidate status, not error evidence. |
| Findings and rework | Implementer: `review_report`, typed edits, `reready`; reviewer rereview | Latest verdict sequence, not round; exact responses retained. One proposed rework round, with no failed-invocation replacement. |
| Learning candidates | Both, in existing closeout fields/responses/verdicts | Shared instruction text, explicit `_None._`, no duplication of published observations, carry forward unpublished ones. Body cap remains 4 KiB. |
| Approved closeout | Implementer: `closeout` | Approved current full range, qualified verification, matching archive/identity and retained learning sources. No strict-green claim without strict verification. |
| Local application | Coordinator: existing application command | Explicit target authorization; current preimages/index/reference, frozen journal, all four gates, archive and queue import. No push or pass 2. |

The earlier four broad instruction questions still require 14, 9, 11 and 20
requests on early-stage code. They are a known limitation, not newly solved
here. If this corridor requires an over-limit question, unsupported write,
runtime trace or new input, stop with the missing evidence; do not increase
limits, relabel the same question or repair content as coordinator.

## Verification and proposed live request

The full structured suite on macOS arm64 passed **392 tests, one opt-in skip**,
in 191.1 seconds under the shared heavy-run lock on `5ad82de4a`. The skipped
native test did not consume another invocation. `make test` also passed on that
code: **692 shell cases and 1,206 Java tests**, plus playbook and hygiene checks.
The final documentation-only changes receive separate playbook/hygiene and link
checks; the production suite is carried forward unchanged from that code head.
Exact logs and file hashes are retained in the private check record.
Linux and macOS CI on the publication head are still required.

The private draft pins the starting commit, source/ROM/input identities,
selection, complete task and both role prompts, declarations and write rules.
It is explicitly **not launchable**: consumed measurement profiles are not live
profiles, and no owner authorization or login is created. After code review,
CI and merge, fresh preparation must bind the final code, root/session identities,
assembled prompt bytes and target. Any changed project base requires preparation
again; no automatic rebase during the pass is implied.

Proposed judgment ceilings for owner review are **four hours shared, one hour
per invocation, five invocations**, comprising at most three implementer turns
and two reviewer turns: initial work, independent review, one rework/rereview,
then closeout. Claude has 60 responses total with the existing 30-response
reservation per invocation. Codex reports native usage without a token or
monetary cap; time and invocation caps are enforced. These are bounds, not a
forecast from the trivial smoke. A role can exhaust its allowance before
finishing; that is an incomplete attempt, not permission to extend.

Proposed owner attention is 15 minutes after login, with a 30-second cleanup
allowance. Any failed invocation, unknown write, missing pin, changed model,
unresolved required capability or budget expiry stops the pair; there is no
automatic replacement. Login is before the clock. Cleanup captures state,
halts the pair, verifies process identities, terminates and reaps owned groups,
checks protected files, and retires isolated logins after result review.

Success later requires substantive semantic improvement, independent approval,
qualified gates, archive/import and authorized local application without
coordinator content repair. A static pass leaves runtime integration, sustained
compaction, cross-game throughput and comparative cost unproven.
