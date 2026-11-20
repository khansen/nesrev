# FG-1 readiness: early checkpoint

Historical checkpoint. The approved [continuation result](FG1_READINESS_RESULT.md)
records new native captures, complete write mapping and final checks. The stops
and results below remain unchanged.

20 November 2026. **Preparation passed; readiness is incomplete.** The
[approved slice](FG1_PASS_READINESS.md) has reached its repeated-failure stop:
two successive layout probes omitted requirements of the existing pass
contract. Neither is evidence against the prepared source or the boundary.
The failed observations remain in the private packet. No native client,
provider call, login, application or semantic pass has run in this slice.

## Completed and proposed changes

The owner authorized exposing published candidate identities in an existing
reviewer result. The implementation adds
`status.handoff.published_candidate`, with `cid`, `revision`, `attempt`,
editable `generation` and retained `ticket`. It selects only the published
candidate for the current reviewed head, while holding the existing publisher
lock. Draft or merely validated successors do not replace it. An artifact-only
handoff without an editor has no candidate identity.

The generated contract uses separate role histories:

| Argument | Implementer source | Reviewer source |
| --- | --- | --- |
| Mutation `cid` | `confirm.candidate`, then non-null `preview.candidate` | Not offered |
| `candidate_status.cid` | Same candidate sources | `status.handoff.published_candidate.cid` |
| `validation_evidence` identity | `validate.candidate`, `validate.revision`, `validate.attempt` | Published candidate's `cid`, `revision`, `attempt` |
| Ordinary generation | `status.generation` | `status.generation` |
| Review head / base | `status.handoff.coverage.pass_head` / `pass_base` | Same, from the reviewer's status |
| Ticket | `status.ticket` | `status.ticket` |
| Report sequence | `status.handoff.latest_review.sequence` | Same, from the reviewer's status |
| Input identity | `inputs.records[].id` | Same, from the reviewer's catalog |
| Preview digest | `preview.preview_digest` | Not offered |

The retained reader continues to obtain generation and review ancestry from
its own status and input IDs from its own catalog. It offers no candidate
operations. The lifecycle test checks every advertised path in both supported
profiles without borrowing the implementer's transcript for the reviewer.

`candidate_status` contains gate results. `validation_evidence` is an error-detail
reader, not successful validation history: after a successful attempt it can
correctly return `EVIDENCE_UNAVAILABLE`. The new help states this distinction.
This slice does not change that operation's semantics.

## Tests and declaration budget

The real-service lifecycle uses a revised candidate and an initial failed
setup followed by successful validation. The reviewer obtains revision 1 and
attempt 2 from its own status. After one verdict and a response, the test reaches
**round 2 with latest review sequence 1**, reads report 1, then reads report 2
after the second verdict. A separate test covers two published heads, an
unpublished successor, invalid metadata and wrong-head binding.

Five deliberate source faults are caught by this lifecycle test, without the
frozen client fixture: sequence from round, an implementer-only reviewer
source, a wrong candidate value, an omitted revision and a stale attempt.
The sequence fault fails the lifecycle's explicit argument assertion.

The final affected suite passed **51 tests, no skips**, in 60.0 seconds under
the shared heavy-run lock on macOS arm64: contract logic, identity lifecycle,
handoff, pair supervision and learning import. Playbook and repository-hygiene
checks passed. This is not the full structured suite or `make test`.

Earlier checks remain recorded: the identity fixture initially assumed four
gate rows although its simulated closeout produces one; the first supervisor
test run could not execute process inspection inside the command sandbox; and
an older metadata-only handoff fixture needed published-candidate records.
The fixture corrections did not change production acceptance. The process-test
rerun waited for command approval; that inactive wait is excluded from effort.

| Generated declaration | Top-level characters | Argument-contract characters | Listing bytes |
| --- | ---: | ---: | ---: |
| Corridor implementer | 4,027 | 3,684 | 8,755 |
| Corridor reviewer | 3,403 | 2,975 | 7,245 |
| Retained reviewer | 1,211 | 2,071 | 3,930 |

These are generated sizes, **not new native captures**. All fit the existing
4,096-character description and 24 KiB text limits. The implementer still has
only 69 top-level characters free. Both native fixtures and the Codex admission
pin remain unchanged and are stale for the proposed help. Full-suite and
client-delivery acceptance remain pending; this is not a release-ready head.

## Rebase, preparation and layout stop

The authorized rebase onto the launcher merge completed. All project-side
commits compare unchanged, the old head has a local archive tag, and the
owner's working files and four stashes were preserved. Exact identities are
private. An independent clone, including Git metadata and the inherited exclude
file, supplied fresh preparation; no prospective live state was consumed.

Preparation ran next-pass and pass-start, inventory, verification, process and
documentation checks, the generated-only check, and native certification.
It passed with 1,181 unresolved names: strict verification exited 3, then the
complete naming-only verifier exited 0. It is **not strict-green**. Both role
input assemblies were produced with the retained text, page and analogue pins.

First-use measurement then stopped twice:

1. A disposable notes-only preview omitted the mandatory scorecard/closeout
   operations. `CORRIDOR_WRAPPER_REQUIRED` refused it before candidate creation.
2. After adding the existing wrapper operations, the synthetic pass-1 scorecard
   omitted its authored analogue decision. Validation preserved ROM parity and
   passed naming-only verification and documentation checks, then the process
   check refused closeout. The service recorded `NEW_GATE_FAILURE`.

The second result does not establish an admission blocker: the unchanged
starting point passed process checks, and the dummy pass submission lacked
required content. It also does not establish a successful first use. Nothing
was published, watched, reviewed or applied in that real-layout probe. No
source, gate, baseline or acceptance rule was repaired to obtain a pass.

The preparation diff and rejected candidate are retained. The runtime exclude
append, watcher writes, client/profile writes and application changes have not
yet been observed for this slice; no complete expected-change list is claimed.

## Continuation for review

The pass-path map is still provisional:

| Obligation | Existing route and owner | Checkpoint evidence or remaining limit |
| --- | --- | --- |
| Selected inputs and comparisons | Both roles: `inputs`, `input`, `guidance`, `navigate` with the pinned analogue selector | Fresh assemblies; native delivery pending. Manual analogue selection remains an operator step. |
| Corridor analysis | Both roles: `navigate`, `inspect`, `query`, `search`, RAM evidence | Existing admission applies to unchanged operations. Compact expansion, shared sets and the eight-request practicality ceiling still need inclusion in the live matrix. |
| Semantic and document edits | Implementer: `preview`, `confirm`, `validate`, `publish`, using existing typed operations and closeout fields | Synthetic identity lifecycle passes. The real-layout dummy candidate was refused; it is not semantic acceptance. |
| Independent review | Reviewer: `status`, `review`, `candidate_status`, error evidence when available, verdict with Learning Candidates | Role-local identities tested; changed native declaration not yet captured. |
| Rework | Implementer: `review_report`, edits, `reready`; reviewer rereview | Unequal round/sequence witness and two distinct reports tested. |
| Closeout, archive and learning import | Implementer `closeout` after approval; coordinator application | Existing synthetic recovery tests remain the appropriate plumbing fixture. Complete observed-write rules are pending. |
| Local application | Coordinator-only application to the authorized branch and target | No application authorized or performed here. Target preimages, reference, index and unrelated files must still be checked at launch/application. |

This table is not the final sealed operation/limit matrix. A runtime trace,
new policy writer or broader input requirement still invokes the existing stop.

Do not attempt another fabricated semantic closeout on the real project.
Keep its successful preparation as starting-state evidence. Use the already
planned four-phase synthetic native recipe, with its known complete operations
and full handoff Git metadata, to collect actual initialization and watcher
diffs. Use the existing full-lifecycle synthetic application fixture for archive,
import and retry writes. These remain plumbing evidence, not semantic progress.

After checkpoint review, the remaining work is to capture both clients and
refresh the changed pins, complete the pass-operation matrix and observed-change
rules, run final checks, and prepare the separately authorized live request.
Estimate **3–5 further active hours**, within the original eight-hour ceiling,
conditional on no new stop. All four credential-free native invocations remain
unused. There is no provider or game-pass authorization.

The code changes remain review work in progress. The accepted r5 evidence still
belongs to its original declarations; it does not admit these changed ones.
