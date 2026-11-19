# FG-1 launcher: first offline checkpoint

16 November 2026. The owner authorized the [launcher slice](FG1_LAUNCHER_SLICE.md)
with a two-hour checkpoint and sixteen-hour hard bound. This checkpoint supports
continuing the existing integration scope. It does **not** admit either client,
authorize inference, or start the fresh-game pass.

The target remains one substantive structured corridor, independently reviewed
and locally applied without coordinator content repairs. This slice connects
the capabilities already built; it adds no game work, scheduler or worker system.

## Delivered and measured

| Item | Result and limit |
| --- | --- |
| Prerequisite | [PR #196](https://github.com/khansen/nesrev/pull/196) merged at its reviewed head with green CI. The project branch was archived and rebased; its committed project tree, working files and four stashes were preserved. |
| Retained clients | Copied the complete accepted packages outside Homebrew's managed directories: 43 files, 749,302,300 bytes. Source and copy hashes, sizes and modes match; no symlinks. Old seals remain unchanged. |
| Fresh offline profiles | Prepared from those copies against a synthetic declared-input session. Model and effort are explicit, configurations remain unauthorized, and all workspace ancestors were checked for a Git repository. This is integrity preparation, not live admission or fresh-game preparation. |
| Learning guidance | Both roles now distinguish earlier **published** observations from an unpublished candidate whose observations must be carried forward. The canonical guidance is reused. Two real learning sections are refused; removing the section-count check is caught. |
| Watch route | A real structured handoff now reaches the existing `watch --notify` path. Each poll checks retained history and publisher state under the existing locks, which are released before notification. The notification identity includes the structured head. A bound watcher refuses a changed run or mode. |
| Smallest turn | Real watch command, real synthetic structured handoff, prototype notifier and stub client. The delivered 1,056-byte message matches exactly. A normal return leaves the authoritative state unchanged and records waiting for owner continuation; a repeat watch returns “no new turn.” |
| Refusals | Expiry starts no stub client; notifier failure starts none either. Neither writes a seen marker. Both preserve the message and result. These are component checks, not proof of the final launcher guard or process-tree cleanup. |

The first watch experiment exposed `STRUCTURED_COMMAND_UNAVAILABLE`: the CLI
had a watch command but its structured dispatcher rejected it. The small routing
change above closes that integration gap. Two test-harness corrections are also
retained: an in-memory mutation did not reach a verdict subprocess, and a test
mistook the pre-created workers directory for a delivery marker. Acceptance was
not weakened; direct parser and actual marker checks replaced those assumptions.

## Call graph and remaining edits

The planned production path is:

1. `agent_review_tmux.py --workflow structured` reads the prepared session and
   sealed authority, verifies the supported pair and workspace ancestry, and
   starts visible supervised workers.
2. The initial implementer task is a recorded message. Subsequent turns use
   `agent_review.py --repo <session>/handoff --expected-run-id <run> watch --notify <structured notifier>`.
   No main-checkout handoff is inspected or changed.
3. The notifier snapshots the exact message bytes and identity, rechecks the
   authoritative turn, and runs one adapter invocation under the shared heavy
   lock and deadline guard. It records the adapter result and re-reads service
   status before deciding whether a handoff occurred.
4. Claude uses `subscription_client.run_role`; Codex uses
   `structured_codex_client.run` with a narrow extension of `phase_message` for
   distinct recorded messages on the same thread. An initial task is not
   silently resent as the response to a review.
5. Existing qualified closeout and `application.apply` supply completion and
   local application under explicit authority. Client exit zero supplies neither.

| File or seam | Remaining work |
| --- | --- |
| `scripts/agent_review_tmux.py` | Opt-in preparation/routing, supported pair, visible result and recovery instructions. Ordinary launch remains its existing path. |
| Structured notifier/supervisor entry point | Connect recorded messages, shared authority, existing adapters and process supervision. The checkpoint notifier is private prototype code only. |
| `scripts/agent_review.py`, `structured_pass/structured_handoff.py` | Initial checked watch route is implemented. Integration must recheck message/turn identity at execution and test duplicate delivery and changed state. |
| `scripts/structured_codex_client.py` | Message selection and identity, same-thread continuation, ancestry check and declaration re-pin. Preserve tool inventory, audit, confinement and quiescence checks. |
| `structured_pass/subscription_client.py` | Ancestry admission, shared absolute expiry, immediate pre-launch deadline recheck, exact message identity and recorded allowance prefix. Preserve isolated configuration and restrictions. |
| `structured_pass/usage_budget.py` and existing process supervision | Keep observed usage in native units; bind existing role allowances to the same owner deadline. Add no response-equivalence conversion. |
| `structured_pass/service.py` and bridge error tests | Expose the existing `REVIEW_NOT_READY` refusal as a public typed error. |

The watch loop releases its locks before the notifier runs: otherwise the client
could not publish or record a verdict. Production notification still needs its
single-invocation guard and authoritative pre/post checks; this checkpoint does
not claim those are implemented.

## Pins and complete role inputs

The choices match the retained accepted profiles:

| Role | Copied client | Model | Effort |
| --- | --- | --- | --- |
| Implementer | Codex 0.167.0 with matching code host and package resources | `gpt-6-astra` | `xhigh` |
| Reviewer | Claude Code 2.1.319 | `claude-opus-5-5` | `high` |

Hashes and executable modes are verified offline. Live availability of those
models is untested for this new admission. There is no fallback to a newer
Homebrew executable or a default model.

The private packet records the full current implementer, reviewer and retained
reader declarations, including descriptions. It also records the expected Codex
native serialization, derived from the previous native declaration while
replacing its facts operation. **The adapter still has its old admitted native
pin.** The candidate declaration is not installed or live-observed. Final
integration must re-pin both service profiles and confirm the actual native
declaration before acceptance; preparing a profile alone does not do that.

Both fresh profiles assemble the declared-input fixture: current scope, guidance,
reference identities/media, historical intake evidence and two analogues.
Historical archive text remains on demand. The fixture has simulated gates and
synthetic media bytes; the live packet must use valid media and the complete
frozen role prompts. The actual fresh-game input set already accepted in the
[input-delivery slice](INPUT_DELIVERY_SLICE.md) must be refreshed with final tooling
before the pass. This checkpoint does not replace that preparation.

## Hook-disabled reviewer expectation

Offline inspection of the **copied, hash-matched 2.1.319 binary** found an
independent file-tool check. Its read permission function enters the restricted
path check before mode-derived allowances. That check compares resolved path
spellings with the working directory and additional-directory roots and returns
a restricted-mode denial for an outside path. Unresolved spellings also refuse.

This is the expected second layer. `dontAsk`, a small tool list, the deny entries
for other tools and an empty workspace are supporting configuration facts, not
substitutes for that read check. The native client is not OS-sandboxed.

There are explicit exceptions for certain client-owned files, including plans,
tool results, scratchpad, background-job temporary files, project temporary files
and bundled skill references. Therefore the claim is **not** that every path
outside the workspace is denied. Byte offsets and relevant code excerpts are
retained privately; this inspection is not a live denial result.

| Probe group | Placement | Expected enforcement with hook absent |
| --- | --- | --- |
| Synthetic source, model and instruction files | Separate fixture checkout/store outside all workspace roots | Restricted file-tool path check |
| Editor and handoff state | Synthetic service session outside the workspace | Same path check |
| Unselected reference and synthetic private canary | Separate sibling fixture directories | Same path check |
| Alternate spelling of an outside canary | Parent traversal from the workspace | Resolved-spelling check; require an actual Read attempt |
| Selected PNG/PDF | Copied into workspace | Positive controls: reads succeed |
| Service status | Strictly configured facts bridge | Positive control: operation succeeds |

Before sealing the smoke, prove every negative fixture exists, is readable by
the coordinator, and falls outside both working roots and the enumerated
client-owned exceptions. Include no actual secrets. A separate hook-off profile
omits the hook; never edit a sealed active profile. Any protected read succeeding,
or a model refusing without a tool attempt, stops that window.

## Result ownership and recovery

One sealed owner authority holds the absolute shared expiry. Each existing
adapter keeps its native usage ledger: Claude response identities and Codex native
turn/token records remain separate. Taking turns cannot reset the expiry.

Before every launch: verify authority, code/packages/inputs and source-free
ancestry; verify prior processes are gone; acquire the shared heavy lock and
single-turn guard; arm deadline supervision; then recheck expiry immediately
before creating the client process. Authentication happens before opening the
authorized window. A notifier failure must not become an automatic retry loop.

| Observed outcome | Classification and next action |
| --- | --- |
| Service records the expected next actor/head | Completed turn with handoff; deliver that recorded turn within remaining authority. |
| Client returns normally, service does not hand off | Unfinished, visibly waiting for owner continuation. Preserve the seen marker; continuation gets a new recorded message identity. |
| Deadline, quota or role allowance exhausted | Budget stop; preserve usage and partial output. Only owner extension permits another turn. |
| Denied unsupported work with missing evidence | Record incomplete evidence; no silent substitution or success claim. |
| Notifier/adapter failure or unfamiliar output | Preserve raw output, stop the worker, and require diagnosis before another invocation. |
| Protected read succeeds or cleanup is uncertain | Stop and block reuse; no broader access or automatic replacement attempt. |
| Service approves all edges and qualified closeout/application succeed | Complete this authorized pass only; no next pass or push. |

## Next implementation and smoke

The remaining work fits the original scope: connect tmux/notifier/adapters,
shared expiry and recovery; finish the exact-message and ancestry tests; then
freeze admission pins and a smoke packet. The rough remaining estimate is
**7–15 active hours**, within the original sixteen-hour hard bound after charging
this checkpoint. It is still a planning estimate, not measured throughput; live
authorization and review waits are separate. There is no new dependency
requiring a scheduler or worker project at this checkpoint.

The smallest planned live sequence has four invocations: hook-disabled reviewer
first; initial Codex fixture task; reviewer notified from its publication; Codex
receiving a distinct rework message on the same thread. The final packet must
specify exact prompts, required calls/results, role allowances, shared/per-turn
deadlines and cleanup. Independent calls may reorder; real dependencies may not.
No smoke is ready for authorization yet. Its proposed thirty-minute shared
window and zero retries remain a separate owner decision, followed later by
the separately authorized unscripted pass.

Final validation: **352 structured tests passed with one opt-in skip**, and
**105 ordinary handoff/launcher tests passed**. The section-count mutation was
caught. Strict playbook, repository-hygiene and whitespace checks passed; this
checkpoint did not run the full `make test` or CI.

About **50 minutes** are charged against the two-hour checkpoint, conservatively
including the elapsed coordination waits that were not measured separately.
The private effort record retains exact timestamps and heavy-job durations,
including failed attempts. Failed observations are retained. There have been
**zero provider calls**, and implementation stops here for the agreed checkpoint
review.
