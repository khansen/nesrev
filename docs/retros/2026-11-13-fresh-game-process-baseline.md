# Fresh-game process baseline: checkpoint assessment

**Observed:** 12–13 November 2026. **Written:** 13 November 2026.
**Tooling snapshot:** master `92b8c9c50`, including PR #182.

This is the first checkpoint report under the
[process baseline plan](../PROCESS_BASELINE_PLAN.md), assessed against the
[manifesto](../MANIFESTO.md). It recommends one next improvement; it does not
authorize implementation, another trial window or a change to the quality bar.
Project identity, supplied references and raw transcripts remain in local records.

## Conclusion

The ordinary workflow produced an approved intake and an approved first semantic
pass on a previously unstarted, supported game. A second semantic pass was
committed but its review stopped at the reviewer's quota limit. This establishes
useful early progress with assistance, not unattended operation, static maturity
or a cost per completed game.

Recommend **reducing routine reviewer approval friction first**. Twenty inspection
approvals accounted for 73.6 minutes of waiting, about 47% of the resumed segment,
on the critical path to the implementer's next turn. Begin with a one-hour
read-only audit of those commands to separate existing tool routes, reference
preparation and operations that need a permission-boundary decision.

The initial assessment ranked launcher deadline integration first without
measuring this wait. The measurement changes that ranking. The late restart
remains an authorization failure, but arose in the coordinator's launch procedure
and consumed about 69 seconds. Correct that procedure before another window;
defer native launcher deadline integration until longer unattended windows make
it the selected need. The owner decides which work to authorize.

## What ran and what it established

The trial used the ordinary tmux launcher on macOS, Codex CLI 0.167.2 with
`gpt-6-astra` and Claude Code 2.1.322 with `claude-fable-5-2`, both at `xhigh`.
The agents received the default task; a separate coordinator kept measurements.
Default pass-cycle permissions were selected, with existing broader grants
disclosed. Those grants are not a filesystem containment boundary.

The subsequent approval audit established the size of that limitation: the
reviewer inherited 107 local allow rules, including broad Python and Make grants,
alongside its generated role profile. It also loaded personal auto-memory;
the implementer's user rules were not isolated. The observed prompted/unprompted
split therefore describes this machine's configuration, not repository-only
permissions. Explicit settings sources and a new measured baseline precede any
claim of portable approval reduction; the [permission plan](../CLAUDE_PERMISSION_PLAN.md)
records that correction and the separately authorized next steps.

| Segment | Outcome and timing |
| --- | --- |
| Initial eight-hour authorization | Stopped after 2h 30m 10s, before the first review. An unrelated article draft blocked the clean-tree check. After a separate project repair, the saved initial handoff had no supported way to advance to the repaired head. |
| Restart after PR #182 | Both clients ran readiness turns after the original deadline. They were stopped about 69 seconds after the first recorded native start, before review delivery. This was an authorization failure, not a successful continuation. |
| Separately authorized four-hour window | Ran for 2h 38m 10s including waits and shutdown. Intake and the first semantic pass were approved in round one; the second semantic review remained unfinished. Quota reset was later than the deadline, so the coordinator stopped the workspace. |

The article request-to-resume interval was **100m 12s**, measured between native
transcript events. It is elapsed waiting, not owner active time or time spent
computing. The article was unrelated to the pass; the later head mismatch
followed a separate project repair. [PR #182](https://github.com/khansen/nesrev/pull/182)
fixed those two handoff defects, and its tooling change is a segment boundary.

The late restart exposed a different fault: the deadline was checked during
preparation, but not at the actual client launch. Its external guard had already
exited without a registered workspace. The coordinator initiated the late launch;
neither client was responsible for enforcing an allowance it had not been given.
The failed attempt and its provider usage are retained.

## Quality, effort, reliability and cost

**Quality.** Both completed reviews approved their scoped work without a blocking
correction round. They still recorded six and eight numbered nonblocking findings,
respectively, including reference coverage, unsupported prose and analogue reuse.
Those findings show independent examination; approval does not mean zero rework.
Project gate failures during the next implementation were repaired before handoff.
Its reviewer saved completed checks, unchecked work and next steps without a
verdict. This assessment reuses those records; it did not rerun project gates or
perform a third semantic review. No runtime or final-maturity acceptance resulted.

**Effort.** The resumed window recorded **20 reviewer inspection approvals**:
two individually authorized by the owner and 18 handled by the coordinator under
an explicit read-only delegation. Commands included source and analogue searches,
reference extraction, CSV summaries and inspected byte-checking helpers. Every
approval was one-time; permission settings stayed unchanged. Some requests used
compound shell commands rather than the existing standalone inspection helpers,
so the evidence does not establish that all twenty require new tooling.

Delegation moved work from the owner to the coordinator; it did not eliminate
supervision. All twenty recorded commands matched native Bash calls exactly.
Method: match each command to its call, pair the result by tool-use ID, and time
call to result, splitting at the coordinator's recorded approval timestamp.
The intervals do not overlap: 73.6 minutes precede approval and 3.5 seconds follow
it. The latter rounds to 0.1 minutes and includes command execution plus
delivery/logging overhead; it is not independently instrumented execution time.

| Review | Approximate UTC interval | Approvals | Wait to recorded approval |
| --- | --- | --- | --- |
| Intake | 05:29–06:42, about 73 minutes | 13 | 63.5 minutes; the first request alone took 22.5 minutes |
| First semantic pass | 06:54–07:14, about 20 minutes | 7 | 10.1 minutes |
| Total | 158.2-minute resumed segment | 20 | 73.6 minutes, or 46.5% (about 47%) of the segment |

The implementer waits for the review verdict, so this delay sits on the critical
path. Five-minute coordinator observation contributed detection delay. An owner
watching continuously might shorten it, but would still be supervising approvals.
These measurements do not imply that a permission change would reclaim every
minute or remove later quota limits.

The last owner estimate was 15 active minutes across the trial.
Later approvals and coordination have unknown active durations, so neither the
final owner total nor compliance with the one-hour active-time allowance is
established. Coordinator active time was not measured. Measured approval waiting
is elapsed delay, not either person's active time.

**Reliability.** After the handoff fix, ordinary verdict transitions delivered
the next turns automatically. A Codex context compaction was followed by continued
work. The final quota stop preserved the partial review, transcripts and clean
tracked checkout; process inspection found no remaining trial clients or watchers.
These are preservation and shutdown results. Resuming that unfinished review has
not yet been demonstrated. The quota was observed at about 07:42 UTC and shutdown
completed at 07:57:56 UTC; it was not an immediate or automatically enforced stop.
The native reviewer had advertised continuation at 10:00 UTC, beyond the
09:19:45 UTC deadline. Closing the client prevented that continuation.

**Usage.** The following native counters cover the resumed four-hour segment,
including readiness and unfinished review. They are recorded lower bounds.

| Role | Input accounting | Output accounting |
| --- | --- | --- |
| Codex implementer | 13,290,400 input tokens, including 12,966,144 cached | 62,344 output tokens, including 23,648 reasoning |
| Claude reviewer | 176 uncached input; 499,562 cache creation; 25,494,066 cache reads | 124,546 output tokens |

Codex uses the last cumulative counter, not a sum of snapshots. Claude uses
distinct assistant-message IDs, retaining the largest recorded counter per
category for each ID; streaming duplicates and cache-creation subcategories are
not counted again. Cache hits repeatedly expose context; they are not millions
of distinct source tokens. These providers' categories are not interchangeable
prices or quota units, and the account quota includes activity outside this trial.

Earlier usage is separate: the initial segment recorded 10,868,549 Codex input
and 34,520 output tokens; the late restart recorded 101,779 input and 487 output.
Claude's readiness turns in those segments also consumed usage: respectively
2/43,228/23,377/4 and 2/43,259/23,377/4 for uncached input/cache creation/cache
read/output. Coordinator work and development of PR #182 are outside these
figures. Complete workflow cost, preparation effort and cost per accepted
semantic outcome remain unmeasured.

The owner selected Opus 5.5 for future Claude launches after this stop. It has
not been exercised in this trial. Any continuation is a new model segment;
these observations do not establish that switching reduces cost or restores quota.
Approval waiting itself consumes no inference tokens. Removing that wait could
bring the quota stop earlier in elapsed time; a future window should record
usage per review to assess that next constraint.

## Alternatives and priority

| Candidate | Expected benefit, evidence and cost | Decision at this checkpoint |
| --- | --- | --- |
| Reduce routine inspection approvals | Twenty approvals delayed review by 73.6 minutes. Audit existing read/search routes and reference preparation before adding narrowly scoped operations; arbitrary helper execution cannot be declared read-only by filename. | Recommend first, beginning with a one-hour read-only audit; implementation is bounded after that audit. No blanket grant proposed. |
| Coordinator deadline procedure / later launcher integration | The late restart consumed 69.5 seconds, 101,779 Codex input tokens (59,008 cached), 487 output tokens and one reviewer readiness turn. Its cause was the coordinator's procedure. | Recheck expiry at launch and arm/verify the guard before another window. Defer launcher integration; retain its acceptance tests below. |
| Quota recovery | Quota ended the resumed segment and a review checkpoint survived. A bounded wait/resume policy could reduce reconstruction and intervention; it cannot create quota or extend an owner deadline. Provider-specific detection and replay make this a larger, unscoped change. | Preserve the checkpoint and measure usage per review next time; quota is a likely subsequent throughput limit. |
| Model or context-cost experiment | Recorded input exposure warrants investigation. There is no comparable Opus run or measured quality/cost tradeoff yet. | Honor the model preference; defer comparative claims and further inference. |
| Structured launcher and services | The accepted launcher option was estimated at 8–16 active hours, but structured new-project intake remains outside the current roadmap. Runtime coverage is also incomplete. | No evidence here justifies selecting that broader work ahead of the measured approval bottleneck. |
| Mapper coverage and concurrency | NROM/MMC1 support excludes other architectures; one managed session per checkout leaves multi-game workspace and resource management unresolved. This supported-game trial could not measure either gap or the affected library share. | Keep visible as strategic alternatives; no automatic implementation queue. |

The approval ranking now rests on measured critical-path delay as well as
recurrence. Active operator time, avoidable share and comparative implementation
costs remain incomplete. A successful same-checkpoint resume would add recovery
evidence, but would not erase the earlier failures or complete the fresh-game trial.

## Proposed next improvement and acceptance test

This was the assessment's original proposal. The completed audit led to the
[permission plan](../CLAUDE_PERMISSION_PLAN.md), which supersedes the sequence
below while retaining the requirement for equivalent inspection evidence.

**Outcome:** routine reviewer inspection proceeds through appropriate existing or
narrowly scoped tools without owner or coordinator approval for each read.
Start with **at most one active hour of read-only audit**, if the owner selects
this work. Classify all twenty requests against the tools actually available and
the effective permissions. The independent review's preliminary split is roughly
ten compound read/search commands, five reference-extraction/hash commands and
five reviewer-authored helper or inline-Python commands; the audit must confirm it.

For each request, identify whether Read/Grep or the existing symbol-search helper
already serves it, whether retaining extracted reference text at intake removes
repeated work, or whether executing custom code requires a separate trust decision.
An approved filename does not make changing Python code read-only. Return a
bounded implementation proposal, expected approval reduction and unresolved
boundary choices; do not implement or widen grants during the audit.

Acceptance for the selected change is that every request classified as avoidable
has a demonstrated route producing equivalent inspection evidence without
per-command approval. Out-of-scope writes, installation, Git mutations and
arbitrary code must not gain permission through that route. A separately
authorized review smoke should confirm the expected reduction, record approvals
and usage per review, and disclose Opus 5.5 as a configuration change. If the
audit cannot establish a small scope in one hour, return the findings for an
owner decision instead of expanding the work.

Before any further window, the coordinator must recheck the authorization deadline
immediately before starting clients, after preparation and consent waits, and
arm and verify the guard before launch. An expired allowance or exited guard
prevents launch; confirm workspace registration before releasing the handoff.
This is a prerequisite on the coordinator's next launch procedure, not a claim
that the launcher already enforces it. No new window is authorized here.

## Deferred launcher deadline integration

The earlier proposal and its acceptance tests remain available if the owner
selects them later, particularly for routine long unattended windows.

**Outcome:** an explicitly bounded ordinary-launcher session cannot start or keep
running native clients beyond its recorded authorization. Put the small control
in the existing launcher rather than another private campaign script. Keep role
prompts, permission policy and review verdicts unchanged.

Acceptance should exercise these concrete cases with controllable fake clients
and a clock, followed by a separately authorized short native smoke if needed:

1. An already-expired deadline launches zero clients. Permission/readiness delays
   that consume the remaining allowance also prevent a subsequent client spawn.
2. Expiry between the two role launches stops the first and prevents the second.
   Failure to establish the owned workspace's deadline supervision prevents
   handoff and leaves no running client.
3. An active session, including a client waiting to auto-resume after quota,
   stops at the deadline within a declared and tested shutdown tolerance. It
   preserves handoff state and available logs and checks owned descendants;
   unrelated sessions are untouched.
4. Normal handoffs still work before expiry. Reconnect or resume cannot silently
   replace the saved deadline with a fresh window. Extending it requires an
   explicit owner decision recorded outside either trial role.

Estimate **4–8 active engineering hours including focused tests, plus one light
review**, with uncertainty around native child cleanup. Reassess at four hours
if the design needs a new supervisor framework, or when the same failure class
survives a correction. The driving agent calls that checkpoint; the owner decides.
Automatic provider retries, token caps, generic read-only command classification,
new permission grants, structured integration and multi-game scheduling are
outside this proposed change. Nothing in this report starts it.

## Evidence and limits

The assessment used preserved launch/stop records, the article-wait observation,
handoff blocker and restart result, the resumed segment's intervention log,
private transcript copies, two committed reviews and the unfinished review
checkpoint. A local assessment index maps these sources and the usage reduction
to their hashes. The revision adds all twenty call/result matches and the approval
wait reduction without changing the original evidence; raw logs, reference paths and project-specific details are not
published with this report. Verification here was read-only evidence reduction
and document checking, not a new provider run or test campaign.

The trial was deliberately partial, used one supported game and one platform,
and crossed an authorized tooling correction and an assistance-policy change.
Its strongest result is a concrete account of what still required supervision.
It does not establish per-game throughput, semantic repeatability, unattended
completion, or superiority of the ordinary or structured workflow.
