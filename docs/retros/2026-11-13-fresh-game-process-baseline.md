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

Read-only command approvals were the most frequent recorded intervention.
However, the more consequential reliability finding was a restart after its
authorization had expired. Recommend **deadline enforcement inside the ordinary
launcher's session lifecycle** as the next bounded improvement. It should prevent
late launches and stop the owned clients at expiry without relying on the
coordinator remembering the deadline. Permission friction remains the strongest
candidate for reducing recurring supervision after that boundary works.

## What ran and what it established

The trial used the ordinary tmux launcher on macOS, Codex CLI 0.167.2 with
`gpt-6-astra` and Claude Code 2.1.322 with `claude-fable-5-2`, both at `xhigh`.
The agents received the default task; a separate coordinator kept measurements.
Default pass-cycle permissions were selected, with existing broader grants
disclosed. Those grants are not a filesystem containment boundary.

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
supervision. The last owner estimate was 15 active minutes across the trial.
Later approvals and coordination have unknown active durations, so neither the
final owner total nor compliance with the one-hour active-time allowance is
established. Coordinator active time was not measured. Five-minute observation
also added possible detection delay to permission waits; no total approval-wait
duration is claimed.

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

## Alternatives and priority

| Candidate | Expected benefit, evidence and cost | Decision at this checkpoint |
| --- | --- | --- |
| Native deadline enforcement | One actual late launch and an external guard that could not stop an unregistered workspace. A small integration can remove reliance on coordinator timing; estimated below. | Recommend first because bounded unattended spending needs this boundary. |
| Reduce routine inspection approvals | Twenty approvals are strong evidence of recurring friction. Audit existing read/search routes and reference extraction before adding narrowly scoped operations; arbitrary helper execution cannot be declared read-only by filename. Implementation cost is not yet scoped. | Next candidate for operator-effort reduction; no blanket grant proposed. |
| Quota recovery | Quota ended the resumed segment and a review checkpoint survived. A bounded wait/resume policy could reduce reconstruction and intervention; it cannot create quota or extend an owner deadline. Provider-specific detection and replay make this a larger, unscoped change. | Preserve the checkpoint; assess recovery after the spending boundary is enforceable. |
| Model or context-cost experiment | Recorded input exposure warrants investigation. There is no comparable Opus run or measured quality/cost tradeoff yet. | Honor the model preference; defer comparative claims and further inference. |
| Structured launcher and services | The accepted launcher option was estimated at 8–16 active hours, but structured new-project intake remains outside the current roadmap. Runtime coverage is also incomplete. | No evidence here justifies selecting that broader work ahead of the smaller reliability fix. |
| Mapper coverage and concurrency | NROM/MMC1 support excludes other architectures; one managed session per checkout leaves multi-game workspace and resource management unresolved. This supported-game trial could not measure either gap or the affected library share. | Keep visible as strategic alternatives; no automatic implementation queue. |

These priorities combine severity, recurrence and scope. They are not a measured
ranking by minutes saved: intervention durations and comparative implementation
costs are incomplete. A successful same-checkpoint resume would add recovery
evidence, but would not erase the earlier failures or complete the fresh-game trial.

## Proposed next improvement and acceptance test

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
to their hashes; raw logs, reference paths and project-specific details are not
published with this report. Verification here was read-only evidence reduction
and document checking, not a new provider run or test campaign.

The trial was deliberately partial, used one supported game and one platform,
and crossed an authorized tooling correction and an assistance-policy change.
Its strongest result is a concrete account of what still required supervision.
It does not establish per-game throughput, semantic repeatability, unattended
completion, or superiority of the ordinary or structured workflow.
