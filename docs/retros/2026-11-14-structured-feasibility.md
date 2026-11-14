# Structured execution feasibility: milestone retrospective

**Observed and written:** 14 November 2026. The
[accepted decision](../structured-pass/FEASIBILITY_DECISION.md) records results,
limits and evidence identities. This retrospective suggests improvements; it
does not add policy or authorize the next slice.

## Outcome against the purpose

The checkpoint answered a process question: can useful analysis, emulator work
and reviewer access operate within boundaries suitable for unattended work?
Python and emulator jobs did useful work under App Sandbox, with per-job transfer,
protected-access denials and bounded cleanup. The reviewer used selected media
and facts without approval prompts. The reviewer hook's independent fallback
still needs testing. No production worker or fresh-game workflow was delivered.

This reduces a real technical uncertainty in the
[manifesto's](../MANIFESTO.md) destination. It does not establish lower cost,
better quality or owner-free operation across games. Existing artifacts served
as evidence of workload needs; advancing a game was not the milestone.

## What helped

Unsandboxed controls made the denial results meaningful: the same protected
accesses worked without the boundary. Per-job inputs arrived after signing and
outputs were collected, so a passing bundle could not merely read its own
fixtures. Dependency and process observations separated packaging failures from
boundary failures. Failed observations remained available for independent review.

The later shakedown used one bounded allowance for local harness corrections.
Two fixes and a complete installed-runtime run took about 13 of 45 minutes,
without another authorization per correction. The final package then passed all
eight cases in one sequence, using about 20 of 60 authorized minutes. Those
intervals include preparation and reporting; they do not erase earlier effort.

## What cost avoidable effort

We initially inferred runtime needs from static links and familiar APIs. That
missed SDL3's dynamic load and assumed LuaSocket existed. The probe also guessed
a frame-count floor and relied on emulator termination behavior it had not
demonstrated. These mistakes stopped runs before they could answer the boundary
question and created unnecessary review and authorization cycles.

The corrective sequence worked: prove the whole job on the installed runtime,
measure every loaded library, then package and compare control with sandbox.
The reviewer harness had the analogous problem: an exact ordering of independent
calls exceeded both the claim and the prompt. Checking actual dependencies
instead, with negative controls, preserved the useful acceptance requirement.
These were preparation and review gaps, not evidence that a model or OS failed.

Evidence collection also needed care. One observer appended after an early hash;
the prefix relationship was explained and the full record retained. Waiting for
the observer to exit before sealing removed that ambiguity in the final run.

## Improvements to carry into the next slice

Use the retained workload to define behavior before inventing abstractions. For
search, distinguish facts available through practical queries from facts that
could theoretically be recovered by reading every page. Count actual calls,
and retain no-match, incomplete and unresolved outcomes as different results.

Prove a harness on the known-good route before spending a boundary attempt.
Within an agreed allowance, classify and fix local harness errors while keeping
their observations; return to the owner for a new capability, broader access or
a failed boundary. Apply the existing
[proportionate-verification guidance](../../agent_playbook/AGENT_SESSION_OPERATIONS.md#proportionate-verification)
rather than building another campaign around every correction.

Record actual active effort by component. The package maintenance cost is now a
concrete tradeoff to compare with a VM; the investigation has not measured that
comparison. Keep typed search, worker integration and launcher delivery separate
decisions, each justified by the workload and its acceptance test.
