# Opt-in structured launcher: decision record

Date: 12 November 2026. Status: draft for scope review. This record authorizes
neither implementation nor provider calls, profile admission or another project
pass. The owner has authorized preparing the guidance and this record.

## Outcome and boundary

Make the exercised structured workflow launchable through
`scripts/agent_review_tmux.py --workflow structured`. Reuse the existing review
store and notifier interface; tmux displays supervised headless turn output.
The owner steers between turns. Ordinary interactive launching remains the
default. This is an integration slice ahead of further Step 2B work, not
completion of 2B, 2C or default rollout.

The driving implementation agent owns the plan, effort accounting and
[reassessment checkpoint](../../agent_playbook/AGENT_SESSION_OPERATIONS.md#decision-checkpoints).
The reviewer may call that checkpoint independently; the owner decides.

## Scope needed for acceptance

| Area | Required behavior |
| --- | --- |
| Preparation and admission | Prepare isolated profiles without `tmp/` campaign dependencies; verify accepted binary identities, configuration, empty workspaces and service pins before inference. Fail on drift. |
| Pairing | Initially accept only Codex implementer and Claude reviewer on the exercised macOS arm64 setup. Refuse other pairings and untested platform claims. |
| Watch routing | Watch the session's `<session>/handoff` store, with recorded per-role prompts. Enable structured watch without redirecting it to checkout handoff state. |
| Notifier | Deliver the exact recorded message to one supervised turn under the shared heavy-run lock and deadline. Keep output visible and record its result. |
| Handoff and stops | Inspect authoritative state after the turn. Classify results using the shared [result categories](../../agent_playbook/AGENT_SESSION_OPERATIONS.md#stop-classification); never mark unfinished work as handed off merely because the client exited zero. |
| Continue and extend | A normal return without handoff waits visibly for owner continuation. Budget exhaustion waits for a recorded extension. Neither action automatically recovers a failed or uncertain run. |
| Public errors | Expose `REVIEW_NOT_READY` through the bridge and test that route. Preserve other unknown errors as internal errors. A service refusal alone is not a verdict on the entire turn. |

Pinned profile instructions own each role's duties. Handoff text supplies its
current task and report; owner messages provide recorded steering without
relaxing the role or access boundary. Audit the complete delivered input using
the [assembled-input check](../../agent_playbook/AGENT_SESSION_OPERATIONS.md#delivered-inputs).

Codex per-turn delivery must change only where message bytes come from and how
their identity is checked and recorded. Disclose the changed functions; preserve
tool, configuration and sandbox behavior. Retain the per-run message hash. Any
additional adapter change needs its own justification and affected checks.

## First experiment and completion evidence

Build the smallest notifier path early and run, once separately authorized, a
short supervised turn per role on disposable synthetic fixtures. Each must end
in the expected handoff or deliberately selected typed stop, with saved
observations and reconciled cleanup. Use actual emitted records to inform tests;
an unexpected stop is evidence for investigation, not a successful smoke result.

Acceptance also needs focused offline coverage of preparation refusal, watch
routing, unchanged-state return, continuation/extension, supported pairings and
the public-error correction. The real smoke should include Codex message
delivery on same-thread resume, since that is the adapter behavior being changed.
Reviewer receipt of its assembled message must be observed through the notifier.

Run the offline adapter suite after its final change, relevant launcher/watch
tests and required repository CI. Scope any further native checks to changed
behavior or concrete unresolved risk under
[proportionate verification](../../agent_playbook/AGENT_SESSION_OPERATIONS.md#proportionate-verification).
Retain accepted evidence for unchanged behavior within its
[documented limits](CODEX_CLIENT.md#established-evidence-and-limits); the old
preflight does not certify changed adapter bytes. This slice does not close the
open reference-media or reviewer-side confinement feasibility work.

## Effort and reassessment

Working estimate: 8–16 hours of active implementation and verification, with
review, quota and other coordination waits reported separately. This is an
uncertain estimate, not an authorized runtime or token allowance. Watch-state
integration and the changed Codex resume input are the main uncertainties.

Reassess before another round if any of these occurs:

- three implementation review rounds have completed without acceptance and a
  successful live smoke;
- the same failure class recurs twice;
- active effort reaches 16 hours, or new evidence makes that estimate untenable;
- a dependency becomes a separate client, service or evidence-framework project.

The driving agent records what is complete, the blocker, remaining cost and
the shortest alternatives. The owner decides the next step. These checkpoints
must not be met by weakening acceptance criteria or reducing documentation
quality. No failed live attempt automatically authorizes another.

## Clients and live environment

Use the existing retained Codex CLI 0.167.0 package, including its sibling code
host and resources, and the retained Claude CLI 2.1.319 executable. Select exact
absolute paths in local preparation records and profiles; never resolve the
client through `PATH`, a current-version link or the newest installed package.
Keep machine-specific paths out of tracked documentation.

| Component | Accepted SHA-256 |
| --- | --- |
| Codex CLI 0.167.0 | `030316ecfbb41f4e7946e584b0063ef333b7a36cd312ba349f2f6869e39b62cc` |
| Codex code-mode host | `5cc29d144fc05e3563f5f90c36adc95bdc287e2297b48ecf0bf4abdf1892d3ab` |
| Claude CLI 2.1.319 | `1f53587e92dee8e089fa349188a4cda64fa34ace6e7b0ca2ee278ddaa3cc2ebd` |

Keep the accepted per-role model and effort settings, including Codex
`gpt-6-astra` at `xhigh`, explicit in the preparation record. Apply the existing
[admission and package-upgrade rules](CODEX_CLIENT.md#admission-and-execution).
Do not rebase the project branch while an active session pins its ancestry.
Login precedes the separately authorized live window. Leave existing retained
client directories and sealed profiles untouched. Relocation remains parked;
if needed later, preserve the whole Codex package and validate fresh profiles
at the new paths.

## Parked

Other role pairings, interactive confined panes, reference-media expansion,
client relocation, broader Step 2B/2C work, the shared debt-plan writer,
`FORBIDDEN_PATH` detail improvements, preview and raw-RAM follow-ups, and the
earlier test/performance refinements stay outside this slice. The CI queue
incident alone does not justify workflow changes. Reopen a parked item only
with a concrete dependency or new evidence and an explicit scope decision.

This record applies selected lessons from the
[pilot retrospective](../retros/2026-11-12-structured-pass-pilot.md); it does not
turn the retrospective's remaining observations into work. Owner acceptance of
the scope and live-test authorization are the next decisions before execution.
