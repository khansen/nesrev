# Fresh-game process baseline: assessment and proposed trial

Date: 12 November 2026. Status: reconciled assessment and recommendation;
game selection, configuration, budgets and execution authorization remain pending.
This plan records the next proposed experiment under the [manifesto](MANIFESTO.md).
Merging it starts neither trial preparation nor provider usage. It does not authorize
another project pass, a tooling change or a later trial stage.

<a id="assessment"></a>
## Assessment and priority recommendation

The ordinary workflow has produced independently reviewed results from fresh
starts, including runtime evidence. Those records include owner interventions
and explicit evidence limitations; they do not establish unattended completion
or a measured cost per game. The structured pilot demonstrates durable state
across a client change and confined static work within its
[tested limits](structured-pass/CODEX_CLIENT.md#established-evidence-and-limits).
The [pilot retrospective](retros/2026-11-12-structured-pass-pilot.md) makes no
comparative token, quality or speed claim.

The recommendation is one instrumented fresh start using the ordinary launcher.
It has the broadest implemented workflow coverage and can expose where owner
effort and execution cost arise. The intended deliverable is a supported choice
of one next process improvement. Another disassembly is a by-product.

Compare these alternatives against that question:

| Alternative | Benefit and remaining uncertainty |
| --- | --- |
| Measured fresh start | Tests the unfamiliar-game workload and establishes an operating baseline; cost and completion time are unknown. |
| Targeted ordinary-workflow improvement | Can remove an existing intervention; choose directly if owner experience or retained evidence already identifies a sufficiently important bottleneck. |
| Structured launcher | Makes the exercised static workflow reusable through the existing launcher; its accepted scope has an uncertain 8–16 active-hour estimate and does not provide fresh-game coverage. |
| Broader structured services | Can extend controlled operations and runtime execution; substantial coverage remains, and the current plan excludes new-project intake. No end-to-end delivery estimate is established. |
| Mapper coverage or managed concurrency | Opens additional workloads or increases throughput; these structural gaps require explicit comparison even when the trial cannot encounter them. |

The [structured launcher](structured-pass/LAUNCHER_DECISION.md) remains an
accepted bounded option, not selected implementation work. The assessment is a
recommendation; the owner may select a known bottleneck directly instead of the
trial. If semantic repeatability is the immediate question, a held-out rerun is
an alternative, with prior model exposure and artifact access disclosed.

<a id="structural-gaps"></a>
## Structural gaps to keep visible

| Gap | Established boundary | Implication for the decision |
| --- | --- | --- |
| ROM coverage | [Intake](../agent_playbook/NEW_PROJECT.md#rom-support-matrix) accepts only NROM and MMC1 within its size/header limits. | A supported-game trial cannot measure the excluded library. Assess mapper priorities against the owner's intended games; the affected share is not yet measured. |
| Structured intake | [Step 2 scope](structured-pass/STEP_2_COVERAGE.md) explicitly excludes new-project intake; 2B recovery operations do not change that. | Even completing the currently specified 2B/2C work would leave a fresh-start gap. |
| Recovery | The [ordinary launcher](../README.md#start-a-project-with-two-agents) documents manual recovery after exit or usage-limit stops. Structured budgets preserve interrupted accounting and require owner recovery. | Durable state and fewer prompts do not establish automatic recovery. A safe, bounded recovery policy is separate work. |
| Independent games | The launcher refuses two managed sessions in one checkout; separate checkouts and session names provide part of the structure. | Workspace, branch/integration and resource management remain to be demonstrated. Do not remove the guard to claim concurrency. |
| Runtime and confinement | Agents own [capture and analysis](../agent_playbook/RUNTIME_EVIDENCE.md#agent-capture) before human handoff. Structured runtime workers and parts of client/media feasibility remain open. | Human judgment may be needed, but runtime work is not inherently owner-operated. Ordinary grants and bypass are not the structured containment boundary. |

<a id="trial"></a>
## Proposed trial and frozen setup

Select one small, previously unstarted NROM game for which the owner supplies
the ROM and manual. Confirm the actual header and supported sizes through intake;
a title shortlist is not evidence about the supplied revision. Avoid a title
with a widely circulated complete disassembly when practical, and disclose
possible prior model exposure. Keep project identity, private input paths and
raw client logs in the local project records, not this shared plan.

Use the ordinary launcher with **default pass-cycle permissions**. This is the
recommended baseline, pending owner acceptance. Freeze the repository revision,
client and tool versions/hashes, role pairing, models, effort, effective
permissions, task inputs and reference identities. Read both complete delivered
prompts under the existing
[input-review guidance](../agent_playbook/AGENT_SESSION_OPERATIONS.md#delivered-inputs).
Record existing broader grants; the requested mode alone does not prove the
effective boundary. A mode change ends the frozen segment and must be disclosed.
Include log preservation in the frozen setup: keep private copies of the relevant
session logs before automatic client cleanup and before reducing them.

Do not change tooling or permission profiles during a measured segment. Record
an unexpected dependency and stop for a decision. Any authorized correction
creates a new configuration and separately labelled segment; it cannot erase
the original result. Keep client installations and the active project's base
stable while the run depends on them.

<a id="stages"></a>
## Stages and proposed budgets

| Stage | Proposed bound and endpoint |
| --- | --- |
| Preparation | At most two active agent hours. Complete the existing setup checks, input/configuration record and measurement plan. Optionally spend up to one hour of this allowance checking usage-log coverage for a recent completed pass whose logs remain within retention, to inform the token allowance. Do not build a telemetry framework. |
| Stage 1 | One eight-hour elapsed observation window from the first trial model invocation, including readiness turns and quota/coordination waits. Record the achieved scope or earlier stop. This is a spending limit, not a prediction of game completion. |
| Checkpoint | If a sufficiently important bottleneck is clear, recommend the intervention. Otherwise report what remains unknown and propose the smallest further observation. |
| Possible stage 2 | Separately budget and authorize remaining static work and independent review against the existing criteria, with runtime gaps explicit. This is not a new mechanical maturity gate. |
| Possible stage 3 | Separately budget and authorize a runtime corridor and its review if needed to answer the remaining process question. Earlier runtime evidence may make this unnecessary or change its scope. |

Stages are spending checkpoints, not restrictions on evidence. Obtain runtime
evidence whenever an earlier claim requires it, or leave that claim unresolved.
Do not postpone necessary captures to manufacture a static-only success. Full
reviewed closeout remains the end-to-end target; a partial stage does not establish
complete per-game cost, quality or unattended operation. No stage or unused
allowance automatically authorizes the next.

Before launch, the owner selects a usage allowance and an active owner-time
limit in addition to the elapsed window. The ordinary launcher has no aggregate
token limiter. Record who monitors usage, the observation interval, known
accounting delay and the action taken at the threshold or loss of usable
accounting. Describe a monitored allowance as such; do not promise a hard token
cap. If the owner requires a mechanically enforced cap that this setup cannot
provide, resolve that mismatch before launch. Also record how the coordinator
will stop/checkpoint the roles at the deadline using the existing controls.

<a id="measurement"></a>
## Measurement and evidence

Use existing logs, handoff records and review archives. The coordinating agent
outside the trial owns measurement and checkpoints; the trial implementer and
reviewer receive the unmodified default task, without measurement duties.
The owner supplies actual active-time estimates where logs cannot establish
them. Preserve observations before reducing them.

| Measure | Record and limitation |
| --- | --- |
| Owner touches | Time, role, cause, action, actual active minutes or unknown, and evidence. Categories: references/missing input, semantic judgment, permission, quota, recovery/crash and coordination. Separate initial setup from in-run intervention, and active time from waiting. |
| Usage | Per-role native usage and its session/run coverage. Handle cumulative counters and duplicate/resumed records correctly; retain cache categories and identify missing or interrupted accounting. Tokens are not automatically monetary cost or comparable provider units. |
| Time | Trial and stage boundaries, waits and available role/round events. Commit timestamps bound history; they do not measure active execution. |
| Quality | Review verdicts, rework, supported semantic claims, evidence gaps and waivers at each checkpoint. Green mechanical metrics do not establish semantic completeness. |
| Reliability | Quota stops, crashes, normal unfinished returns, restarts, retained state and any lost or uncertain evidence. Reconnection alone does not prove recovery. |

Historical log extraction must establish coverage before presenting totals.
Report partial coverage as partial; do not reconstruct missing owner time from
tool-call duration. Retain raw logs privately and export only the relevant
reduced measurements, without credentials or unrelated conversation content.

<a id="stop-rules"></a>
## Stops and reassessment

Stop the measured segment when:

- the elapsed window, agreed usage threshold or owner-time limit is reached;
- the same operational blocker class stops work twice, or one blocker already
  makes further observation uninformative;
- a parity failure requires owner judgment, or a tooling dependency blocks work;
- the frozen configuration must change, or evidence integrity/containment is
  uncertain.

Ordinary review rework and agent-repairable project defects remain part of the
measurement, subject to existing quality gates and budgets. The recurrence rule
does not authorize a retry; any continuation follows the existing authority and
recovery rules. Classify the result using the
[shared stop categories](../agent_playbook/AGENT_SESSION_OPERATIONS.md#stop-classification).
The driving agent calls the checkpoint, the reviewer may raise it independently,
and the owner decides whether to continue, change scope or stop.

<a id="decision"></a>
## Deliverable and outstanding owner decisions

Produce a short report of measured bottlenecks, known structural gaps and
remaining uncertainty. Rank them by expected benefit to repeatable new-game
work, cost and evidence strength. Recommend one next improvement with an
acceptance test and a bounded effort estimate. An informative early stop can
justify a process decision while remaining an unfinished project.
Use the [milestone retrospective](../agent_playbook/DOCUMENTATION.md#milestone-retrospectives)
guidance without creating a second duplicate report or turning every finding
into implementation work.

Before any execution, record the owner's choice of:

1. The trial versus directly addressing an already established limitation.
2. The game and supplied reference set, held in local project records.
3. Exact role/client/model/effort configuration and acceptance of the recommended
   default permission mode.
4. Preparation and stage-1 allowances, usage-monitoring arrangement, owner-time
   limit and deadline-stop procedure.
5. Authorization to prepare and launch stage 1, including provider usage.

All five are pending. Later stages, implementation of the recommended fix and
the structured launcher require separate decisions.
