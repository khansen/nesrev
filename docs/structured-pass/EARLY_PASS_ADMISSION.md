# Early-pass admission: measurement and scope proposal

15 November 2026. **Checkpoint 1 and offline implementation complete.** The
owner authorized the four-to-eight-hour implementation after accepting the
[measurement record](EARLY_PASS_ADMISSION_CHECKPOINT.md). The
[implementation evidence](EARLY_PASS_ADMISSION_IMPLEMENTATION.md) records the
lifecycle, refusal controls, qualified results and remaining search overflows.
No provider call or working-project restart was made.
The [search retrospective](../retros/2026-11-15-structured-typed-search.md)
closes the preceding milestone.

## Outcome and priority

Allow a legitimate early semantic pass to use the structured service while
names remain unresolved, preserving parity and every other applicable check.
This removes one entry barrier on the
[fresh-game path](TRIAL_WORKLOAD_COVERAGE.md#minimum-path-to-one-fresh-game-pass-through-the-service).
It does not supply intake, runtime integration or launcher delivery.

| Alternative | Reason for this order |
| --- | --- |
| Admission measurement first | Establishes whether the blocker is only mode propagation or includes other unmet contracts before committing to an implementation estimate. |
| Launcher first | Makes supported mature-project work easier to launch, but fresh projects still fail admission. Its intake/admission interface must reflect this result. |
| Workflow jobs or worker integration first | Needed for the complete path; neither removes the current entry refusal. |
| Continue ordinary passes | Already permits incomplete naming, but does not establish the structured path or remove its measured intervention burden. |

Start the eventual fresh-game milestone from the owner running existing intake
once with supplied inputs. Require a new intake service operation only if the
selected pass exposes a concrete need. This proposal makes no new intake or
launcher implementation commitment.

## Checkpoint 1: measure before estimating

**Authorized allowance: at most two active hours**, including setup, gate execution
and reporting, with no provider use. This is an investigation bound, not an
implementation estimate. The driving agent owns measurements and the checkpoint;
the reviewer can raise a stop, and the owner decides whether to proceed.

Pin a private corpus manifest before running checks. Select at least three
distinct retained source states spanning intake and early semantic work,
including the previously refused snapshot and the source used for the heavy
search measurements; do not count rebased copies of the same source as broader
coverage. Record exact commits, source/reference and authored-artifact hashes,
current master/toolchain pins, selection reasons and any unavailable input.
Game identities, input paths and raw logs stay in the private packet.

Use disposable copies with the pinned current tooling and the selected
snapshot's project inputs, including required shared project artifacts. Copy
ignored reference inputs and verify their hashes. Reuse the preparation flow's
generated next-pass/plan setup with a fixed diagnostic selection. Record allowed
generated changes; do not repair authored files, baselines or gates to obtain
admission. Leave the working project branch and saved sessions untouched.

For each snapshot, run the four canonical structured checks sequentially:
`project-inventory`, `project-verify`, `project-process-check` and
`project-docs-check`. First retain the strict verification result. For an
unresolved-name refusal, also run verification with the existing documented
`ALLOW_UNRESOLVED_LXXXX=1` mode. The measurement driver may explicitly select
that existing mode in its disposable copy; production service admission remains
unchanged during this checkpoint.

Use the service's pinned gate environment, adding only that explicit diagnostic
exception for relaxed verification. Run each top-level check even when a
preceding check failed, retaining the dependency context. Internal checks after
a wrapper's first failure remain **not run**; do not infer their success. Keep
per-check exit codes, modes, elapsed time, log hashes, label counts and changes
to generated files. Missing prerequisites are recorded as blocked, never passed.
Also run preparation's generated-only change check and native source
certification, preserving their results independently. If prerequisites or the
bound prevent either, record it as blocked or not run; the four gates alone
cannot earn a go. This measures preparation readiness, not a newly admitted
service session or historical replay.

Tag every extra failure with its evidenced cause: a property of early-stage
code, tooling/artifact drift since the snapshot, or an environment/pin problem.
Keep uncertain causes explicitly unresolved rather than assuming admission
scope. A check introduced after a snapshot is not by itself evidence that
early-stage code needs a weaker contract.

The earlier 11-commit survey was naming-only. Its one preparation refusal
stopped at verification step 3 of 4; sixteen subsequent checks in
[`project_verify.sh`](../../scripts/project_verify.sh), plus process/docs gates,
remain unmeasured by that attempt.

**Go/no-go:** if every selected snapshot passes all non-naming checks and both
final preparation checks, propose the bounded mode/evidence integration and
its estimate. Any additional failure
is a new scope finding: report it and the unrun checks before estimating or
implementing a fix. Finish the already defined diagnostic matrix within the
allowance, but add no repair loop. Stop for missing inputs, pin drift, unsafe
execution dependencies or the time limit. Report a partial matrix honestly.

## Service-owned mode, if implementation is selected

Reuse the [existing semantic-pass verification contract](../../agent_playbook/PASS_WORKFLOW.md#semantic-pass-verification),
the closeout's relaxed mode and the review runner's strict-first fallback.
Define one trusted decision from the immutable pass starting source:

- A zero canonical unresolved-name count selects strict verification. A later
  candidate that introduces generic names must fail; it cannot switch modes.
- A nonzero starting count makes an early semantic pass eligible for the
  naming-only exception. Strict-first evidence must identify the naming refusal;
  relaxed verification and all other gates must then pass. The count is an
  eligibility condition, not evidence that naming is the sole failure.
- Gold, maturity and semantic-completion checks always run strict, regardless
  of the pass's starting count or inherited environment.

Identify the naming refusal from the verifier's own exit status or a structured
result, not `make`'s exit status or matching log text: `make` returns 2 for any
failed recipe, including a verifier exit of 3. A successful relaxed verification
proves that the naming exception was sufficient, because it retains the same
preceding and subsequent checks. The strict run is a cross-check; its early
refusal alone cannot prove that no other failures exist.

The service computes and seals the decision before agent mutations, with the
base/source identity, canonical naming predicate and starting count. It records
distinct-name and reference counts before and after. Agents, job code, request
fields, candidate documents and inherited environment variables cannot select
or overwrite the mode. Validate that binding on load/resume and before applying
changes; missing or changed mode evidence refuses rather than choosing a default.

Carry the same trusted policy through
[`prepare.py`](../../scripts/structured_pass/prepare.py),
[`service.py`](../../scripts/structured_pass/service.py), closeout and
[`application.py`](../../scripts/structured_pass/application.py). The
[`gate_environment.py`](../../scripts/structured_pass/gate_environment.py)
exception must be service-generated, not an ambient-variable passthrough.
Review, scorecard, gate and application receipts must distinguish relaxed
success from strict-green. Removing the last generic name does not establish
strict completion without an actual strict verification run.

## Acceptance after implementation authorization

| Case | Required evidence |
| --- | --- |
| Retained early source whose only strict failure is naming | Full preparation, candidate validation, review/closeout and application to a disposable target succeed with the same recorded policy and hashes. |
| Same source with a real defect | Independent mutations for ROM-byte mismatch, warning-baseline mismatch, comment-audit failure and data-extent failure are each refused. Each control reaches its intended gate; unrelated setup failures do not count. |
| Initially clean source gains a generic name | Strict mode remains selected and the candidate is refused. |
| Attempted mode changes | Agent/request/environment overrides cannot relax a strict pass; altered or missing sealed mode/base evidence refuses, including after resume. |
| Reporting and completion | No relaxed result becomes strict-green in review, closeout or application; gold/maturity/completion remain strict. |
| Four heavy search questions | Repeat the pinned predicates and context requests through an actually admitted service on the corresponding retained source. Compare complete oracle results and request counts, explicitly recording proxy substitutions or unavailable snapshots. |

Override tests must try `ALLOW_UNRESOLVED_LXXXX` and `VERIFY_MODE` separately
and together. Also assert that closeout's third argument comes from the pinned
service policy: neither inherited variables nor caller fields may change that
argument or confer relaxed eligibility on an initially clean source.

Keep the eight-request limit and 24 KiB response ceiling. A repeated search
overflow is a recorded usability gap, not a failed admission fix or a complete
fresh-game acceptance. Compact match lists, grouped summaries and query changes
are outside this slice and need a later decision. Never credit the old
unit-level measurements as admitted-service evidence.

The post-measurement scope must name changed functions, data/receipt compatibility,
the estimate and hard bound, and one implementation review round. Reassess on
a repeated failure class, a new capability dependency or the bound. Run focused
positive/refusal tests with failing controls, affected regressions and required
Linux/macOS CI; no live client is needed for this admission slice. Approval of
the proposal or a successful checkpoint does not automatically start coding.

## Post-checkpoint implementation proposal

The [completed measurement](EARLY_PASS_ADMISSION_CHECKPOINT.md) found no extra
gate failure. **Proposed estimate: four to eight active hours, hard bound eight,
with one implementation review round.** This is a judgment estimate for mode
propagation, evidence and tests, not an extrapolation from the one-minute gate
matrix. Review waiting and remote CI elapsed time are separate. The owner authorized this slice on 15 November; the bound and checkpoint below
remain the record of that decision.

| Change area | Intended work |
| --- | --- |
| `prepare.prepare` and `current_project.service_class` | Compute and pin policy from starting-source identity and canonical naming counts; validate the policy and baseline evidence when opening the profile. |
| `gate_environment.environment` / `closeout_environment`, with a shared service-owned policy helper | Keep the default environment strict. Issue the existing naming exception only from validated policy, for the applicable verification command; never inherit it from the caller. |
| `Service.run_gates`, current-project gate dispatch and application `apply` | Apply one policy consistently, preserve strict diagnostics, record effective mode and before/after counts, and re-check the binding on resume/application. |
| `mixed_documents.run_closeout` and `Corridor._closeout` | Use the wrapper's existing relaxed mode when eligible; validate its qualified scorecard result rather than requiring or manufacturing an unqualified `pass`. |
| Review/archive evidence | Carry the recorded mode into review and closeout output. Preserve strict gold/maturity/completion behavior and reject unsupported mode claims. |

Exact function changes will be listed in the PR. No tool operation gains a
caller-selectable verification mode. Reuse the canonical verifier's naming
predicate; do not substitute a new interpretation of which names count.

New current-project profiles must carry an explicit versioned policy binding.
Old profiles and receipts stay with their original pinned readers; no automatic
migration or missing-field default may confer relaxed eligibility. Re-preparing
on the new tooling creates a new profile. Fixture-only services remain strict
unless an explicit test fixture supplies the same trusted policy contract.

At two active hours, report whether a retained early snapshot can be prepared
with pinned mode evidence and an initially clean fixture still refuses an
introduced generic name. Stop for reassessment if that seam reveals another
admission dependency. The remaining acceptance is the full table above:
candidate validation, review/closeout, application, refusal controls, receipt
integrity and the four heavy-query measurements. Existing strict-path tests
must continue to pass; deliberate faults must show the mode/refusal assertions
can fail. No client adapter, provider run or fresh game pass is required.

The estimate excludes search redesign, broader gate changes and old-session
migration. Any such dependency, a repeated failure class, or exhaustion of the
bound returns to the owner with evidence instead of expanding this slice.

## Separate follow-ups

Search redesign, intake automation, launcher implementation, broader policy
waivers, mapper support and worktree/concurrency integration remain separate.
The reviewer hook-disabled check belongs in the next authorized client smoke.
For [#188](https://github.com/khansen/nesrev/issues/188), propose at most 30 active
minutes for race reproduction before isolating each test mode's fixture;
do not make reproducing a rare interleaving a prerequisite to that isolation.
If audit loss recurs with fresh fixtures, retain it as a separate adapter finding.
That correction does not belong in admission, and it must preserve the audit
assertions rather than hide failures with sleeps or retries.
