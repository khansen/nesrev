# NESrev manifesto: the process is the product

**The gold of NESrev is its reverse-engineering process.** Disassemblies and
documents are artifacts that the process should be able to recreate. Its lasting
value is the reusable knowledge, tools, evidence practices and orchestration
that make high-quality reverse engineering repeatable across unfamiliar games.

This is the basis for repository priorities. The playbooks define how to do the
work; this manifesto defines what that work is for.

## Begin with the end in mind

Given a user-supplied ROM and reference material, one standard workflow should
carry a game through intake, code and data recovery, semantic passes, runtime
evidence, independent review and honest closeout. It should expose unresolved
questions and its evidence limits, preserve useful work across interruptions,
and resume without depending on a particular agent's conversation or the
owner reconstructing what happened.

The ambition is to make this practical for hundreds of games not yet started.
That requires safe unattended work, reliable recovery, affordable execution and
the ability to run independent games without interference. The owner's role
should concentrate on supplying references, setting goals and budgets,
resolving genuine ambiguities and accepting results. Routine handoffs, retries
within an authorized recovery policy and bookkeeping should not require the
owner to operate the workflow one pass at a time.

These are objectives to demonstrate, not claims that today's workflow already
meets them. A bounded successful pilot establishes only the capabilities and
conditions it actually exercised.

## Recreated artifacts must earn trust

Replaceable outputs still have to be correct, readable, maintainable and useful
to an experienced NES programmer. Binary identity, semantic evidence, reference
identities, runtime validation where needed and independent review remain the
quality bar. A process that produces more files or greener mechanical metrics
without better-supported understanding has not improved.

Reproducibility means comparable, evidence-backed understanding and quality
from declared inputs. It need not mean identical symbol spellings, prose or
pass counts. Retain the inputs, tool and configuration identities, decisions
and evidence needed to explain and evaluate a result.

Treating outputs as replaceable is a design goal. Existing work and historical
evidence remain subject to the repository's preservation rules; this manifesto
does not authorize their deletion or regeneration.

## Use projects to validate the process

The existing corpus is a source of reusable knowledge and a validation set.
Work on an existing game is valuable when it tests a capability, exposes a
general limitation, supplies an analogue or meets an explicit owner objective.
Its accumulated debt or proximity to completion does not automatically make
it the next priority.

A completed disassembly is a comparison source, not an infallible answer key.
Possible evaluations include a rerun that withholds that game's existing
artifacts from the agents, followed by work on a genuinely unstarted game.
Compare supported semantic claims, coverage and quality, and disclose possible
prior exposure through model training. Any trial needs its own question, budget
and authorization; this manifesto selects no trial.

## Put first things first

Choose work by how much it advances a dependable, reusable workflow for new
games. Ask which limitation currently prevents that outcome and what evidence
would show that the proposed change removes it.

Compare improving the ordinary workflow, adding structured capabilities and
making a smaller fix at the measured bottleneck. None has priority by name.
A new tool, service, rule or review round earns its place through the capability,
reliability or cost improvement it can demonstrate. Reusable infrastructure can
be the right investment; its anticipated reuse does not by itself justify an
unbounded detour.

Use the existing [decision checkpoints](../agent_playbook/AGENT_SESSION_OPERATIONS.md#decision-checkpoints)
to state the alternatives, expected benefit, effort, uncertainty and reassessment
triggers. Keep experiments and implementation stages small enough to learn from
before committing to the next stage. A well-scoped task can still be the wrong
next task.

## Measure progress at the process boundary

Evaluate quality and operating cost together:

- **Quality and generality:** evidence-backed identities and behavior,
  meaningful coverage, readability, review findings and performance on
  unfamiliar games and architectures.
- **Operator effort:** interventions, approval requests, manual handoffs and
  time spent recovering or reconstructing state.
- **Reliability:** completion and recovery under the promised conditions,
  preserved state and evidence, containment, and truthful stop reasons.
- **Cost:** tokens and provider usage, elapsed and active time, rework and
  maintenance, measured against a comparable accepted result.

Pass counts, test counts, merged PRs and artifact volume are activity measures;
they do not establish these outcomes. Mark unmeasured costs as unknown, and
separate demonstrated feasibility from comparative improvements. Use
[milestone retrospectives](../agent_playbook/DOCUMENTATION.md#milestone-retrospectives)
to retain what was learned and suggest the next improvement without turning
every observation into new work.
