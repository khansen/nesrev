# Proof-Debt Signals and the Identity Pass — Specification

Status: retrospective. The rules this argued for live in
[AGENTS.md](AGENTS.md) and [agent_playbook/](agent_playbook/); this records why
they exist and what was rejected along the way. It is not itself normative — if
it disagrees with a playbook, the playbook wins.

The review questions in the final section were written for the change's own
review and are kept as the record of what was contested.

**The terms this shipped under**, agreed at review and still binding on anyone
extending it:

1. **The signals stay advisory and opt-in.** Every check exits `0`; none can
   fail a build; they run only where `PROOF_DEBT_REQUIRED="1"` is set.
2. **The thresholds are corpus-fitted tripwires, not proven invariants.**
   Twelve constants, all chosen by looking at a corpus that is not a controlled
   experiment (§5). Re-run the backtest before changing any of them.
3. **The identity pass is reachable, not validated.** The recommender now asks
   for one at the right moment; whether running one produces good names is
   unproven, and only a real pass answers it.

Promoting any signal to a hard gate means revisiting all three. §5.1 states the
condition that binds every signal before any such promotion, and what the
nearest candidate would additionally need.

## 1. Problem statement

A disassembly project can pass every gate, preserve binary identity across
thousands of renames, maintain its warning baseline and rename ledger with real
discipline, and still arrive at a codebase that does not describe the game it
came from.

That is not hypothetical. It is the measured state of one project in this
corpus after 89 committed passes:

| Signal | Value |
|---|---|
| Committed passes | 89 |
| Renames logged | 3,294 |
| Binary parity | preserved on every pass |
| Terminology-crosswalk terms mapped to code | 0 of 65 |
| Semantic claims recorded | 0 |
| Passes recording a deferral | 41 of 89 (46%) |
| Deferrals citing dynamic/runtime/trace | 14 |
| Trace plans authored | 0 |
| `WORKING_NOTES.md` | does not exist |
| Largest symbol family with no matching reference term | 222 symbols |

Every individual pass in that history is defensible. Each one names what its
corridor proves, states honestly what it is leaving out, updates the ledgers it
touched, and preserves parity. The scorecard prose is unusually precise about
its own limits — rows name the exact RAM addresses whose ownership stayed out
of scope.

The aggregate is a game-agnostic disassembly.

One caveat, because this evidence is easy to overstate. The absence of manual
terms — no enemy, item, or character names anywhere in the source — is *not*
itself the finding. Declining to name a routine after a manual entity on thin
evidence is correct restraint, and the project's own crosswalk rule requires it.
What is decisive is the pair restraint cannot explain: not one of sixty-five
reference terms mapped to code after 3,294 renames, and the same identity family
deferred pass after pass with no record of what would close it. Restraint
declines to name a thing; it does not decline to record that the thing is still
unnamed.

### 1.1 Why local compliance produced global drift

The process is built on **corridor-local evidence**: prove ownership from the
code in front of you, do not reach. That rule is correct, and it is why the
mechanical quality of this corpus is high.

But identity evidence is never corridor-local. Establishing that a routine
family implements a specific named entity normally requires placement or spawn
data, behavior dispatch, render or sprite tables, and an external reference
document — four corridors and a source outside the ROM. No corridor pass can
justify that from inside its own boundary, so every corridor pass correctly
defers the identity question.

Repeated across 89 passes, "correctly defer" becomes "never decide". The
Corridor Execution Contract reinforces this by design: *"Do not expand into
unrelated subsystems merely because a token or literal matches."* Cross-corridor
synthesis is precisely what identity naming needs, and the playbook had no pass
shape that permitted it.

The observable residue is a large symbol family built on a plausible generic
noun phrase. Such a name passes every existing check: it encodes no address, no
ordinal, no raw hex, and it reads as semantic. The stale-placeholder audit
matches `State03`, `Page0600`, `AddrC000` — it structurally cannot match a
phrase that merely means nothing. And because the name *looks* resolved, it is
arguably worse than an unresolved `LXXXX` label: later passes build on it.

### 1.2 Why the existing gates did not catch it

Three distinct mechanisms, each verified in the source rather than inferred:

**Gates that check existence, not currency.** The crosswalk gate proves
`TERMINOLOGY_CROSSWALK.md` exists with the canonical header at intake. Nothing
checks it is still being maintained. Every crosswalk reference in `scripts/` is
an existence check.

**Gates that reward absence.** `working_notes_maturity_check.sh` returned
`OK: not present; no working-notes maturity debt` and exited 0 when the file was
missing. A project that defers pass after pass and keeps no notes passed the
notes gate *because* it kept no notes.

**Metrics that auto-fill their own best value.** `project-pass-closeout` seeded
new scorecard rows with `rework_items: "0"` and backfilled `0` over any blank or
`pending` cell. All 89 rows read `0` — not because the operator claimed zero
rework, but because the tool wrote it. A metric that defaults to its best value
is worse than no metric: it looks like data.

**Gates that fire too late to steer.** `data_format_targets.csv` and
`data_blob_dispositions.csv` are enforced by `project-maturity-check`, a
terminal gate the playbook explicitly says not to run early. Eighty-eight passes
elapsed with 8 of 11 core data families still `not_yet_reviewed` and nothing
said a word.

### 1.3 The session conditions

The 89 passes were run unattended: work until no substantial progress is
possible without dynamic analysis, commit each pass, do not stop for feedback,
follow the process meticulously, expect later review.

That instruction is reasonable, and it was followed. Parity held on every pass,
friction was logged as asked, and the stop condition was never falsely claimed —
790 unresolved labels remain, so continuing was correct. But it removes human
review for the entire run, which is the condition under which slow drift
compounds, and it phrases the exit in terms of dynamic analysis, which gives the
most attractive deferral a second reason to be attractive. Nothing in it asked
for identity or vocabulary outcomes, so what got optimised was what was
measured: label count, parity, green gates.

The instruction did not cause the gap. It removed the mechanism that would
otherwise have caught it, which is precisely the mechanism these signals are
meant to replace.

### 1.4 The design claim

> However detailed the playbooks are, a clear signal to the operator at the
> moment of decision is the only thing that reliably changes behavior.

The playbooks already contained every rule that was violated. The crosswalk
synchronization protocol is mandatory. The placeholder policy requires revisit
conditions in `WORKING_NOTES.md`. State-machine symbolization is per-value.
Rules were not the missing ingredient. Feedback was.

## 2. What is proposed

### 2.1 Name the missing pass shape

A **cross-corridor identity pass** — the one sanctioned exception to the
corridor-boundary rule. It opens no new code. Its objective is to decide what
already-named machinery *is*, by fusing evidence from several closed corridors
with the reference material.

Preconditions (all required): the machinery is already named and parity-stable;
at least two independent evidence channels exist; the crosswalk holds candidate
terms the pass can discharge.

Evidence standard: **two independent channels must agree.** A shared handler is
not identity — entity families routinely share movement, collision and render
code, so reaching a routine from one entity's data proves it is *used by* that
entity, not that it *is* it. Stop at the first family member whose channels
disagree and record the disagreement. A wrong identity name is worse than a
structural one, because it reads as settled.

Deliverable: crosswalk rows moved off `reference-only` with their evidence;
family-wide renames in one scripted batch; a semantic claim per resolved family;
and for a partial result, the proven subset named with the missing evidence
channel recorded.

This pass shape is *enabled* by the corridor work that preceded it, not a
replacement for it. It could not have run at pass 10 — the machinery was not yet
named.

Whether it can run *now* is two different questions, and the answer differs.
Where a subject has been deferred three times or more, yes: the cheap corridors
have already been tried on it and did not close it, which is why the recommender
ranks that case above them. Where the only evidence is vocabulary drift, the
honest answer is not yet — a project with hundreds of unresolved labels has
cheaper work available, and that trigger sits below the cheap corridors
accordingly. The playbook's three-strikes rule and the ranking now say the same
thing; an earlier draft had the prose issuing an interrupt the ranking quietly
overrode.

### 2.2 Proof debt as a ratio

Transformation recorded against evidence recorded:

| Signal | Fires when |
|---|---|
| `crosswalk_unmapped` | Under 25% of crosswalk terms map to code |
| `semantic_claims_empty` | Semantic naming complete, zero claims recorded |
| `deferrals_uncaptured` | ≥15% of passes defer, ≥2 recently, no ledger |
| `deferrals_unclosed` | Over half the open deferrals lack a revisit condition |
| `deferral_repeat` | One *subject* deferred ≥3 times without closing |
| `runtime_deferrals_unscheduled` | ≥5 operator-promoted runtime gaps, no trace plan |

Ratios where a denominator exists — mapped terms against total terms, unclosed
deferrals against open ones, deferring passes against all passes. Two are
deliberately not ratios: `semantic_claims_empty` is a completion binary because
gold closeout requires at least one claim and there is no denominator for how
many a project should have, and `deferral_repeat` is a count because three is
the threshold the escape rule names.

The distinction matters. A trigger that fires only at exactly zero is silenced
permanently by one row or one empty file — which is *"gates that reward
existence, not currency"*, the defect §1.2 diagnoses. The first implementation
had that bug in three places: mapping one of sixty-five terms killed
`crosswalk_unmapped` forever, and touching a `WORKING_NOTES.md` killed the
deferral signal. Both now measure proportions. No per-project threshold tuning, and the
message carries its own evidence: *"3,294 renames logged across 88 passes, but 0
of 65 crosswalk terms map to code"* lands where *"zero mapped terms"* does not.

Reported by `project-next-pass`, above the evidence buckets, because proof debt
concerns work already done and must be read before choosing what to do next.
`project-next-pass` is the mandated resume step; the maturity dashboard is
opt-in, and a signal the operator must choose to see is not a signal.

### 2.3 Dismissal must be cheap and durable

A heuristic over judgement calls cannot be made never-wrong. The design target
is therefore not zero false positives — unachievable — but **zero cost per false
positive.**

Adding a row to `inventory/proof_debt_acknowledged.csv`
(`signal,reason,pass_id`) silences that signal permanently. A row without a
reason is ignored: the ledger's value is the recorded judgement, not the
silence. This is the contract `constant_magic_allowlist.csv` and
`WARNING_BASELINE.txt` already use.

This inverts the design problem. Rather than making the detector smart enough
never to be wrong, disagreement becomes a one-line, permanent, *documented*
act — and the accumulated dismissals become their own evidence artifact.

### 2.4 Capture deferrals where they are made

This is the piece that addresses cause rather than symptom.

Deferring is normally correct. The failure is deferring with no record of what
would close the gap, so the next pass to reach the same edge starts from nothing
and defers again.

The operator already writes the deferral, in the closeout notes. Closeout reads
its own `NOTES` and appends rows to `inventory/deferrals.csv` (`pass_id,corridor,subject,kind,deferral,revisit_condition,status`).
`revisit_condition` starts empty and is the operator's to fill; proof debt
raises it until they do.

**One row per gap, not per sentence.** A closeout note is mostly a list of work
done with the gap as a trailing clause — *"Reflowed the touched tables, added
extent assertions, refreshed inventories, and left save-RAM field names out of
scope"* — and a single clause routinely defers several things at once. Storing
the sentence buries the subject under accomplishments and makes the ledger
unqueryable, so capture extracts the deferred clause and splits its list. On the
motivating history this turns 42 sentences into 98 individual gaps, each one
closable on its own.

**Keyed on subject, not corridor.** `deferral_repeat` must recognise the same
gap across passes. The first implementation keyed on the pass focus line, which
is unique per pass by construction: replaying the real history produced 41
distinct corridors from 42 rows, so the signal built to break a defer-forever
loop could not fire at all. Rows now carry a `subject` — the deferral sentence
reduced to its distinctive nouns, crudely singularised so *identities* and
*identity* agree. The same replay then surfaces four subjects deferred three or
more times, object-type identity among them, which is the fossilisation this
whole document is about.

The key is approximate by construction and will merge some distinct gaps and
miss some genuine repeats. That is the right trade against a key that never
matches anything.

False-positive risk is low because the trigger is the operator's own words,
though the clause parse is a genuine step that can mis-split unusual phrasing.
The incentive changes rather than the volume: deferring stays cheap, deferring
*without recording what would close it* stops being free.

The ledger is deliberately **not** `WORKING_NOTES.md`. Those notes are
unstructured by design — curated prose under a maturity line budget — and
appending every deferral would turn them into the pass log the documentation
rules forbid. A deferral has fields worth keeping structured: which corridor,
static or runtime, what would close it, whether it is still open. A CSV also
makes repeat deferrals queryable, which is what the repeated-deferral escape
rule needs and what prose cannot answer.

This was the one new authored artifact reviewed and kept on its merits; the
provenance-coverage report, proposed later as a second file, was rejected on
the same test and built as a derived mode instead.

### 2.5 Runtime deferral is a scheduling claim, not an evidence gap

A static deferral admits incompleteness: the evidence exists in the ROM and
nobody has assembled it yet. A runtime deferral asserts something stronger —
that the evidence *cannot* be obtained from the desk because the value depends
on live input, RNG, timing, scenario state, or emulator-visible state. The
classification procedure therefore obliges it to become a trace plan naming the
expected signal and promotion criteria.

This makes "needs dynamic analysis" the most attractive deferral available. It
is unfalsifiable from the desk, it sounds rigorous, and — unlike a static
deferral — it appears to be somebody else's problem. Where a session's stop
condition is itself phrased in terms of dynamic analysis, it is also the exit.

In the motivating project, 14 of 41 deferrals cite dynamic, runtime, trace, or
capture. Zero trace plans exist. Seven of ten comparable projects in the corpus
do author them. The runtime classification was terminal rather than scheduled.

The narrow definition matters here. Identity and liveness questions — which
entity a handler family implements, whether a slot is reachable — do not depend
on live input, RNG, timing, or scenario state. They depend on evidence that is
entirely in the ROM but spread across corridors. Under the definition they are
static-resolvable, and the honest disposition is an identity pass, not a trace
plan. A cross-corridor static gap that gets filed as runtime-gated is
misclassified in the direction that ends the conversation.

Captured deferrals therefore carry a `kind`, and
`runtime_deferrals_unscheduled` fires when runtime gaps accumulate with no trace
plan. The action text restates the definition, because the most likely correct
response is re-classification rather than a capture session.

**`kind` is never inferred.** The first implementation classified on wording,
matching *dynamic* — so *"left dynamic feature-id meanings out of scope"* was
stamped `runtime`, which is precisely the identity question this section argues
is desk-resolvable. The tool automated the misclassification the rule exists to
prevent, then demanded trace plans for evidence already sitting in the ROM.
Capture now always writes `static`; `runtime` is an explicit operator promotion
(`--kind runtime`). Asserting that evidence cannot be had from the desk should
cost a deliberate decision, not a word choice.

A project with no ledger yet still gets a prose-derived warning, since the
alternative is no signal at all — but the moment a ledger exists it is the whole
truth, and the wording says *recorded as* rather than *classified as* to keep
that provenance visible.

### 2.6 Claims are gated on completion, not volume

The claims signal first triggered on rename volume, which is the wrong axis.
The ledger is a gold-closeout artifact by its own definition — a pass records a
claim when it matures a subsystem, and most passes touch nothing there. Volume
crosses any reasonable threshold inside the first twenty passes, so the signal
would have nagged from the early midpoint of every project onward.

It now fires only once semantic naming is complete and the ledger is still
empty. Note what that costs: a project with settled subsystems mid-run is no
longer prompted to claim them. That is the deliberate trade — a signal that
fires early and often stops being read, and the crosswalk and deferral signals
already cover mid-project drift.

The corpus cannot settle where this line belongs. The claims ledger postdates
most of the projects in it, so their first-claim pass numbers record when the
artifact was introduced, not when the project was ready. The gate follows the
playbook's own wording instead, and is deliberately the conservative reading.

### 2.7 Coverage, not existence

Every signal above asks whether an artifact exists and keeps pace. None asks
how much of the work it accounts for, and that is the question a reviewer
actually has: *is this assembly justified?*

Every name in a disassembly is invented, so a named label with no reasoned
rename row is a decision nobody can trace. Measured across the whole corpus the
range is 1% to 97%, not the 3–38% an earlier draft reported from a partial
sample — and it was invisible, because the entire KPI suite reads only the
assembly. Not one script reads `renames.csv`,
the crosswalk, or any other authored ledger. Gates validate a ledger's schema
and never its completeness, which is how a schema-valid ledger hides what it
omits.

`proof_debt.py --coverage` joins the assembly against the ledgers that already
exist and reports the fraction each accounts for: named labels against the
rename ledger, reference terms against the crosswalk, deferrals against their
revisit conditions. Only rows carrying a *reason* count — a row without one
records that a rename happened, not why. It is derived and stores nothing: no
new authored artifact, and a mode on the existing detector rather than a
sibling script.

This is a different axis from the documentation KPIs, with the opposite target.
Those ask whether a symbol carries a comment and must not be driven to zero,
because high comment coverage is a redundancy smell. Provenance coverage asks
whether a naming decision carries a recorded reason, and should approach 100%.

**What it is not.** It measures ledger discipline, not whether names mean
anything — and the project this entire spec is about scores highest in the
corpus at 97%. That single fact disqualifies it as *the* answer to "is this
assembly justified": the project with the best provenance coverage is the one
whose vocabulary never reached the game. Nor is it clean across vintages; the
low scores are mostly projects that predate the rename-ledger discipline, so
1–8% is vintage rather than debt.

It is a useful hygiene metric and a fair size-independent comparison between
projects of the same era. It is not the yardstick for a from-scratch redo, and
a maturity gate with any useful floor would currently fail most of the corpus.

### 2.8 The rules belong in the process, not the prompt

An unattended run needs the rules a reviewer would otherwise supply. Carrying
them in the kickoff prompt makes them optional — they apply only when whoever
starts the run remembers to type them, and the prompt grows with every failure
mode discovered.

The outcome standard therefore joins the Mission: the finished disassembly
should read as a description of *this game*, taking names from the reference
material wherever the code proves the mapping. A codebase that could describe
any game in its genre has not finished naming.

The unattended-session rules join the proof-debt section: signals are blocking,
three strikes on a repeated deferral, triangulate before declaring a gap
runtime-gated, and a session ending on runtime evidence ends with an executable
trace plan rather than a claim that static work is exhausted.

What remains in the prompt is the goal and the exit condition:

> Work on `<slug>` until you need runtime traces that only I can run. End with a
> trace plan I can execute. Commit each pass and record friction in
> `PROCESS_FRICTION.md`; otherwise don't stop for feedback.

Adding process detail to a prompt is usually the wrong fix. The prompt that
produced the motivating history already constrained process heavily — *follow
the process meticulously, no cutting corners* — and process compliance was
never what failed.

This is a trade, not a free move: the prompt shrank but the playbook bundle
loaded on every pass grew, and the route budgets rose 9–13% across this branch.
Moving a rule into the process makes it apply unconditionally, at the cost of
context on every pass that reads it.

## 3. Calibration

**What a corpus backtest can and cannot establish.** The corpus is not a
controlled experiment: the process, playbooks and gates have evolved
continuously, and most projects were built under earlier versions of both.
Several artifacts these signals read — the semantic-claims ledger, the
data-format worklist — postdate the projects that lack them, and trace plans
were historically authored when a human asked rather than when the process
called for them.

So the backtest establishes exactly one thing: **the noise rate.** A detector
firing on half the corpus is too loud whatever the vintage of the work. It does
not establish that quiet projects were healthy, or that firing ones were not.
Only one project in the corpus was run start-to-finish under the current
playbooks, which makes it the sole clean observation and a sample of one.

A detector whose corpus fire rate is unknown cannot be trusted. One noisy
detector trains the operator to scroll past the region where every other signal
appears, making the channel worse than silence.

Every signal was backtested across all 21 projects. The first cut of
the deferral signal fired on **11 of 21 (52%)** — including mature,
fully-green projects. That is the failure mode this spec warns about, caught
before merge. Measuring the underlying distribution showed why:

| Project | Passes | Deferring | Rate | Notes file |
|---|---:|---:|---:|---|
| The motivating project | 89 | 41 | 46% | **no** |
| Project B | 222 | 81 | 36% | yes |
| Project C | 185 | 48 | 26% | yes |
| Project D | 336 | 82 | 24% | yes |
| Project E | 105 | 13 | 12% | yes |
| the remaining 16 | — | — | ≤7% | mostly no |

The projects that defer systematically **already keep working notes**. That is a
validation of the rule, not a violation of it: the signal should fire on high
deferral rate *with no durable home*, which is one project.

The first backtest was itself unsound. The crosswalk parser matched only the
canonical header, so thirteen projects — including several with fully mapped
crosswalks — read as empty tables. The signal could not fire on them and the
vocabulary check's healthy-family suppression was disabled, which is the
false-positive direction. "20 of 21 silent" therefore rested on eight readable
projects, not twenty-one.

With both header spellings accepted, eighteen crosswalks are readable and the
result is **19 of 21 silent, 2 firing**: the motivating project, and one other
at 19% mapped, which is a fair call rather than noise.

| Signal | Fire rate |
|---|---|
| `crosswalk_unmapped` | 2/21 (10%) |
| `deferrals_uncaptured` | 1/21 (5%) |
| `runtime_deferrals_unscheduled` | 1/21 (5%) |
| `semantic_claims_empty` | 0/21 — no project has finished naming with an empty ledger |
| `deferral_repeat` | 0/21 — no project has captured deferrals yet |

Re-run the backtest before changing the signal set.

## 4. Implementation

| Change | File |
|---|---|
| Identity pass shape | `agent_playbook/PASS_WORKFLOW.md#identity-pass` |
| Proof-debt contract, dismissal, deferral capture | `agent_playbook/PASS_WORKFLOW.md#proof-debt` |
| Detector docs and calibration rule | `agent_playbook/TOOLING.md#vocabulary-drift` |
| Ratio signals + acknowledgement ledger | `scripts/proof_debt.py` |
| Deferral capture at closeout | `scripts/deferral_capture.py` |
| Dominant-unmapped-phrase detector | `scripts/symbol_vocabulary_check.py` |
| Signals at the mandated chokepoint | `scripts/project_next_pass.sh` |
| `identity_pass` bucket and contradiction interception | `scripts/project_next_pass.sh` |
| Cache freshness across every brief input | `scripts/project_next_pass.sh` |
| Provenance coverage (`--coverage`) | `scripts/proof_debt.py` |
| Outcome standard | `AGENTS.md#mission` |
| Unattended-session rules | `agent_playbook/PASS_WORKFLOW.md#proof-debt` |
| Suggested kickoff prompt | `README.md` |
| Drift section in the dashboard | `scripts/project_maturity_summary.sh` |
| `rework_items` no longer auto-zeroed | `scripts/project_pass_closeout.sh` |
| Missing notes no longer reads as no debt | `scripts/working_notes_maturity_check.sh` |
| Opt-in flag (`PROOF_DEBT_REQUIRED`) | `scripts/project_common.sh`, `scripts/new_project.sh` |
| Both crosswalk header spellings accepted | `scripts/proof_debt.py`, `scripts/symbol_vocabulary_check.py` |
| Partial-match suppression on a mapped crosswalk | `scripts/symbol_vocabulary_check.py` |
| `rework_items` enforced on closed rows | `scripts/scorecard_lifecycle_check.py` |
| Ledger header, field-count and enum validation | `scripts/project_process_check.sh` |
| `REWORK_ITEMS` input and closed-row enforcement | `scripts/project_pass_closeout.sh`, `scripts/scorecard_lifecycle_check.py` |

Every check is advisory (exit 0). None of them can fail a build. The two
corrected gates change what is *reported*, not what is enforced.

The signals are also opt-in, following the mechanism the repository already
uses for nine other checks: they run only where `PROOF_DEBT_REQUIRED="1"` is set
in `project.conf`. New scaffolds opt in; existing projects stay silent until
chosen. This matters beyond caution — these signals read authored ledgers that
postdate most of the corpus, so firing them on work done under an earlier
process would report a debt the project never had the chance to incur.

Tests: 326 shell tests pass (35 new, each exercising both a firing and a silent
case), plus 1,206 JUnit tests. New detectors were mutation-tested — reverting
each script to its previous version makes exactly the corresponding tests fail.

## 5. What this does not fix

Stated plainly, because a spec that only lists its strengths is not reviewable.
These are known limitations, not oversights awaiting discovery — a reviewer's
time is better spent on what this list misses than on re-deriving it. The
sharpest of them, in the author's estimate, are the fitted-constant count and
the reliance on prose parsing.

- **It cannot make an identity pass succeed.** If the evidence channels do not
  exist in the ROM, the signal will fire forever and the honest response is an
  acknowledgement row.
- **It does not validate a claim's correctness.** `SEMANTIC_CLAIMS.md` going
  from 0 to 1 silences `semantic_claims_empty` regardless of whether the claim
  is any good. The signal measures whether evidence was *recorded*, never
  whether it is *right*.
- **It can be satisfied cheaply.** A crosswalk row mapped to a plausible-looking
  symbol clears `crosswalk_unmapped` without proving anything. These are
  tripwires against silent drift, not proofs of quality.
- **It adds two ledgers to maintain**, and ledgers rot. `deferrals.csv` in
  particular will accumulate closed rows unless pruned.
- **The `--dominant 100` threshold is corpus-calibrated, not principled.** Four
  projects report a family at or above it, and they are not simply the largest —
  one is among the smallest in the corpus with a thin crosswalk. A family whose
  words are wholly absent from the crosswalk is always reported; a partial match
  is suppressed once the project's own crosswalk is at least half mapped, on the
  reasoning that a project demonstrably naming what the reference material names
  is more likely to have found a real subsystem than invented private
  vocabulary. That suppression is a second corpus-fitted knob, not a principle.
- **Subject keys are untested against an operator who knows they are parsed.**
  The replay feeds real prose through a synthetic loop, so it establishes that
  the key works on notes written before capture existed. It cannot establish
  whether keys stay stable once an operator writes knowing the sentence will be
  split and keyed — the measure becoming a target. Only a real run with capture
  enabled tests that.
- **Subject keys are approximate.** `deferral_repeat` groups deferrals by
  distinctive nouns drawn from the operator's sentence. It will merge some
  distinct gaps and miss some genuine repeats; the alternative, keying on the
  pass focus, made the signal unable to fire at all.
- **Three crosswalk schemas remain unreadable.** Two header spellings are
  accepted; three projects use genuinely different column sets and report as
  unreadable rather than as zero.
- **Coverage measures recorded reasons, not good ones.** A ledger row saying
  "proven by callsites" counts identically to one that proves it.
- **Twelve constants are fitted, not derived.** The two named above are the
  ones most obviously arbitrary, but the full set is: deferral rate 15%, recent
  window 20 passes, 2 recent deferrals, 5 runtime gaps, crosswalk mapped 25%,
  unclosed ratio 50%, well-mapped suppression 50%, minimum symbols 40, dominant
  100, three strikes, minimum 8 passes, and zero unresolved labels for claims.
  Every one was chosen by looking at this corpus, which is not a controlled
  experiment. None is derived from a principle, and the corpus cannot validate
  them because most of it predates the artifacts they read.
- **Deferral capture can fall back on parsing English prose**, which nothing
  else in this toolchain does. `DEFERRALS` lets the operator state gaps
  directly and is the intended contract, but without it clause extraction runs
  regexes over a human sentence and reduces it to nouns, and three strikes
  rests on that reduction being stable. It remains the least verifiable path,
  and an unattended run that never sets `DEFERRALS` takes it every time.
- **Default-off means the branch may be inert.** Every check exits 0 and runs
  only under `PROOF_DEBT_REQUIRED=1`, which no project currently sets. Nothing
  here changes any outcome until someone opts a project in and then acts on
  what they read. That posture is deliberate — a new check firing on twenty-one
  projects at once is how a channel gets ignored — but safety and efficacy are
  trading directly against each other, and this sits at the safe end.
- **`deferrals.csv` is a materialised view with no reconciliation.** Its rows
  are derived from scorecard notes. Editing a note after closeout leaves the
  ledger silently divergent, and because the dedup key is `(pass_id, subject)`,
  re-running after a rewording adds a row rather than correcting one. Nothing
  detects the drift.
- **The identity pass has never been run.** The recommender can now rank it as
  an `identity_pass` bucket, so it is reachable by an operator who reads only
  the generated brief — but It is the change the previous
  review called highest-value, and it is entirely prose. Its two-channel
  evidence standard has not been exercised against a real ROM, so the claim
  that identity work is reachable this way is argued, not demonstrated.
- **`rework_items` enforcement rides a different flag.** It is gated on
  `SCORECARD_LIFECYCLE_REQUIRED`, not on the proof-debt opt-in, so the next
  project to enable lifecycle checks inherits the stricter rule without opting
  into anything. Only one project sets that flag today and it passes.
- **Signal fatigue remains the standing risk.** Three signals on one project
  today is healthy. Thirty signals on every project would restore exactly the
  blindness this is meant to cure.

### 5.1 Before promoting any signal to a hard gate

No proof-debt signal may be promoted from advisory or recommender behaviour to a
hard gate until `PROOF_DEBT_REQUIRED=1` has been run through at least one real
opted-in project pass — including pass start, closeout, and review of the
resulting recommendations. Backtests and fixtures establish regressions and
noise bounds; they do not prove that a signal improves live pass work.

This is a condition on the whole mechanism, not on any one signal. It covers all
six proof-debt signals — `crosswalk_unmapped`, `semantic_claims_empty`,
`deferrals_uncaptured`, `deferrals_unclosed`, `deferral_repeat`,
`runtime_deferrals_unscheduled` — and equally the surrounding behaviour that
reads them: vocabulary-family drift in `scripts/symbol_vocabulary_check.py`, the
identity interception in `apply_identity_interception`, and the `rework_items`
enforcement in `scripts/scorecard_lifecycle_check.py`. Advisory opt-in operation
is not covered by this condition and needs no such proof; the condition binds
only the step that makes something able to fail a build.

The distinction matters because the two kinds of evidence answer different
questions. A backtest over this corpus can show a signal does not fire wildly on
projects it was not designed against — a noise bound. It cannot show that an
operator who reads the signal does better work than one who does not, because
nobody in that corpus ever read it. Only a live pass produces that evidence.

Beyond the general condition, individual signals may need more.
`deferrals_unclosed` is the nearest candidate and is not ready. Capture writes
`revisit_condition` empty by construction, so the unclosed ratio starts at 100%
and the signal fires on the very first captured pass. As an advisory that is the
intended nag; as a hard gate it would block closeout the moment a project adopts
capture, and the ratio threshold gives no protection because the denominator is
one or two rows.

Promotion therefore needs a minimum ledger size or a grace window on top of the
general condition above. The honest sequence is to run a project with capture
enabled for a dozen passes, read the steady-state unclosed ratio, and set the
floor from that rather than from a guess.

## 6. Review questions

1. Is the causal analysis right — is corridor-local evidence genuinely unable to
   support identity naming, or was this an execution failure that better
   adherence to the existing rules would have prevented?
2. Would these signals, firing from pass ~8 onward, have changed the outcome
   over the 89 passes already committed? If not, what would have?
3. Is deferral capture at closeout the right forcing function, or does writing
   to a ledger from `NOTES` prose overreach?
4. Are the thresholds defensible, or is `deferrals_uncaptured` at 15% tuned to
   a single project? More broadly — see the knob inventory in §5 — is twelve
   fitted constants too many to call this calibrated rather than fitted?
5. Is the acknowledgement ledger a genuine escape hatch, or a mechanism for
   dismissing signals without engaging with them?
6. Is the runtime/static split drawn in the right place? Specifically: were
   the 14 runtime-classified deferrals genuinely runtime-gated under the
   definition, or is identity work being filed as dynamic because the
   cross-corridor static path is harder?
7. Is provenance coverage the right yardstick for "the assembly is justified",
   and should it become a maturity gate with a floor?
8. Should any of these be promoted from advisory to a hard maturity gate, and if
   so, which — and what breaks in the existing corpus when they are?
