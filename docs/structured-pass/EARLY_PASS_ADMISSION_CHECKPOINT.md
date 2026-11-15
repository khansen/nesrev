# Early-pass admission: checkpoint 1

15 November 2026. **Go for scoping implementation; implementation is not yet
authorized.** On three retained early-stage snapshots, the existing naming-only
exception was sufficient: all four gate families and the two final preparation
checks passed without repairing any input. This establishes a smaller admission
scope than a new early-stage verification policy. It does not admit a service
session or prove a fresh-game pass end to end.

## Measurement

The owner authorized at most two active hours, offline, under the
[checkpoint proposal](EARLY_PASS_ADMISSION.md#checkpoint-1-measure-before-estimating).
The private manifest was sealed before gate execution:
`bdd80e259ec2567fb2010cc1efc43342481a132518012554ad7e8b57d7c07a96`.
The pinned tooling was master `e0ad82396`; the retained native producer's
SHA-256 was `85e6bc5784132c4483b0a197c30ec3876edf6a1d6fd325558bf23db7dadb105b`.

S1 is the intake/recovery baseline. S2 is the exact snapshot used in the earlier
refused preparation and unit-level heavy-search measurements. S3 is a later
early-semantic state. Their source hashes are distinct; rebased copies did not
increase the sample. They belong to one supported game, not three games.

Each disposable repository combined current tooling with the snapshot's project
tree, including shared project artifacts. Supplied reference files and the
existing text extract were copied and hash-checked. The manifest records original
commits, composite diagnostic commits, file hashes, tool pins and the fixed
selection. These are current-tooling measurements on historical inputs, not
historical replay. Identities, paths and raw logs remain private.

The driver reused preparation's schema checks and next-pass/pass-start setup,
then ran the four gate targets independently and sequentially. Only relaxed
verification received `ALLOW_UNRESOLVED_LXXXX=1`; the other commands used the
unchanged service-configured environment. It also checked preparation's
generated-only change rule and ran native certification. No production service
or gate code changed, and no client or provider was invoked.

## Results

| Check | S1 | S2 | S3 |
| --- | --- | --- | --- |
| Distinct unresolved names, before and after | 1,347 | 1,301 | 1,258 |
| Matching source lines, before and after | 3,686 | 3,534 | 3,431 |
| Preparation schemas | Pass | Pass | Pass |
| Next-pass and pass-start setup | Pass | Pass | Pass |
| Inventory | Pass | Pass | Pass |
| Strict verification | Naming refusal | Naming refusal | Naming refusal |
| Naming-only relaxed verification | Pass | Pass | Pass |
| Process checks | Pass | Pass | Pass |
| Documentation checks | Pass | Pass | Pass |
| Generated-only change check | Pass; no tracked changes | Pass; no tracked changes | Pass; no tracked changes |
| Native source certification | Pass | Pass | Pass |

For each strict run, `make` returned 2. A separately recorded direct invocation
of the unchanged verifier returned 3. The strict logs establish unchanged
warning baselines and ROM parity before the naming refusal; the passing relaxed
runs establish that verification's later checks also passed. Mode selection
must not infer a naming failure from `make`'s general failure code.

All three certifications established exact source round-trip and reference PRG
parity. Every original project file was byte-identical after measurement, as
were supplied inputs and tooling. The main checkout, saved review/permission
state and stashes were unchanged.

No additional failure appeared in any cause category: early-stage properties,
tooling/artifact drift, environment/pins, or unresolved cause. There is therefore
no extra gate-repair scope to estimate from this sample.

The measurement executed 27 subprocess commands, plus the in-process schema and
change checks, in 63.58 seconds. The shared heavy-run receipt finished normally
with exit 0 and no surviving command group. Setup, analysis and reporting are
charged separately in the private effort record; this duration is not the
whole checkpoint's effort or a prediction of implementation cost.

## Limits and retained non-results

- The strict runs stopped at naming. Their later checks were not run; the
  separate relaxed runs supply that evidence.
- Existing conditional skips remain skips: S1 has no pass-1 analogue decision
  yet, and all three snapshots have no canonical packet-stream annotations for
  that process scan. Existing advisories were retained, not repaired or promoted
  to passing evidence. A gate with no applicable assertion rows is not a test
  of its rejection behavior.
- No service profile/session was created. Candidate mutations, review/closeout,
  application, resume integrity and refusal controls remain implementation
  acceptance work. This checkpoint checked preparation prerequisites, not the
  full workflow.
- The four heavy queries were not rerun through a service. Their existing
  unit-level overflow measurements remain unchanged and uncredited as service
  evidence. Admission acceptance must re-measure them without changing queries
  or the eight-request limit.
- Three snapshots of one game cannot prove universal admission readiness or
  future gate compatibility. No mutation controls were run at this checkpoint;
  the proposed implementation must demonstrate refusal of real defects.

## Decision

Proceed to the bounded [implementation proposal](EARLY_PASS_ADMISSION.md#post-checkpoint-implementation-proposal).
The work is to bind the existing naming-only mode to the immutable pass starting
source, propagate it through existing service checks and receipts, and keep
strict completion intact. Search redesign, intake automation, runtime work and
launcher integration remain separate. A fresh-game pass is still the eventual
process test; completing this admission slice alone will not supply that path.

The private packet retains authorization, the sealed manifest, the driver,
per-snapshot input hashes, all 27 command logs and results, certificates,
conditional-skip records, protected-state comparisons and the heavy-run receipt.
