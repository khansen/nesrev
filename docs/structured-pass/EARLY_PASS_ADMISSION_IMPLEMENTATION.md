# Early-pass admission implementation and evidence

15 November 2026. Offline implementation of the owner-authorized
[admission scope](EARLY_PASS_ADMISSION.md), following the accepted
[three-snapshot measurement](EARLY_PASS_ADMISSION_CHECKPOINT.md).
The bound was eight active hours with a checkpoint by two hours. No provider
calls, live project passes or changes to the working project branch were made.

## Result and contract

An early semantic source can now complete structured preparation, candidate
validation, publication, review closeout and application to a disposable
checkout while its only verification exception is unresolved naming. This
removes the measured admission barrier. It does not deliver intake, runtime
integration or the launcher, or establish an unattended fresh-game workflow.

Preparation writes a versioned `current-project-profile-v2` containing the
starting commit, source identity, canonical lexical naming counts and eligibility.
The count uses the same patterns and pinned `rg` as the verifier; it counts
distinct names and matching source lines, not assembler-bound reference edges.
The mode is service-owned:

- A starting source with no generic names stays strict even if a candidate
  introduces one.
- An eligible early source must first fail the direct verifier with its own
  naming-refusal status, then pass the complete verifier with the naming-only
  exception. `make`'s generic failure status does not select the exception.
- The remaining gates receive their ordinary fixed environment. Neither
  `ALLOW_UNRESOLVED_LXXXX` nor `VERIFY_MODE` is inherited. Closeout's third
  argument is derived from the successful verification evidence.
- Resume and application validate the sealed policy against the immutable
  starting source. Missing or altered evidence refuses. Old profiles acquire
  no relaxed eligibility; retained sessions keep their existing pinned readers.
- Scorecards say `pass (LXXXX allowed)` when the exception was used. Gate
  evidence, review archives and application receipts preserve that distinction
  and the before/after counts. Removing the last generic name requires an
  actual successful strict run. Gold and maturity requirements are unchanged.

The existing verifier and closeout wrappers were not modified. Candidate
closeout runs the direct verifier before selecting the wrapper's strict or
relaxed argument; this adds verification work rather than replacing the wrapper.

## Offline acceptance

The real-code lifecycle uses the retained S2 snapshot from checkpoint 1, with
candidate tooling in an independent disposable repository and copied,
hash-checked inputs. The initial source and its 1,301 distinct generic names
are unchanged. This is current-tooling acceptance on retained data, not a
historical replay or game-quality approval. The review verdict exercises the
protocol without a model or an independent game reviewer.

| Check | Observed result |
| --- | --- |
| Full preparation | Inventory, verification, process and docs succeed; generated-only check and native certification succeed. Strict verifier exits 3; naming-only verifier exits 0. |
| Real candidate lifecycle | Scorecard-only diagnostic candidate validates, publishes, is read through review pages, closes and applies to a disposable `projects` branch. Application is idempotent. |
| Qualification | Policy view, wrapper receipt, archived review and application gates retain naming-only status and counts; no relaxed result is reported as strict-green. |
| ROM mismatch control | Direct verifier exits 2 before the naming check; no fallback is attempted. |
| Warning-baseline control | Direct verifier exits 5 before the naming check; no fallback is attempted. |
| Stale-comment control | Strict naming refusal followed by naming-only exit 69 at the comment audit. |
| Data-extent control | Strict naming refusal followed by naming-only exit 1 at the deliberately incorrect extent assertion. |
| Clean starting fixture gains a generic name | Candidate reaches verification and is refused with exit 3; both ambient relaxation variables confer no eligibility. |
| Last name removed in a fixture | A real strict verifier invocation succeeds before the closeout can report strict-green. |
| Policy and override controls | Changed/missing profile or state policy, changed starting source and caller-selected mode refuse. Each environment switch is tested separately and together. |

Fixture lifecycle tests simulate their ordinary quality-gate writers and use
the real pinned assembler. The four defect controls above instead run the real
project verifier on independent mutations of retained data. Those roles are
separate: simulated writers test orchestration, not the correctness of the
quality gates.

The first stale-comment control appended text after the source terminator and
failed syntax before the audit. It is retained and receives no audit credit.
The corrected control puts the same stale prose before the source and reaches
the intended audit. No gate, baseline or production input was repaired.

Three deliberate in-memory implementation faults were caught by assertions:
relaxing an initially clean source, replacing failed gate statuses with success,
and silently accepting extra environment switches. All failed by assertions,
with no setup errors. The mutations were never written into production files.

## Search practicality through admission

The four previously overflowing questions now run through the admitted service
on the same source. Predicates and native context requests are unchanged, and
complete match identities agree with the independent SQL/native-fact oracle.
Every response stays within 24 KiB.

| Retained question | Matches | Rows including context | Requests | Within eight? |
| --- | ---: | ---: | ---: | --- |
| R3-067: stack-pull neighbors | 58 | 339 | 14 | No |
| R3-067: stack-push neighbors | 37 | 220 | 9 | No |
| C4-049: non-immediate operand set | 241 | 241 | 11 | No |
| R4-079: immediate predicates | 523 | 523 | 20 | No |

The last question retains its disclosed global-proxy selection; the original
source-window question is not credited as verified. Native context is not
physical source-line context. These results replace the admission status of
the earlier unit-only measurement, not its honest limits. The eight-request
criterion stays fixed. Compact matches or grouped summaries require their own
scope; they are not included in this admission change.

## Validation, effort and limits

The early checkpoint was met in 17.4 minutes, before the two-hour limit:
retained-source preparation succeeded and the initially clean fixture refused
a newly introduced generic name. The implementation and local validation took about 40 minutes, conservatively
counting the entire working interval including local test waits and command
approvals; private timing records retain the exact interval. Independent review
and remote implementation CI are not included.

Final checks passed: 317 structured tests (one opt-in live-client check skipped),
692 shell cases and 1,206 Java tests. The strict playbook checker reported zero
warnings; repository hygiene and all 69 relative links passed. The final code
also repeated real-source preparation, lifecycle/application, all four gate
defects and the three deliberate faults. The working project checkout, its
preserved state, article changes and stashes match the initial snapshot.

The first synthetic rename test lacked its required ledger entry; it was fixed
to reach the naming check. The first full structured suite was blocked by the
execution sandbox's refusal of `/bin/ps`, which existing simulated-client
cleanup tests require. It passed when rerun with that access. Failed attempts
and their logs remain in the private packet; none is credited as green.

Private evidence retains the authorization, exact inputs and tooling hashes,
raw gate logs, preparation and application receipts, review pages, search pages
and oracle results, mutation results, protected-state comparison and effort.
The packet identifier is `early-pass-admission-implementation-20261115`.

Acceptance remains one game's retained early source, supported by the earlier
three-state measurement and synthetic clean-start controls. A new failure on
another game is a new finding, not authority to weaken admission. No live
client compatibility or owner-effort improvement is claimed. The next
integration choice remains governed by the minimum path to one useful
fresh-game pass, not by completing this validation game's remaining work.
