# Intake measurements and historical baselines

`make project-intake PROJECT=<slug>` checks scorecard compatibility before
assembly, warning seeding or onboarding promotion. It never refreshes a
historical pass row from current source counts.

| Existing scorecard | Intake behavior |
|---|---|
| Fresh scaffold: pending marker and sole empty pass-zero row | Capture pass zero once, only after successful intake gates; remove the marker |
| Existing pass-zero row without pending marker | Preserve every historical byte, including unknown/blank measurements |
| Legacy scorecard beginning at pass one or later | Refuse early until explicit migration records the missing baseline |
| Duplicate/out-of-order IDs, malformed table, or pending marker over populated history | Refuse; correct the structure or remove an inappropriate marker without changing historical evidence |

Scaffolding supplies `<!-- nesrev:intake-baseline pending -->`. Do not add it
to an old scorecard to reinterpret current measurements as original history.
Older unmarked empty baselines are historical unknowns, not fresh capture
permission. Preserve their missing evidence; normal lifecycle gates still
decide whether their outcome cells are acceptable.

## Explicit legacy migration

For a scorecard without pass zero:

```sh
make project-intake-migrate PROJECT=<slug>
```

This writes `inventory/intake_history.json`, recording the original scorecard
hash and the disposition “not recorded; not reconstructed.” It does not create
a pass-zero row, change measurements, run assembly or claim successful intake.
Commit/review the receipt with the local project. Repeating migration is a
no-op; invalid existing receipts are refused, not silently repaired. The stored
hash identifies the migration input, not a prohibition on later pass rows.
Existing `retro-0` retrospective measurements and repeated identical table
headers are preserved; a retrospective row is not an original pass-zero record.

Then run normal intake. Successful verify (explicitly intake-relaxed), process
and docs checks permit publication of `inventory/intake_snapshot.json`. This
small current-state artifact contains source/reference hashes, current supported
metrics and actual successful wrapper modes/statuses. It is refreshable and
should be tracked with the project; it is neither a historical baseline nor
evidence that strict maturity CI passes. Identical inputs/results produce an
identical snapshot; no wall-clock timestamp causes churn.

## Write boundaries

The internal publisher is called only after all canonical intake gates succeed.
It rechecks the preflight scorecard hash before publishing, stages atomic file
replacements, and restores the previous snapshot (or absence) if fresh baseline
publication fails. Failed gates leave the previous snapshot/history intact;
existing onboarding/KPI rollback still applies. Earlier inventory generation
and deliberately seeded warning candidates keep their existing retry behavior.

Direct `project_scorecard_sync.sh` requests for pass zero, including an inferred
latest pass zero or dry-run, are refused. Active semantic-pass sync continues
to update its measured columns without inferring gate outcomes. Historical
corrections require their own evidence-backed edit/review; never use current
intake counts to fill an unknown original measurement.
