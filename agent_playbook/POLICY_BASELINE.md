# Active Policy-Baseline Evidence

The policy-baseline check validates review accounting, not comment quality or
semantic correctness. It reads the latest scorecard audit marker, the active
CSV manifest, fresh procedure/global-code-label KPI detail sets, and the live
semantic-claims ledger. A matching total alone is not evidence of membership.

## Active manifest

The canonical wrapper explicitly supplies
`docs/reverse_engineering/inventory/policy_baseline.csv` beneath the project.
Direct checker calls may use `--manifest` to select an isolated test input;
otherwise the path is `inventory/policy_baseline.csv` beside the scorecard.
Never point it at a historical review snapshot.

CSV header, in this order:

```csv
symbol,inventory,disposition,localization,rationale
```

One row represents one distinct symbol in the union of the two live
undocumented detail sets. A header-only CSV represents an empty union; even
`0/0` requires that explicit evidence. Line numbers are not stored, so
unrelated source-line movement does not stale the manifest.

| Field | Contract |
|---|---|
| `symbol` | Exact global symbol from the live detail union; no duplicates or extra symbols |
| `inventory` | `callable`, `global`, or `callable+global`, matching membership in the two independent sets |
| `disposition` | `retained_headerless` for a completed review; `pending` for an undecided candidate |
| `localization` | `retain_global`, `deferred`, or `pending`; a reviewed row cannot leave this decision pending |
| `rationale` | Nonempty explanation of the header/localization decisions or the missing review evidence; for deferred localization, identify the remaining scope question or durable follow-up |

A retained-headerless disposition does not require adding a comment. Human
review still decides whether scope is safe, a header adds value, and the
rationale is supported. The checker validates the decision's representation
and current membership; it does not prove prose claims or localization safety.
Its candidate universe is exactly that of the existing KPI scanners, not a
new claim of complete 6502 control-flow analysis.

## Accounting and lifecycle

The scorecard marker retains the syntax at
[Policy Baseline Audit](PASS_WORKFLOW.md#policy-baseline-scorecard-artifact).
For example, a reviewed union with one callable and two global candidates:

```text
policy-baseline-audit: semantic_claims=reviewed; procedures=1/1; global_code_labels=2/2; retained_headerless=2; action=reviewed the active manifest.
```

`semantic_claims` accepts `created`, `reviewed`, or `advisory`. The first two
require a maturity-valid live ledger; `advisory` is not accepted at maturity.
For each inventory, its denominator is the live detail count and its reviewed
numerator is the number of manifest members marked `retained_headerless` in
that inventory. `retained_headerless` counts their distinct union, not the sum
of overlapping inventories. Pending rows count toward denominators only.

When a marker is present, missing or invalid active evidence fails even in
advisory mode. Without a marker, advisory mode reports `NOT CHECKED`; maturity
mode still requires a marker. Maturity additionally requires complete review
fractions and a maturity-valid semantic-claims ledger.

Keep this CSV current when candidates are renamed, documented, localized, or
newly exposed. Documented/localized/removed symbols leave the live candidate
set and therefore leave this active manifest; their former dispositions
belong in historical records. Record changed summary counts in a new scorecard
audit marker, not by rewriting an older pass row.

Migration is an explicit review step. Compare archived dispositions with fresh
membership and reconcile later source changes before creating the active CSV.
Do not infer a reviewed disposition from a nonempty rationale, a filename, or
a historical total. Preserve old review snapshots unchanged; the checker
neither scans them for current symbols nor accepts them instead of active
evidence. Do not activate the new requirement on a corpus until its migrations
are prepared and verified alongside the tooling.
