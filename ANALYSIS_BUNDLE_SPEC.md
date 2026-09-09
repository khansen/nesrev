# Invocation-local analysis bundle

Version 1. This is invocation-local production of assembled facts, not cached
gate verdicts or a persistent cache. Branch-literal consumers use the separate
instruction stream; their policy is specified in [BRANCH_LITERAL_POLICY.md](BRANCH_LITERAL_POLICY.md).
The [raw-address KPI](RAW_ADDRESS_KPI_POLICY.md) uses the same validated stream.

## Fixed profiles

Every profile has a closed output set and exact producer argument contract.
Unknown profiles and missing required artifacts refuse; accepting a richer
profile does not weaken a consumer's context or policy binding.

| Profile | Outputs | Owner / warning policy |
|---|---|---|
| `ci-data-v1` | binary, owner/data xref, listing, index patterns, data consumers | Retained data-only interface; unused equates are errors |
| `ci-instructions-v1` | data-only set plus instructions | CI, verification, intake, closeout; unused equates are errors |
| `inventory-instructions-v1` | binary, owner/data xref, instructions | Standalone inventory; ordinary warnings |
| `maturity-instructions-v1` | data-only set plus instructions | Standalone maturity; ordinary warnings |
| `instructions-v1` | binary, instructions | Source-only CLI and pending intake calibration; ordinary warnings |
| `pass-prep-instructions-v1` | CI instruction set plus all-symbol summary and data coverage | Pass preparation; ordinary warnings |

All profiles request the dependency manifest. Instructions are always separate
from legacy xref, so data readers do not decode unused expression trees.
Source-only context explicitly has no project/config/address-domain identity;
it cannot stand in for project verification. A branch leaf accepts any of the
instruction-bearing profiles, but never the old data-only profile.

## Lifecycle

`project_ci.sh` owns a fresh temporary directory and removes it on exit. Before
verification it fingerprints configuration and the selected reference, warning,
KPI, and extent-policy inputs. A configuration change while loading is refused.
The primary `verify.sh` assembly emits the CI instruction profile. The wrapper
continues to check warnings and reference parity on that assembly, in the same
order. A parity mismatch retains the extra source-mapped compare invocation.

The producer driver observes the actual process exit. It accepts no pre-existing
manifest, validates the consumed-input manifest, checks required output shapes,
hashes the exact validated output bytes, and atomically publishes `bundle.json`
only after successful production. The descriptor certifies production, not that
verification, process, maturity, or documentation policy passed.

`NESREV_ANALYSIS_BUNDLE` supplies that descriptor to the embedded-pointer audit,
extent checker, and branch-literal and raw-address leaves. Each validates dependencies and artifact hashes before
use and again after collection, before reporting success. Extent assertions must
be among the bound policies. Project wrappers also check source/project/config
and effective address-domain identity when loading configuration; CI validates
again after its last phase. Invalid supplied input refuses with no reassembly or
pass-prep fallback. Even an explicitly supplied empty path is an error.

With no supplied bundle, standalone checks generate their required fresh facts
once. Standalone verification owns a fresh CI instruction bundle; inventory
refresh owns its smaller profile and supplies both KPI and CSV consumers.
Standalone maturity supplies all its assembled-fact consumers from one ordinary-
warning production; the advisory summary shares an inventory-profile production
between branch and raw metrics. Neither accepts a bare xref as instruction evidence.
Supplied xref alone cannot establish instruction freshness and is refused by
inventory refresh. CI, intake and prep refuse supplied analysis inputs.
Verification permits a parent-owned, prepared build directory, but requires
the strict CI instruction profile before production. Intake and closeout keep
that directory alive for subsequent checks. Live xref consumers use the
descriptor's canonical path; legacy cache copies are presentation artifacts,
never certificates or path-binding substitutes.

Pending intake calibration owns a source-only bundle, binds the original KPI
file, and revalidates immediately before atomically publishing measured limits.
Only then is the final-policy verification bundle prepared. Intake copies its
listing instead of assembling a separate listing. Warning seeding remains
separate. A later intake failure retains the existing KPI/ONBOARDING rollback.

Pass prep produces facts without comparison: xasm publishes no dependency
manifest on comparison exit 5. A validated byte-prefix comparison preserves
compare-v1 semantics (the smaller length, including zero; not full-length binary
identity). Only a mismatch requests xasm's source-mapped diagnostic, whose exit
must be 5. Diagnostic and filtered-summary assemblies use scratch binaries,
not bound output paths. Facts are revalidated after those runs and before
baseline publication. Extraction failure remains failed parity while fresh
facts can still feed planning. Normal prep uses two assemblies, mismatch prep
three; neither successful production nor a cache copy certifies green parity.

## Descriptor and validation

The descriptor contains:

- `schema: nesrev-analysis`, `version: 1`, `complete: true`;
- `context`: profile, project slug, absolute root/config lookup paths, original
  source argument, effective ROM range and compare CPU base, policy fingerprints;
- `argv`: exact expected producer command, including all output selections;
- `dependencies`: path, size, and SHA-256 of the producer manifest;
- `outputs`: exactly the selected profile's output set, each with absolute
  path, size, and SHA-256;
- `reader`: path, size, and SHA-256 of the bundle implementation;
- `instruction_reader`: the instruction-schema implementation fingerprint,
  required for instruction-bearing profiles.

Missing optional policies have an explicit negative fingerprint. All other
fingerprints require regular files and content hashes; size/timestamp alone is
never evidence of freshness. JSON duplicate keys are refused. Negative lookup
probes retain xasm's absolute lookup paths, including symlink/`..` semantics.
The selected xasm executable must match the manifest producer digest. Original
arguments, cwd, source membership, supported schema versions, required output
set, and profile options are checked, not inferred from file existence.

Listing, xref and instructions carry explicit producer schema versions. The
other analyses are unversioned upstream; profiles require their current field/type
contract and binds the actual producer digest. No source parser reconstructs
dependencies or assembler facts. At production, required shapes are checked on
the same bytes whose hashes are stored; reuse checks every output hash and
decodes only the requested consumer artifacts. Existing xref leaves continue
their own xref validation. Instruction leaves validate the whole record stream,
including nonmatching instructions, source-span membership in consumed source
inputs, and emitted bytes against the bound binary. No display text is parsed
to recover a tree or an instruction.

This is an accidental-staleness/consistency contract, not authentication of
hostile descriptors or a filesystem transaction. As with xasm's manifest, a
transient edit restored before validation and changes after the final check are
outside its guarantees. Consumed assembly inputs are xasm snapshots; remaining
text/ledger consumers read live files and must not be certified after a detected
change. No result or policy verdict is reused.

## Verification requirements

Test successful production plus independent refusal of same-size/time-preserved
source, include, binary, configuration, policy, and producer edits; deletion,
new lookup candidates, incompatible schemas/options/project, missing/truncated
artifacts, partial/failed production, and changes during reuse. Include positive
standalone equivalence and assembly-count fixtures, ordinary warnings/parity,
and the compare failure path. Timing evidence belongs in the performance plan
and its private corpus companion, not in test wall-clock thresholds.
