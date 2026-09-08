# Invocation-local analysis bundle

Version 1, profile `ci-data-v1`. This is shared production of assembled facts,
not cached gate verdicts, a persistent cache, or an instruction-consumer migration.

## Lifecycle

`project_ci.sh` owns a fresh temporary directory and removes it on exit. Before
verification it fingerprints configuration and the selected reference, warning,
KPI, and extent-policy inputs. A configuration change while loading is refused.
The primary `verify.sh` assembly emits binary, owner/data xref v2, listing v1,
index patterns, data consumers, and xasm dependency manifest v1. The wrapper
continues to check warnings and reference parity on that assembly, in the same
order. A parity mismatch retains the extra source-mapped compare invocation.

The producer driver observes the actual process exit. It accepts no pre-existing
manifest, validates the consumed-input manifest, checks required output shapes,
hashes the exact validated output bytes, and atomically publishes `bundle.json`
only after successful production. The descriptor certifies production, not that
verification, process, maturity, or documentation policy passed.

`NESREV_ANALYSIS_BUNDLE` supplies that descriptor to the existing embedded-pointer
audit and extent checker. Each validates dependencies and artifact hashes before
use and again after collection, before reporting success. Extent assertions must
be among the bound policies. Project wrappers also check source/project/config
and effective address-domain identity when loading configuration; CI validates
again after its last phase. Invalid supplied input refuses with no reassembly or
pass-prep fallback. Even an explicitly supplied empty path is an error.

With no supplied bundle, the existing standalone checks generate their required
fresh facts once. Standalone project wrappers retain their existing production
flow; the one-assembly budget applies to normal complete `project-ci`. CI refuses
caller-supplied bundles because CI always requires fresh production.

## Descriptor and validation

The descriptor contains:

- `schema: nesrev-analysis`, `version: 1`, `complete: true`;
- `context`: profile, project slug, absolute root/config lookup paths, original
  source argument, effective ROM range and compare CPU base, policy fingerprints;
- `argv`: exact expected producer command, including all output selections;
- `dependencies`: path, size, and SHA-256 of the producer manifest;
- `outputs`: exactly `binary`, `xref`, `listing`, `index_patterns`, and
  `data_consumers`, each with absolute path, size, and SHA-256;
- `reader`: path, size, and SHA-256 of the bundle implementation.

Missing optional policies have an explicit negative fingerprint. All other
fingerprints require regular files and content hashes; size/timestamp alone is
never evidence of freshness. JSON duplicate keys are refused. Negative lookup
probes retain xasm's absolute lookup paths, including symlink/`..` semantics.
The selected xasm executable must match the manifest producer digest. Original
arguments, cwd, source membership, supported schema versions, required output
set, and profile options are checked, not inferred from file existence.

Listing and xref carry explicit producer schema versions. The two analysis
arrays are unversioned upstream; this profile requires their current field/type
contract and binds the actual producer digest. No source parser reconstructs
dependencies or assembler facts. At production, required shapes are checked on
the same bytes whose hashes are stored; reuse checks every output hash and
decodes only the requested consumer artifacts. Existing xref leaves continue
their own xref validation. Instruction records are deliberately absent from this
profile so legacy consumers do not decode unused expression trees. Adding an
instruction profile and migrating branch literals is the next separate unit.

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
