# Multi-session implementation checkpoint

The [narrow first build](MULTI_SESSION_SCOPE.md#authorized-first-build) is
stopped at its editor-capacity decision. The three investigation partitions
pass their initial component prices. The editing envelope does not: it leaves
17,467 tokens against the required 25,840-token margin, a shortfall of 8,373.
The 48K lifecycle reserve, measured rates and observed overhead are unchanged.

This is a checkpoint for review, not offline acceptance or a launch packet.
No native client invocation or provider call was used. The existing whole-pass
launch gate remains in place; no multi-session route has been exposed.

## Measured plan

The assembler-derived inventory is divided into source roots, helpers and
analogues, plus two whole-byte RAM ranges and their access-owner contexts.
The union retains every source unit and every fact/address membership. Shared
facts keep one identity derived from the full parent set, including certainty
and membership. Native declaration dependencies are retained explicitly.

| Entry | Estimated tokens | Remaining context | Required margin | Initial price |
| --- | ---: | ---: | ---: | --- |
| Source, helpers, analogues and declarations | 184,183 | 74,217 | 25,840 | Pass |
| Lower RAM range and its access owners | 229,161 | 29,239 | 25,840 | Pass |
| Upper RAM range and its access owners | 203,261 | 55,139 | 25,840 | Pass |
| Editing envelope | 240,933 | 17,467 | 25,840 | Refuse |

Each price retains the previous complete startup bundle, charged at 80,909
tokens, and includes the 48K reserve, observed unscripted overhead and a maximum
next response. Phase-specific startup selection has not been implemented or
credited. Repeated startup alone costs 323,636 estimated tokens across these
four contexts. These are component prices using native service views and the
real bridge encoder, not a rehearsal of a completed multi-session launcher.

The conservative editing envelope contains 274 native records: the complete
local roots, vector and helper bodies, every direct, exact-base or pointer-byte
access site for the inventoried RAM, and their referenced declarations. It
covers 170 access sites and 140 core records, with overlap. It does not assert
that all of those sites deserve semantic edits. Actual proposals will depend
on investigation; no smaller justified edit set has been established.

The editor re-reads the roots, vector, helpers and both analogue routines and
receives full records for that envelope. The price also reserves 64 KiB of
aggregate handoff wire data, 8 KiB for the transition index/receipt and 8 KiB
for phase-contract growth. These are proposed upper bounds to enforce at
consumer assembly, not measurements of a model-authored handoff. Final wire
cap enforcement and input pagination are still pending.

The first projection used 127 individual navigation calls for the edit records:
292,072 bytes, and an overall estimate of 315,592 tokens. That failed projection
is retained. The checkpoint prototype resolves the same selected citations
into seven pages using the existing lossless record codec. All 274 decoded
records, including every preimage, compare equal. They cost 120,269 bytes.
This reduces repeated envelopes without dropping edit facts, but does not make
the current editor plan fit. Required evidence and reservations total 284,658
bytes against its 264,604-byte allowance.

## Implemented components

`investigation.py` provides a frozen catalog, whole-set partition validation,
typed claims and citations, service-derived partial/complete coverage, bounded
handoff projections, full-record pages and consumer rechecks. The complete
coverage witness stays server-side under a hash; the delivered projection
contains claims, citations, locators, counts and that hash. It does not require
the editor to read thousands of receipt identifiers as conversational evidence.

The Codex adapter exposes an audit projection containing only actual tool
outputs after the last compaction. Both observed compaction shapes are checked
by the existing parser. Replacement history cannot restore delivery coverage.
The handoff validator refuses absence claims or completion based on invalidated
reads. A new read and checkpoint can restore coverage; a later compaction still
invalidates an earlier checkpoint at consumer admission. Ordinary subsequent
calls do not invalidate it.

These are tested components. Dispatch, phase capabilities, service receipt
collection and reconciliation with native call IDs, immutable checkpoint
publication, fixed input delivery, shared budgets and the launcher transition
route remain unimplemented. Input-derived citations, parent links and conflict
handling also remain to be wired into the final envelope. No declaration or
client pin has been changed or captured for these new operations.

## Configuration and storage seams

The existing Codex adapter already separates immutable CLI configuration from
its `CODEX_HOME`, and starts a fresh thread when `exec` has no `resume` argument.
It currently hard-codes a home per profile in preparation, verification, hooks,
login and audit paths. The proposed seam is one explicitly pinned home shared
by immutable session profiles, with separate state files whose initial thread
ID is null. Login credentials would remain in that one home. This is code
tracing only; native proof and implementation were deferred at the capacity
stop, so fresh-context feasibility is not claimed as accepted.

The existing retention store publishes content-addressed blobs with `fsync`
and atomic replacement. The editor transaction lock and atomic state writer
can publish a pointer only after a checked blob exists. A failed pointer write
would leave an unreferenced blob rather than a completed checkpoint. No new
transaction framework is needed in this proposed path; interruption controls
remain pending with its integration.

## Review boundary

The final component checks pass all eight new tests. Four deliberate faults
are caught: retaining native deliveries through compaction, trusting receipts
that are absent from the current context, allowing an omitted RAM-byte set,
and removing edit preimages. The full structured suite on macOS arm64 passes
452 tests with one existing opt-in skip. Repository documentation and hygiene
checks are run separately. CI and the broader `make test` suite have not been
run for this checkpoint.

Review the editing envelope, handoff caps and remaining startup obligations
before choosing the next scope. The current measured plan does not justify
continuing toward a live grant. Splitting editing across fresh contexts would
require the deferred generation-renewal and editing-continuation work, so it
needs an explicit scope decision. No limits or reserves were reduced to avoid
that decision.
