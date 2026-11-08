# Step 2A source operations

Status: Step 2A is merged and available through the opt-in structured services.
The scope and frozen limits are in [STEP_2_COVERAGE.md](STEP_2_COVERAGE.md).
This contract grants no inference, project migration or rollout authorization.

## Authority and identity

All operations use the existing generation → preview → confirm → validate →
publish lifecycle. Requests contain producer-derived record IDs and SHA-256
preimages. The service serializes typed requests; XORcyst parses, resolves,
evaluates and certifies the result. There is no client source-file writer,
assembler parser, expression evaluator, command selector or executable upload.

New sessions publish the `source-v2` review profile. Its capture includes
`ownership.json`, and source-changing candidates include `source-edit-map.json`
(`source-edit-map-v1`). The map records operation indices, before/after IDs,
tombstones and operand provenance. Capture hashes bind both files. A retained
window requires one unchanged ownership registry. Older review profiles do not
accept these new operation kinds. Existing stores and their reader identities
are not rewritten.

Each operator profile may explicitly register `authored_paths`, relative to its
project, in addition to the named canonical documents. Registration admits only
document paths; it cannot override source, inventory, policy, review, reference,
configuration or wrapper ownership. An unregistered `.md`, `.csv`, `.txt` or
`.json` path is forbidden. Registration is outside the bridge. Existing files,
suffixes and case variants do not grant permission. Root/shared documents and
the remaining policy writers belong to Step 2B.

## Typed source requests

Every operation has `kind` and a nonblank `reason`. Unknown fields refuse.
Preimages cover the selected producer span, not a caller-selected byte range.

| Kind | Additional fields | Contract |
| --- | --- | --- |
| `declare` | `anchor_id`, `preimage`, `declaration_kind`, `name`; `expression` for an EQU | Insert an EQU or global label before a complete statement and its leading full-line native comments, preserving the header's attachment. A preceding statement's inline comment stays with that statement. Declarations sharing an anchor are inserted together in request order. The declaration is addressable within the request as `new:<name>`. |
| `replace_expression` | `expression_id`, `preimage`, `expression` | Replace exactly one selected expression. Multiple occurrences require explicit selections. |
| `delete_declaration` | `declaration_id`, `preimage` | Remove a selected EQU/global/local declaration only when the complete native reference inventory has no surviving use. Every current use must already be absent or explicitly replaced/deleted in the same candidate. This does not claim code is unreachable or authorize code deletion. |
| `localize` | `declaration_id`, `preimage`, `scope_id`, `new_name` | Convert a global label to `@@lowerCamelCase` in an explicit preceding global scope. Every intervening global must be localized into that same owner in this batch. Require local branch evidence; refuse uses outside the merged scope, EQU/data/JSR/JMP uses, gaps and local-name collisions. |
| `reflow_data` | `record_ids`, `preimages`, `groups`; optional `boundaries`, `formats`, `continuation_indent` | Regroup complete DB/DW/string operands in their exact original order. Each group lists operand expression IDs. A boundary is `{operand_id, name}` at a group's first operand, optionally with a `header` list of comment lines. `formats` maps selected literal operand IDs to `decimal`, `hex` or `binary`. Continuation indentation is at most 16 spaces/tabs; the default is empty. |
| `unit_replace` | `unit_id`, `preimage`, `text` | Replace or delete one native comment, whitespace or newline unit. Code tokens are forbidden. Certification and identity checks reject changes that consume statements. |
| `comment_insert` | `anchor_id`, `preimage`, `text`; optional `position` | Insert a single comment at a statement's `header` (default) or unused `inline` tail. Never hide a following statement or existing comment. |

Typed expressions are `{integer: N}`, `{declaration_id: ID}` or
`{operator: OP, operands: [...]}`. The serializer supports unary `- ~ < >`
and binary `+ - * / % << >> & | ^`; the producer decides validity and value.
An integer may also specify `format: decimal|hex|binary`; hex and binary require
a nonnegative value and use the minimum digits. The default is decimal.
Integers are signed 32-bit, trees have fewer than 32 levels, and serialized
expressions are at most 4,096 bytes. New declaration handles are resolved against
the certified result. A same-valued declaration is never a binding substitute.

A batch admits at most 256 new source operations; the existing 64-rename limit
is unchanged. Reflow selects at most 128 statements, one element width and one
segment. It cannot split a string/word, cross a surviving label/ORG, discard an
unselected comment or reorder equal-valued operands. A retired interior label
and its comments may be removed explicitly in the same candidate before the
data records are joined; any surviving use or uncleared gap refuses. Boundary
labels are inserted during that reflow.
A boundary header admits at most 16 comment lines and 4,096 UTF-8 bytes, with
a blank line before an interior header. Newlines or code in a comment refuse.
Literal formatting accepts only nonnegative integer leaves that fit the native
element width. It preserves value and identity, never evaluates an expression
or discards a binding. Hex and binary formats pad to that width. Other operands
keep their original spelling. Other
comments/labels are edited separately and explicitly. Retired declaration names
have the same current-prose cleanup obligation as renamed or localized names;
deletion does not append a rename-ledger row.

Certification checks the intended bindings, unchanged bindings, statement and
declaration identities, instruction encodings, locations, segment origins and
copied operand emission ranges. Deletions remain visible as tombstones. The
existing rename and stale-prose guards still apply. All canonical gates and
reference PRG parity must pass before publication.

Localization requires matching rename-ledger rows in operation order. Their old
names come from the selected declarations, and their new names are the requested
locals. Every localized declaration and bound use appears in review. Current
source and document prose naming a localized global must be disposed in the same
candidate, as for an ordinary rename. New declarations still do not create
rename-ledger rows.

## Required artifact writers

`extent_rows` and `blob_rows` select fixed registered files. They take the whole
file `preimage`, a `reason`, and `changes`: `{key, preimage, row}`. The row
preimage is SHA-256 of sorted compact JSON; `null` means an absent row. A null
`row` deletes it. Keys are labels; rekeying requires explicit deletion and
creation. Unknown columns, duplicate keys, stale preimages and invalid schemas
refuse. The repository's blob-row validator remains authoritative, including
artifact links and disposition vocabulary. Citation checks use the candidate's
document set, including explicitly registered creations and deletions in the
same request. Extents are also checked against
certified data operands. Normal project gates retain their existing glob and
coverage checks.

An inserted row may also specify `before_key`, identifying an existing row that
must survive the candidate. Otherwise it is appended. This field cannot move an
existing row. Preview shows the anchor; review records include zero-based row
positions before and after the edit.

CSV edits preserve the original header, footer, row order and every untouched
row's bytes, including quoting and line endings. An unchanged request returns
the original file. Changed rows are serialized in place; new rows use their
explicit anchor or the end of the file.
Comments or blank lines between data rows and multiline CSV records refuse with
`ARTIFACT_LAYOUT_UNSUPPORTED`, because these row writers do not own that layout.

`warning_baseline` takes the file `preimage`, `reason` and the complete proposed
`entries`: `{declaration_id, rationale}`. This complete-set request admits at
most 4,096 entries and 256 KiB of compact UTF-8 JSON, including unchanged rows;
the other artifact writers retain their 256-change cap. Only the fresh assembler diagnostic
set may appear in the resulting baseline. The writer derives names, including
renames, from certified declarations. Resolved warnings must be removed in the
same candidate; nonexistent warnings and blank/generic rationales refuse.
Pure renames carry the declaration identity and exact prior rationale. A rename
that also shortens the native data extent is recorded as a rename and split,
with the split allocation's warning recorded separately. Leading and trailing
comments and blank lines are preserved byte for byte, as are unchanged row
spellings. For supported layouts, a no-op complete set keeps the entire original
file, regardless of request order. Comments or blank lines between rows refuse
in preview and validation with `WARNING_LAYOUT_UNSUPPORTED`; this writer cannot
rearrange sections. A nonempty header must end at a line boundary before rows
can be written. Changed requests must preserve the relative order of surviving
warning rows by declaration identity, including renames; otherwise validation
refuses with `WARNING_ORDER_CHANGED`. New rows may be placed anywhere among
those surviving rows. When a file has no rows, new rows inherit the header's
final line ending (LF for a new or empty file).
Rationale quality is still a reviewer judgment. The fresh
diagnostic hash, curation entries and identity transitions are retained. Unused
EQU errors cannot be turned into baseline warnings.

Preview and review page artifact changes, preserving old/new values and file
hashes. Warning review rows carry identity transitions so a rename is not shown
as an unrelated removal and addition. Q09 includes the admitted current artifact rows; rename-ledger
history and historical scorecard/review records retain their existing exclusions.
KPI changes, allowlist migration and runtime-question writers remain Step 2B.

Trusted refresh may update the existing raw-RAM queue's `active`, operand/owner/
read/write counts and top readers/writers. Each changed row appears in both
review sessions with its address, changed fields, old/new values and file hashes.
The address sequence and authored `status`, `proposed_symbol`, `notes` and
`last_pass_reviewed` must remain unchanged. A changed judgment refuses with
`RAW_RAM_JUDGMENT_CHANGED`; creating/deleting the file, adding/removing/reordering
addresses or changing its schema refuses with `RAW_RAM_REFRESH_UNSUPPORTED`.
There is no client operation for these generated fields. D3 judgment writes
remain disabled in Step 2A.

## Read views

The bridge's `evidence` operation takes `generation`, `view`, and optional
`offset`/`limit` (at most 40 records). All responses pass the existing 24 KiB
wire-size ceiling. It works in live and retained sessions, including admitted
`E-` generation IDs. Reads verify the generation's inputs before using caches.

| View | Selection | Evidence |
| --- | --- | --- |
| `ram` | `address` or declaration `record_id` | Direct/indexed/RMW/pointer-byte and unknown indirect cases. Indexed-indirect pointer-byte possibilities stay within zero page; unresolved indirect destinations remain separate. Alias evidence requires a native memory binding, not equal values. Indexed possibilities are not exact destinations. |
| `outgoing` | `record_id` | Native instruction effects and separately identified reference leaves, including through-EQU declarations. Segment and physical output position remain distinct from CPU address. |
| `expression` | `record_id` | Paged native expression nodes, operators, values, bindings and children. String payloads have length/hash and use the data decoder for bytes. |
| `data` | declaration or data-statement `record_id` | Operand identities, widths, output ranges, segment, byte counts and references. |
| `decode` | `record_id`, `decoder`, optional `byte_offset`/`byte_count` | Fixed `bytes` or `words_le` decoding, at most 4,096 input bytes in one segment. Width/alignment/bounds errors refuse. No inferred record format. |
| `scopes` | optional `record_id` | Native declarations, use counts and lexical owners. Missing is distinct from zero. Reachability and localization safety remain unknown. |
| `units` | none | Native comment/trivia IDs and byte preimages; long payloads explicitly flag truncation. |
| `artifact_rows` | `artifact`, optional `key` | Registered extent/blob/warning data, field paging, row and file preimages. |
| `policy` | none | Retained wrapper outcomes; availability is explicit. No automatic naming, prose-quality or maturity verdict. |
| `prior_reuse` | declaration `record_id` | Candidate names/values from separately identified operator-approved analogue models; coincidence is not semantic proof. |

Consecutive data labels with the same native segment and physical output offset
share one extent. A distinct label position, instruction, ORG or END still ends
that extent; equal CPU addresses in different banks do not join it.
An EQU is not a data declaration, even when it appears inside a data block.

An operator can supply up to two certified `analogue_models`. Their checked
bytes are retained losslessly compressed before admission and copied unchanged into subsequent
captures. `analogue_index` selects their native read views. Their IDs are
namespaced by model identity and cannot be used as current-project edit IDs.
The source is never exposed as a bulk read. The old query branches stay intact;
their source-excerpt interface is superseded by these structured views.

<a id="acceptance-still-required"></a>
## Remaining scope

The accepted Step 2A slice does not complete Step 2B, runtime confinement in
Step 2C, or the structured-default rollout. Full H4 replay, M8 publications 5
and 7, and the integrated eight-publication workload remain with the later
slices described in [STEP_2_COVERAGE.md](STEP_2_COVERAGE.md). Real-pass inference,
project migration and rollout still require their separate authorizations.
