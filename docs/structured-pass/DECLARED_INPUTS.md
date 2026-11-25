# Declared evidence inputs

The operator declares the evidence for a corridor during preparation. Agents
can read the admitted items by ID; they cannot add inputs or choose host paths.
This implements the [slice-2 contract](INPUT_DELIVERY_CHECKPOINT.md). It does
not expand ordinary document ownership or authorize a client launch.

## Preparation and identity

The preparation selection may contain `declared_inputs` with exactly `path`
(an absolute path to the private selection JSON) and `sha256`. Its schema is
`declared-input-selection-v1`, with `items` and `analogues` arrays. Inputs are
validated before capture payloads or the profile are installed. The profile
pins the resulting catalog; the starting generation also includes that hash.

Nine guidance files come from the starting commit automatically: `AGENTS.md`
and the pass, assembly, quality, review-audit, tooling, documentation, recovery
and new-project playbooks. Each additional item has a unique `id`, a fixed
`kind` and `sha256`, plus the fields below.

| Kind | Operator fields and allowed origin |
| --- | --- |
| `reference_text` | `path`, `original_path`, `original_sha256`, `identity`. UTF-8 `.txt` under the current project's `tmp/`, derived from a supplied PDF under its `docs/game_reference/`. |
| `reference_image` | The same fields, with a PNG derivative and positive integer `identity.pdf_page`. Preserve printed-page and conversion identities in `identity`. |
| `comparison` | `path`: the committed architecture index or Markdown under a selected analogue's `docs/`, excluding review archives and inventories. |
| `intake_review` | `path`: the current project's committed pass-0 review archive. |
| `intake_receipt` | `data`: an operator-owned JSON object, including source, baseline and qualified gate evidence. |
| `reference_decision` | `data`: an operator-owned JSON object recording the supplied-reference decision. |

Inline JSON hashes use UTF-8 JSON with sorted keys, no indentation, default
ASCII escaping and separators `(',', ':')`. Text and image hashes cover exact
file bytes. Paths must be relative, canonical and free of symlink components;
tracked evidence must match the selected commit. Input IDs do not become paths
the agent may choose. IDs beginning with `guidance-` are reserved.

Each analogue entry supplies `source`, `sha256` and `model_sha256`, in the same
order as the existing `analogue_models` selection. Preparation compares the
native model's source bytes with the committed source and checks both hashes.
The existing producer identity and two-model limit still apply. Comparison
vocabulary is evidence requiring proof against the current game, not authority.
Selecting the analogues remains a manual operator step.

Limits are 32 text items, 256 KiB each and 2 MiB total; 16 PNGs, 16 MiB each
and 64 MiB total including retained original PDFs; and two analogue models.
Original PDFs are retained privately, not exposed by a new PDF read operation.
Both roles receive their complete declared extracts and page PNGs. Excesses
are refused rather than silently truncated. Missing conversion provenance must
remain explicitly unknown; a hash does not establish extraction quality.

## Read operations

Both corridor roles and restored review readers support:

- `inputs({generation, offset?, limit?})`: paged metadata for fixed input IDs.
  The default is 12 items and the maximum is 40.
- `input({generation, input_id, offset?, limit?})`: exact UTF-8 text, with
  offsets measured in Unicode characters. The default and maximum are both
  8,192 characters, matching the startup pages used by capacity admission.
  Follow `next_offset` until null. Empty input is an
  explicit complete result. The corridor implementer may fetch an image ID
  with only `generation` and `input_id`; the reply contains identity metadata
  and one MCP PNG image. Reviewers and retained readers return
  `INPUT_MEDIA_REQUIRED` for media IDs; Claude uses its admitted `Read` route.
- `guidance`: the existing named guidance reader, now including the first-pass
  playbook. Declared sessions use captured bytes, including after restoration;
  older profiles retain their commit-based behavior.
- `navigate`: the existing native record, symbol, use and comment views accept
  `analogue_index` 0 or 1. Responses identify the selected native model. No
  source-text or arbitrary-project reader is added.

The 24 KiB serialized MCP ceiling remains for text and image metadata. The
image reply alone has a 4 MiB + 24 KiB wire cap, with a 3 MiB PNG and dimensions
at most 2048 × 2048. Preparation renders bounded full-page derivatives before
sealing; the service never resizes. See the [image contract](FACTS_IMAGE_ROUTE_DESIGN.md).
Text pages reduce their character
count when encoding requires it. Other oversized pages are refused with the
existing reduce-limit response. No successful response silently loses content.
Invalid paging arguments return correctable `INVALID_PAGINATION` with the
field, integer type and accepted bounds. This includes offsets beyond the input;
exactly the end returns an empty complete page. Nulls and booleans are not integers.
The same diagnostics apply to the other offered paging operations, with their
own limits. An unknown input ID is correctable: `INPUT_UNKNOWN` points to the
IDs returned by `inputs`. Integrity and configuration failures such as
`INPUT_CHANGED`, `INPUTS_UNAVAILABLE` and `INPUT_SELECTION_INVALID` remain terminal. No recovery class
permits changing the selected evidence or replacing a client invocation.

Before preparing a live packet, run the argument regression matrix through the
real bridge for investigator, editor and reviewer. Every offered operation and
each required or optional argument is covered for wrong types, missing required
fields and unknown identifiers or enum values. Authored text and filters may
legitimately have no matches; optional fields may be omitted. Caller mistakes
must identify the field and its accepted values or delivered source, without
echoing submitted values. A caller-induced internal error fails the matrix.
Nested edit and checkpoint controls also verify that refusals cannot change a
candidate or stage coverage; investigation audit receipts still record refusals.

The terminal exceptions are access and integrity boundaries, not lookup misses.
A misspelled document in the current project's documentation namespace points
to the accepted paths in `operation-reference`, without reading the missed path.
Absolute paths, traversal, another project, source files, generated files and
reviewer-owned archives remain refused because they cross that route's scope or
ownership. Unknown review tickets are correctable; corruption of a stored
publication receipt stays terminal. Read-only investigation profiles still
reject mutation operations. Tests exercise these boundaries alongside corrected
requests, so argument recovery cannot silently widen access.

Investigation assignment, contract, transition and handoff text use the same
8,192-character default. The typed `investigation-edit-targets` input keeps its
40-record default. Image inputs still accept no paging arguments.

The service copies the catalog, originals and payloads into each candidate's
hashed capture. Publication retains them as blobs. Restored reads therefore
need neither the original operator folder nor the source PDF or model paths.
Input evidence remains read-only; canonical notes use the existing document
writer. Root README, root notes and friction records gain no access here.

## Role assembly and historical scope

One manifest builds both roles' input lists and page identities. The Claude
adapter requires `--task-file` for declared sessions; the Codex adapter uses its
explicit `--message-file`. The task states the current authorized corridor and
stop condition. Additional `--media` inputs are refused for declared sessions,
so they cannot bypass the manifest.

Both adapters pin the assembled manifest, copied PNGs and prompt. They label the
intake review, receipt and reference decision as historical. The prompt includes
an index and an explicit instruction that quoted historical run restrictions
do not govern the current task. The whole archive remains available on demand
for its verdict, findings and gate evidence; its prose is not injected into the
task prompt. Offline acceptance checks the assembled bytes and labels, not an
agent's statement that it received them.

Codex retains the sealed page assembly privately but gets an empty workspace,
fixed page IDs and the facts route. Its preparation admits at most eight bounded
pages; native image, shell and code-mode tools stay disabled. Claude keeps
hash-matched workspace files and native `Read`. Both prompts preserve the same
catalog and task identity. Codex's guidance limits successful image deliveries
to eight per conversation, including repeats across resume and compaction;
this is audited guidance, not a service quota. Fetch relevant pages on demand.
Live readability, provider request limits and the reviewer's hook-disabled test
remain launcher-admission checks; offline transport is not readability proof.
