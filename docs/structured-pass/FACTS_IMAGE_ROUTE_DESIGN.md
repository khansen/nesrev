# Fixed-ID reference-page delivery proposal

16 November 2026; implementation authorized 17 November. The
[offline measurement](FG1_LAUNCHER_INTEGRATION.md#offline-facts-image-feasibility)
established that the pinned Codex client carries a standard MCP image block into
its next request as an image item. This proposal closes that reference-delivery
gap for the selected fresh-game pass. It adds no reference acquisition, runtime
worker, native shell access or alternative review workflow.

## Decision and boundary

Extend the existing `input` operation for the **Codex implementer** to return one
selected PNG by fixed ID. Keep Claude's admitted native `Read` route. Reuse the
[declared-input catalog](DECLARED_INPUTS.md), captured payloads, generation checks
and restored-review integrity checks. Do not add a caller-supplied path, URL,
crop, renderer, size override or arbitrary binary-reader operation.

This is preferable to attaching every page at startup: pages remain available
on demand, including after context loss. Enabling native `view_image` would
reopen the measured code-mode boundary. An unmeasured Claude MCP-image route
would add a second client question without helping this pass.

## Page preparation and hashes

Prepare full-page PNG derivatives whose width **and** height are at most 2,048
pixels, preserving aspect ratio, orientation and the complete page. This happens
once in operator preparation, before the selection is sealed. The service never
resizes or re-encodes a page while answering a request.

The eight retained pages are all 2,080 × 794, totalling 10,534,353 source bytes.
They therefore need fresh bounded derivatives; none has been produced for this
design. The existing local Poppler renderer supports `-scale-to 2048`. Use that
existing PDF-rendering path, pin its executable/version and exact arguments, and
record original-PDF hash, PDF page number, printed-page identity and conversion
identity in the existing selection metadata. Do not introduce a runtime imaging
dependency. Keep the earlier images, selections and evidence unchanged.

Make a fresh disposable preparation from the same project state. Both roles get
the same new catalog and derivative identities. Their original PDF/page identity
stays the same; their derivative hashes change explicitly. The catalog's
`sha256` is the hash of the exact PNG bytes the service returns and Claude reads.
Do not call it a hash of pixels subsequently processed by a provider or client.

Before building the route, make one credential-free loopback capture of a bounded
derivative. The earlier capture proves that an oversized image is resized; it
does **not** prove that an image below this threshold is passed through unchanged.
Require unchanged dimensions and an outgoing PNG no larger than 3 MiB. A byte
change alone is not a stop: record both hashes, use the measured outgoing size
for conversation accounting and continue. Stop if dimensions change or the
outgoing PNG exceeds the cap. Keep client feature flags unchanged, and check
these same conditions for every page in the later eight-page capture.

## Operation and role behavior

The request remains:

```json
{"operation":"input","arguments":{"generation":"<current>","input_id":"<selected-id>"}}
```

`input_id` is the existing public field. The feasibility stub's synthetic `id`
argument was not a production-service schema test. Acceptance must use the real
request above through the bridge.

| Caller / item | Result |
| --- | --- |
| Either role, text ID | Existing exact paged text and existing offsets/limits. |
| Corridor implementer, selected image ID | One hash-checked PNG as MCP image content, plus bounded identity metadata. No text encoding of the payload. |
| Claude reviewer, selected image ID | Existing `INPUT_MEDIA_REQUIRED` refusal; help directs it to the matching admitted workspace file through `Read`. No MCP image is returned. |
| Retained-review reader, image ID | Same media refusal; native-media admission is not added to this reader. |
| Unknown or unselected ID | `INPUT_UNKNOWN`, with no payload. |

Image requests must omit text-only `offset` and `limit`; explicit values are a
schema refusal. One ID means one complete page, never a batch or implicit page
selection. Text requests retain their current defaults and limits.

Resolve the public generation through the existing corridor/retained ancestry
checks. Check the sealed catalog and payload hash before returning anything.
Only captured `reference_image` items qualify; an original PDF blob, a text item
containing base64 or an arbitrary capture filename cannot become image content.
Role comes from the bridge's fixed launch configuration, never from arguments.

Use a small internal image-result type carrying PNG bytes and metadata, created
only by the checked input reader. Preserve its public generation identity when
the corridor maps a retained head to an editor generation. The bridge recognizes
this type only for corridor-implementer `input`, and emits standard MCP content:

- one `text` block containing generation, input ID, catalog hash, derivative
  hash, MIME type, byte count, dimensions and original page identity;
- one `image` block with `mimeType: image/png` and base64 encoding of those exact
  bytes. The binary is not embedded in the metadata's text JSON.

All other results keep their existing JSON/text handling. Authored document text
cannot opt into the image exception by imitating a result dictionary. No generic
response-size exemption is introduced.

## Limits and conversation cost

These are proposed fixed admission limits, not observed provider maxima.

| Boundary | Limit and enforcement |
| --- | --- |
| One returned PNG | 3 MiB (3,145,728 bytes); positive dimensions at most 2,048 × 2,048. Validate the PNG header and payload identity before encoding. |
| One serialized image MCP reply | 4 MiB + 24 KiB (4,218,880 bytes), including JSON-RPC framing/newline. Refuse before emitting if exceeded. |
| Metadata and ordinary text | Existing 24 KiB ceiling stays in force. Metadata must fit that budget independently of image data. |
| FG-1 prepared page inventory | At most eight eligible pages, each meeting the above checks. This is a Codex/pair preparation condition; it does not silently reduce the general catalog's existing 16-page storage contract. |
| Per native conversation | Guidance: fetch only needed pages, normally once each; at most eight successful image deliveries including repeated IDs. Count deliveries across resumed turns and compaction, not just one invocation. |

The 3 MiB cap leaves room above the measured 2,409,323-byte re-encode. It is a
judgment bound, not proof that the freshly rendered inventory fits. Refuse an
ineligible inventory before launch; do not lower resolution further, drop pages
or raise a limit silently. The existing original-PDF/storage limits still apply.

The conversation count is **guidance and an audited acceptance condition**, not
a new persistent service quota. This slice adds no counter transaction or native
history editor. If a ninth delivery is needed, the agent records the missing
evidence and stops for a decision. If the agent exceeds the guidance, record the
excess as a process failure. Do not claim a mechanically enforced session cap.

A page can remain in history and be retransmitted on later requests. Eight
maximum-sized PNG deliveries contain up to **32 MiB of base64 image data** per
later request, plus metadata, tool framing and the rest of the conversation.
Repeated deliveries can add repeated image items. Eight copies at the measured
transmitted size alone would contribute about **25.7 MB** of image data URLs;
the actual eight pages differ. Their old source encodings total about 14.0 MB,
but that is not a forecast of their post-preparation or native-request sizes.

Do not preload all pages. Start from the catalog and relevant text; fetch a page
when the visual evidence is needed. After compaction, fetch again only when that
evidence is no longer available, counting the repeat. Measure the complete
eight-page request offline before live admission, including exact returned and
transmitted bytes. Record image deliveries and usage in the smoke and real pass.
Wire bytes are not an image-token or price estimate; provider processing and
cache savings remain unmeasured.

Before the live window, read the provider's published request limits and record
the source, date and applicable endpoint. If the worst case approaches a
published limit, tighten the eight-fetch guidance with room for the remaining
conversation. Do not treat an API limit as a guarantee for a subscription
endpoint; mark undocumented limits as unknown. This documentation check uses no
inference and does not substitute for live acceptance.

## Client inputs and declaration pins

For newly prepared Codex declared-input profiles, copy the sealed role assembly
into the private profile as today, but put no images in the client workspace
and grant no native-media reads. Leave `view_image`, shell and code-mode host
disabled. The assembled prompt names fixed page IDs and `input` calls, rather
than telling Codex to use workspace image paths. The assembly still verifies
every payload hash and page identity. Unsupported standalone `--media` usage
must refuse for this facts-only path rather than silently enable `view_image`.

Claude keeps the matching selected files in its isolated workspace, the same
hash-pinned `Read` allowlist and its restricted-mode checks. Its prompt retains
native paths. Both role prompts state the current pass scope and preserve the
existing historical-archive separation. Pair preparation continues checking the
shared catalog, item list and task; transport instructions may differ by role.

**The `input` help text changes.** Explain role-specific media delivery, image
request shape, caps and conversation guidance in the offered help and assembled
role inputs. In the same implementation change:

1. Capture the full native Codex declaration offline, review its exact diff,
   then update `DECLARATION_SHA256` and the captured declaration test fixture.
   Changes outside the intended facts help/schema are a stop, not a new pin.
2. Regenerate and pin the pair's implementer, Claude reviewer and retained-reader
   declarations, including descriptions. Both corridor roles must be covered.
3. Refresh the Claude reviewer declaration evidence and fresh client profiles.
   The Claude adapter currently pins bridge code, while the pair pins its full
   role declaration; neither substitutes for the smoke's actual tool observation.

Old profiles and prior admission seals stay unchanged and cannot be reused as
evidence for the new declarations. No hash is predicted or installed by this
design. The hook-disabled reviewer probe still runs first in the later,
separately authorized live smoke.

## Acceptance and implementation boundary

Offline acceptance uses the real bridge and admitted captures, not just the
image stub. It must cover:

- selected page ID returning exact retained bytes and original page identity,
  including after restoration with the original input folder removed;
- unknown/unselected IDs, extra path/URL/size arguments, stale or unrelated
  generations, payload/catalog drift, wrong kind and symlink replacement;
- PNG bytes or dimensions over the cap, malformed dimensions, and an encoded
  reply over its cap: all refuse without a partial image;
- unchanged text pagination and 24 KiB refusal, plus a text result imitating the
  internal image marker that cannot obtain the larger allowance;
- Claude and retained-review image refusals, unchanged Claude `Read` delivery,
  and no native Codex image or shell/code-mode grant;
- all declaration pins, changed-help refusal, complete assembled role prompts
  and the image-delivery guidance on initial and resumed turns;
- a scripted native capture fetching the eight prepared pages, comparing each
  service-returned and outgoing image hash, counting calls and measuring the
  resulting request. This is a transport test, not model readability evidence.

Discriminating controls must catch skipped payload verification, a wrong page,
an image-size bypass, a widened text ceiling and a stale declaration pin. Reuse
existing tests and capture helpers; no new testing framework or image engine.

The later live smoke adds a **positive readability control for both roles**:
freeze one unambiguous fact from an illustration on a selected reference page,
not from printed text. Check it against the OCR for every manual page and every
other declared text extract, guidance item and prompt. Keep the answer key
in coordinator evidence only. The prompt asks for that fact and its page ID;
Codex must fetch the image through facts, Claude through `Read`, and each must
answer correctly. Record the attempted call, returned page identity and answer.
A correct guess without image access, wrong answer or no answer fails. If no
suitable image-only question can be established offline, stop smoke preparation
for review; do not substitute a text-search question. Hook-off denials still run
first, and this design grants no live invocation or retry.

Estimated implementation: **2–4 active hours, hard bound 4**, charged to the
existing 16-hour launcher bound; this is an engineering estimate. Check at one
hour, or earlier after bounded-page capture: report normalization provenance,
native byte preservation or re-encoding, measured outgoing sizes, the eight-page
inventory and exact code/pin write set.
Up to three planned credential-free loopback invocations belong in the future
authorization: bounded-page precheck, rejecting declaration capture, and the
eight-page real-route capture. Provider calls remain separately authorized.

Stop on changed image dimensions or an outgoing PNG above 3 MiB, a failed
inventory limit, new tool
exposure, inability to preserve role separation or restored input identity, a
new rendering dependency, a required persistent quota/transaction framework,
or the time bound. A failed live smoke never authorizes another attempt. Return
the measured result and proposed correction before widening this slice.
