# Fixed-ID image route: offline result

17 November 2026. The [approved design](FACTS_IMAGE_ROUTE_DESIGN.md) is
implemented. The real bridge and pinned native client delivered all eight
selected pages without changing their bytes. This closes the measured offline
transport gap; provider acceptance and model readability remain untested.

## Boundary

The corridor implementer's `input` operation returns one selected, hash-checked
PNG plus page metadata. Requests use a generation and fixed `input_id`, with no
image offset, path, URL or rendering argument. Existing capture and ancestry
checks select the payload. A private result type selects the image wire budget;
authored text cannot obtain that allowance. Text and image metadata retain the
24 KiB limit. PNGs have a 3 MiB cap, dimensions at most 2048 × 2048, and a
4 MiB + 24 KiB complete reply cap.

Codex retains the sealed page assembly privately; its workspace and native-media
allowlist are empty. Standalone native media preparation refuses. Shell, native
image and code-mode features stay off. Claude retains matching files and `Read`.
Reviewer and retained-reader facts calls still return `INPUT_MEDIA_REQUIRED`.
Eight deliveries per conversation remains audited guidance, counting repeats
across resume and compaction, rather than a persistent service quota.

## Measured delivery

Fresh full-page derivatives came from the hash-matched, owner-supplied PDF using
Poppler 26.11.0 with `-scale-to 2048`. The private record pins the executable,
version, full arguments, PDF and page identities. Earlier inputs are unchanged.
Fresh preparation passed on the same accepted project state, preserving its
naming-only qualification.

| Page ordinal | Dimensions | Returned and transmitted PNG bytes |
| --- | --- | ---: |
| 1 | 2048 × 782 | 1,020,232 |
| 2 | 2048 × 782 | 1,317,953 |
| 3 | 2048 × 782 | 1,131,207 |
| 4 | 2048 × 782 | 1,268,179 |
| 5 | 2048 × 782 | 1,349,311 |
| 6 | 2048 × 782 | 1,238,416 |
| 7 | 2048 × 782 | 1,713,635 |
| 8 | 2048 × 782 | 1,274,641 |

All three authorized credential-free native loopback invocations were used:

1. The largest bounded page passed the precheck with identical dimensions and
   bytes. Its next request was 2,305,090 bytes.
2. The old declaration pin refused the changed help. The captured declaration
   differs only in the facts operation's description; schemas and tools match.
3. Eight successive calls used the production bridge. Every image hash matches
   both the sealed derivative and the native request. There were eight hook
   allows and no forbidden calls. With all eight pages in history, the request
   was **13,795,385 bytes**, including **13,751,624 bytes** of image data URLs.
   The PNG total was **10,313,574 bytes**.

The first and third captures deliberately returned HTTP 400 after the final
request. Their `CODEX_CLIENT_FAILED` result is capture termination, not a
successful live turn. The second stopped on the old pin. No credentials or
provider inference were used. The selected model was `gpt-6-astra` at `xhigh`;
its embedded catalog permits images, but authenticated behavior is untested.

## Pins and acceptance

The native declaration pin is
`a402b53a734eba55c52788406b0fc17d00185c02d149e387016abd8903e1514f`.
Fresh pair preparation recorded all three full service declarations:

| Declaration | SHA-256 |
| --- | --- |
| Corridor implementer | `8ae0087589af8394233d817044479fd1e04df79a5b523248018fa39a306c0419` |
| Corridor reviewer | `07120b67a5ad51dce915c7a5fe3a5276f70f853f120c2580e806ef090b358826` |
| Retained reviewer | `63287890ce8a5735867f39d76b31fdda6c7fff8d1f6ea8f2ec4c84b0c5222b96` |

Both assemblies share the catalog, items and task. Fresh pair verification
passed; changing any declaration pin refused. Claude's configuration and
declaration evidence are offline preparation, not a live tool observation.

The real bridge returned eight exact pages after the operator folder moved;
all eight reviewer image calls refused. Synthetic lifecycle tests publish and
restore captured inputs without original files, preserving public generation
identity and reviewer restrictions. Tests cover unknown IDs, extra arguments,
generation/catalog/payload drift, symlinks, dimensions, byte and wire caps,
text pagination and fake image markers. Earlier selection-test gaps now have
cases for dot segments, symlink blobs, archive location, item limits, assembly
rechecks and the final text character.

The full structured suite passed **383 tests, one opt-in skip**. Five deliberate
faults were caught by assertions in a disposable copy: skipping the final
payload hash, substituting image bytes, bypassing image size, widening the text
ceiling and restoring the stale native pin. Production files were not mutated.
An additional in-memory control returned a different valid PNG under the
requested page's metadata; the byte-identity assertion caught it too.

`make test` passed **692 shell tests and 1,206 Java tests**. After normalizing
only the captured declaration fixture's JSON formatting, all six declaration
tests passed again. The parsed declaration remained identical to the capture.

Harness corrections are retained: the first fixture used a forbidden temporary
retention root; two assertions initially tested the wrong helper layer; the
outer sandbox blocked process-inspection tests; one focused command omitted
the test import path. Corrected focused tests passed 112 tests before the full
suite. No native invocation was retried or acceptance rule weakened.

## Limits and next step

On 17 November 2026, the provider's API documentation listed a 512 MB total
request payload limit, above the designed 32 MiB maximum base64 image data.
This does not establish the subscription endpoint's limit, which remains
unknown. Fetch relevant pages on demand; eight-page accumulation is a measured
worst inventory, not recommended startup behavior.
[OpenAI image-input requirements](https://developers.openai.com/api/docs/guides/images-vision).

A positive readability question has been prepared from an illustration. Its
answer is absent from the inspected page OCR and declared-text scan and stays
in coordinator evidence. Both roles must access that page and answer correctly;
a guess without the image call fails. Recheck final smoke prompts before sealing.
The hook-disabled reviewer probe still runs first. Neither live check ran here.

The private packet retains authorization, checkpoint, preparation, raw captures,
declaration diff, test and fault logs, and cleanup. Native profiles were removed
after preservation and process checks. Fresh unlaunched pair profiles remain
for review and are copied privately. Review this implementation, then finish
and seal the launcher smoke packet. Live smoke and the unscripted pass remain
separate authorizations.

The protected checkout's head, working files and four stashes are unchanged.
The implementation remained within its four-hour allowance and is charged to
the launcher's existing sixteen-hour bound; the private effort record includes
preparation, tests and this report.
