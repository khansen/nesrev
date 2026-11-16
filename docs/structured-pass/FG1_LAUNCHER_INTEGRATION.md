# FG-1 launcher integration and admission stop

16 November 2026. The [authorized continuation](FG1_LAUNCHER_SLICE.md) fixed
transient watch failures and connected the existing launcher, notifier and
adapters offline. A native-client measurement then found a missing reference
image route for the implementer. Smoke preparation stopped before authentication,
authorization or provider calls. This is not a completed launcher admission.

The goal remains one substantive fresh-game corridor through independent
review and local application. Delivering the selected references to both roles
is part of that goal; dropping images to finish a smaller smoke would not satisfy
the accepted input contract.

## Watch correction and integration

The continuous watcher now retries `REVIEW_STATE_BUSY`,
`VALIDATION_IN_PROGRESS` and `REVIEW_RESTORE_IN_PROGRESS` after one interval,
within the original timeout. A busy `--once` returns 3, meaning no turn yet.
Every other error remains fatal. Tests hold each of the review and validation
locks, prove the watcher stays alive, then release it and observe one delivery.
A changed retained report still stops it. Removing the retry branch fails the
test. The poll interval remains two seconds in the pair launcher.

The new [supervised pair entry point](STRUCTURED_PAIR.md) adds:

- session-local watch routing, exact message records and duplicate identities;
- a serialized invocation of the existing adapters under the shared heavy lock;
- distinct Codex messages on the same native thread, with profile/run/thread pins;
- shared expiry, an immediate pre-spawn check and descendant cleanup;
- authoritative handoff, unfinished and closed results, with explicit steering
  and extension rather than automatic retries;
- checked workspace ancestry, matching role input assemblies and full service
  declaration pins;
- trusted application through the existing journal, requiring separate authority.

Claude's raw output is retained before parsing, including a malformed trailing
event. The existing `REVIEW_NOT_READY` refusal is now a public typed error.
Ordinary launch behavior retains its existing path.

## Offline evidence

| Check | Result and limit |
| --- | --- |
| Watch regression | 17 tests passed, including both held locks, busy timeout and retained-report drift. Removing the retry branch is caught. |
| Full structured suite | Final run: 372 tests, one opt-in skip, OK in 164 seconds. Uses synthetic clients, not provider inference. |
| Full repository gate | `make test` passed: 692 shell tests and 1,206 Java tests; strict playbook and repository-hygiene checks passed. |
| Focused ordinary and adapter regression | 101 tests passed in the pair/client-result/ordinary-tmux run; an earlier adapter/input regression passed 118. These overlap the full suite and are not additive coverage. |
| Standalone production tmux path | Real watcher, generated notifier, adapter entry points and heavy wrapper with synthetic local clients. Publication handed off to review; request-changes handed back to the same implementer thread; normal return without progress stopped as unfinished. Both panes exited and recorded processes were reconciled. |
| Six integration fault controls | Caught exit-zero-as-handoff, ignored workspace ancestry, initial-message reuse, omitted declaration pin, spawn before expiry check and forgotten delivery identity. All failed through assertions. |
| No-media native declaration | Fresh credential-free profile, copied pinned client, rejecting localhost endpoint. One request; full declaration matches the candidate pin and native rollout. No inference. |
| Media native declaration | Same configuration with one pinned PNG. One rejected local request; the declaration changes and the current gate refuses it. No inference. |

Unit tests already holding the shared lock omit a nested acquisition. The separate
tmux exercise covers the unmodified production heavy wrapper and notifier. The
synthetic programs perform fixture service operations from the coordinator; they
do not establish model behavior or client confinement.
The standalone pair deliberately stops at unfinished rework. It does not cover
pair-driven closeout and application end to end; those reuse existing service
tests and still need integrated acceptance before functional admission.

### Superseded-notification correction

Independent review then reproduced a normal multi-publication turn halting the
pair: a queued reviewer notification waited behind the implementer, whose next
publication replaced its head, status and prompt. The correction carries the
watcher's original identity into the notifier and records a superseded delivery
as dropped, with exit zero. The next poll delivers the current prompt once;
the dropped notification consumes no client invocation or response allowance.

The affected pair, structured-handoff and ordinary-launcher suites passed 120
tests, and all three ordinary watcher shell tests passed. Both concurrent races
passed: two publications in one turn, and a reready
followed by publication with no status change. Another test covers the prompt
changing before notifier entry. Restoring the fatal refusal fails both concurrent
tests with watcher exit 2 instead of timeout exit 4. The production tmux exercise
also passed with two publications in its first turn: one recorded drop, exactly
one reviewer turn with the current prompt, then the same-thread unfinished stop.
Both panes exited, no halt was recorded and processes were reconciled.

Changed runs, paths outside the handoff, repeated delivered identities and prompt
drift without a new identity still refuse. The duplicate-after-lost-marker case
remains deferred. No adapter boundary or media route changed. The earlier full
structured and repository-suite results above are carried forward, not rerun
claims for this correction. The separate media feasibility check remains an
owner decision; no provider calls were made.

Two correction-harness mistakes are retained separately: the disposable mutant
copy initially lacked its fixture's scratch directory, and a literal shell-test
filter selected no tests. Neither counts as a passing check or a caught fault;
the corrected runs above supplied the evidence.

Harness corrections are retained: a busy-lock fixture initially used the wrong
generation field; a pair fixture placed retention outside its permitted root;
and a synthetic rollout filename lacked the native scanner's required prefix.
The corrected tests preserve their original acceptance. Failed observations were
not overwritten or called successful.

## Media admission stop

The declared-input adapter copies selected PNGs into the isolated Codex workspace
and sets `features.view_image=true`. The previously admitted callable contract
allows only the direct facts operation. Shell and code-mode execution are off;
the four visible `functions` tools are forbidden and audited.

The copied Codex 0.167.0 client, with the selected model catalog, produced:

| Configuration | Direct tool names | Full declaration SHA-256 | Result |
| --- | --- | --- | --- |
| No media | Facts plus the four forbidden functions | `9964a2c5cfdf78570cb915276b7cfc4411f6fe963806fff0ba28e07009aa6d00` | Current pin matches |
| One selected PNG | Same direct names | `f76184e71a14fda75d2108357061f39d345147bc62865b1d9be28b41e86ebd26` | `CODEX_TOOL_DECLARATION_CHANGED` |

The only added nested capability is `view_image`, inside the forbidden
`functions.exec` declaration. It is not a new direct callable tool. The native
rollout records match both captured requests. Both runs used a custom loopback
provider with no credentials, returned an error, and left no matching processes.
This does not establish the authenticated catalog's behavior.

Two existing adapter checks independently expose the inconsistency: its session
resolver accepts only facts calls, and feeding a synthetic allowed `view_image`
hook row into its monitor yields `CODEX_HOOK_UNEXPECTED_ALLOW`. The latter is a
component control, not a native image-read attempt. Merely accepting the second
hash would not create a usable image route.

The prior input-delivery tests established copied bytes and input-assembly pins;
they did not establish that this native client could read the images. The earlier
on-demand delivery statement was too broad for Codex. Claude's separate selected
media evidence remains unchanged. No tool grant, code-mode setting, boundary or
acceptance criterion was weakened in response to this finding.

### Offline facts-image feasibility

The owner then authorized a two-hour, credential-free loopback measurement,
charged to the existing bound, stopping before transport implementation. One
scripted response asked for a fixed page through `mcp__facts__operation`. A
disposable MCP stub offered the unchanged production declaration and returned
that page as image content. The client's next request carried an `input_image`
inside the corresponding `function_call_output`, alongside a short timing text.
The base64 was the image item's data-URL encoding, not text presented as evidence.

| Measurement | Observed |
| --- | --- |
| Selected page | Largest of eight retained pages; PNG, 2,080 × 794, 1,755,369 bytes |
| MCP return | Source bytes unchanged; JSON result 2,340,561 bytes; JSON-RPC line 2,340,601 bytes |
| Image in the next request | PNG, 2,048 × 782, 2,409,323 bytes after client resizing/re-encoding |
| Entire next request | 3,232,669 bytes |
| Native model | Explicit `gpt-6-astra`, `xhigh`; embedded catalog allows text and image input |
| Calls | One facts call, one hook allow, two loopback HTTP requests, zero provider calls |

The full declaration still matches the existing no-media pin. Shell, code-mode
host and native `view_image` remain disabled, and the session audit reports no
forbidden calls. The isolated profile contains no credentials or fetched model
catalog. The second request was deliberately refused with HTTP 400 after capture;
the adapter therefore records `CODEX_CLIENT_FAILED`, not a successful live turn.
Raw requests, native output and the MCP response were retained before reduction;
process cleanup completed with no survivors.

This establishes image transport feasibility for the pinned client and its
embedded catalog. It does not establish provider acceptance, model readability,
unchanged image bytes, authenticated catalog behavior or a production service
route. The live model's use of the page remains an admission check. No declaration
was re-pinned, no gate changed and no transport was implemented.

## Decision required and remaining work

The media measurement is complete; stop before implementing its route. The draft smoke prompt
and preparer remain private, unexecuted and unsealed. There is no new live
authorization request to approve yet.

The next decision is the bounded route design: return a selected, hash-checked
page by fixed ID through the existing facts tool, with an explicit image limit
separate from the text-response ceiling. The measured sizes include base64 and
client re-encoding overhead. This keeps the callable boundary intact, but adds a
transport contract that returns for review before implementation. The
[fixed-ID route proposal](FACTS_IMAGE_ROUTE_DESIGN.md) specifies that contract,
role separation, conversation-cost guidance, pin refresh and readability checks.

Other choices have different costs: attaching all selected pages at startup
changes on-demand delivery and context cost; exposing a direct native image tool
requires new client configuration/admission evidence. Enabling general code-mode
execution is not authorized. Omitting required images cannot pass acceptance.

After that decision: finish the smoke harness and failing controls, freeze fresh
client profiles and declarations, and request the separately authorized live
window. The hook-disabled reviewer probe still runs first. The unscripted game
pass remains a later authorization. Neither the offline launcher results nor the
no-media declaration capture closes those gates.

The private continuation packet retains source code pins, local native requests,
session records, test logs, deliberate faults, process records, timing and owner
state. No reference payload or personal path is included in this shared record.
The working interval, including offline checks, is charged conservatively;
combined effort remains below the eight-hour report point and sixteen-hour bound.
The released checkpoint fixture and four completed disposable roots were copied,
hash-checked and removed. The project head, review state, untracked project files
and four stashes are unchanged. Concurrent article edits were observed and left
alone. The implementation branch has not been pushed.
