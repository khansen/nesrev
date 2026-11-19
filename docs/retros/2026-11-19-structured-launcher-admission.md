# Structured launcher and client admission retrospective

The intended outcome was a usable, bounded Codex-implementer / Claude-reviewer
loop for one unfamiliar-game pass. The accepted
[r5 smoke](../structured-pass/FG1_LAUNCHER_ACCEPTANCE.md) now demonstrates the
launcher portion: restricted reads with the hook absent, readable reference
images, publication, independent request-changes, and notification back to the
same implementer thread. It stopped deliberately at unfinished rework. A complete
unscripted pass, closeout and application remain the next operational outcome.

The final live run took 84.6 seconds, four invocations and 28 tool calls, with
zero retries or client approval prompts. Eight restricted-path denials were
attributed to structured client events rather than prose. Both visual answers
were checked against an illustration whose answer was absent from the declared
text. These are bounded observations on pinned clients, not a general containment
or cost claim. Native clients have not gained an OS sandbox.

## What made the boundary reviewable

Existing service state, watcher protocol, adapters and heavy-run supervisor
carried the integration. Authoritative state distinguished handoff from a normal
exit without progress. Concurrent tests found two ordinary races before final
admission: temporary service locks must keep polling, and a notification replaced
by a newer publication must be dropped rather than halt the pair. Both fixes
preserved the deadline and genuine integrity refusals.

Measuring the pinned clients changed the design. Codex's native image tool was
only available inside disabled code mode. A credential-free loopback capture
showed that facts-tool image content could reach its next request instead.
Bounded page derivatives then arrived byte for byte without widening callable
access. Claude retained its selected-media Read route.

Real-model admission also found missing production instructions. A named
operation did not tell the implementer that validate consumes `cid`; listing
that key still did not explain that it comes from `confirm.candidate`. Generated
argument tables now share dispatch's source, and delivered identity paths are
tested against real lifecycle results. Captures proved both clients received
the complete contract. The scripted rehearsal was changed to consume those
delivered paths rather than supply the missing knowledge itself.

## Where time and owner attention went

The recorded charge through accepted r5 was 32,142 seconds, about 8 hours 56
minutes of the 16-hour ceiling. This includes conservative reporting time and
is not a precise measurement of active engineering. The estimate alone hides
calendar friction: separate review and authorization rounds, isolated logins,
and one measured preparation approval wait of about 10.7 hours. That wait was
excluded from active effort and retained as a learning candidate. Zero prompts
inside the final client run does not mean zero coordinator or owner effort.

Several earlier live stops were avoidable harness assumptions: system messages
treated as conversation objects, images read from truncated event output,
denials classified by prose, valid optional arguments rejected, and a hook-off
profile lacking a facts allowance. Preserved real streams and complete native
loopback rehearsals provided a better basis than synthetic success streams.
The final four-phase rehearsal exercised actual settings, declarations, watcher
notifications and same-thread continuation before the next authorization.
Failed attempts and their authorizations remained distinct throughout.

One implicit runtime effect still escaped the rehearsal's expected-change list:
handoff initialization appends its standard Git ignore block. The post-run
reporting helper stopped on this and was corrected openly. Future expected-change
lists should come from the actual prepared layout. The same report corrected
cumulative Codex usage rather than double-counting resume. A passing functional
run still needs careful evidence accounting.

Login cleanup also needed a complete inventory. After acceptance, twelve isolated
profiles were checked using native status and logout: six were already logged
out and six remained active. Non-empty folders alone did not establish login
state. All now report logged out, their configuration homes are removed, and
non-auth evidence is retained with relocation records.

## What follows, and what does not

Upstream the reviewed implementation and accepted evidence after final checks
and explicit publication authorization. Keep the remaining reviewer identity
reachability, multi-round contract test and description-size headroom in the
separate readiness scope. Do not quietly fold new service capability into the PR.

The next process outcome is one substantive unfamiliar-game corridor through
review, qualified closeout, observations and local application. Its authorization
must carry its own usage, time and owner-attention bounds. The smoke's very small
reasoning output is not a forecast for that work. Runtime or another missing
operation remains a decision point if the actual corridor needs it. This milestone
supports that next experiment; it neither completes the larger rollout nor
justifies unrelated infrastructure work.
