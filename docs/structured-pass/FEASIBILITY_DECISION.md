# Structured execution: feasibility decision

**Accepted checkpoint: 14 November 2026.** App Sandbox is a workable boundary
for the tested, declared macOS worker runtimes. A packaged Python analyzer and
the configured emulator performed useful work with per-job inputs and outputs,
while protected accesses were refused. The real reviewer used facts and reference
media without approval prompts. Its independent protection when the hook is
disabled remains untested.

This records the completed investigation, not a production-worker release or
authorization for another run. The [workload assessment](TRIAL_WORKLOAD_COVERAGE.md)
motivated it; the [milestone retrospective](../retros/2026-11-14-structured-feasibility.md)
records what helped and what cost avoidable effort.

## Question, alternatives and bound

The [manifesto](../MANIFESTO.md) calls for dependable reverse engineering across
unfamiliar games with little bespoke intervention. The retained workload showed
that typed operations need both better search and a safe route for authored
analysis and runtime evidence. Repeatedly teaching a general shell's permission
classifier new command spellings would not establish that route.

The checkpoint asked whether the intended reviewer and declared analysis runtimes
could do useful work inside enforceable boundaries. Attended ordinary operation
remains possible, but does not answer the unattended-operation question. Typed
operations alone cannot execute newly authored Python or Lua. A VM is another
candidate; it was not provisioned or compared in this investigation.

The selected first mechanism was Apple's public App Sandbox, enabled by the
`com.apple.security.app-sandbox` entitlement on locally signed disposable apps.
Neither deprecated `sandbox-exec` nor unsupported `sandbox_init` was used.
The relevant vendor contracts are [App Sandbox](https://developer.apple.com/documentation/security/app-sandbox)
and [embedded helper tools](https://developer.apple.com/documentation/xcode/embedding-a-helper-tool-in-a-sandboxed-app).
Distribution and long-term packaging were outside this spike.

The original plan set an eight-active-hour reassessment and a sixteen-hour
ceiling, with earlier stops for new dependencies, recurring blockers or failed
boundary cases. The owner authorized bounded continuations as dependencies were
identified. Provider-backed reviewer tests had separate authorizations. Local
harness corrections retained their failed observations; no failure authorized
broader host access or an automatic new live attempt.

The stages were a native boundary/control pair, real Python job transfer,
reviewer launch/resume and media access, then emulator capture and lifetime.
All inputs were synthetic. Real credentials, source checkouts and service stores
were represented by disposable canaries, not exposed to the worker.

## Combined results

The tested worker platform was macOS 27.2.1 on arm64. Runtime binaries,
dependencies, scripts, entitlements, inputs and acceptance rules were pinned in
the retained packets. Counts below describe separate experiments; they are not
one combined denial score.

| Question | Observed result | What it establishes |
| --- | --- | --- |
| Native OS boundary and inheritance | The control allowed all 46 rows. App Sandbox allowed the 13 intended rows and denied 33 protected read, write and network attempts across parent, child and grandchild. | The tested entitlement restricts native code and descendants, including in-process sockets. |
| Python analysis and per-job transfer | Python 3.15.2 plus its packaged dependencies analyzed inputs supplied after signing. The coordinator collected and checked a 2,994-byte output. Control: 25 allowed rows. Sandbox: three useful-work rows allowed, 22 protected accesses denied. | A bundled interpreter can process new job data and return results without the coordinator traversing its app container. |
| Real reviewer, reference media and resume | Claude Code 2.1.319 with Opus 5.5 and requested high effort completed four invocations on one session: 20 calls, 11 responses, about 38 seconds. Facts and selected PNG/PDF reads worked, including after resume; nine protected Reads were denied. | The offered-tool and hook configuration supports the tested reviewer workload without approval prompts. This is a synthetic fixture, not an unscripted project review. |
| Packaged emulator useful work | Both control and sandbox returned the expected trace and capture. All 32 protected accesses succeeded in the control and failed with permission errors in the sandbox. | The declared emulator/Lua workload can run inside App Sandbox with post-signing job inputs and collected outputs. |
| Emulator failure and lifetime | Capture, Lua error, forced timeout and cancellation passed in both configurations: eight cases, expected exits 0/71/73/72, no overrun or surviving process group. Cleanup took 2.13–2.17 seconds. | The tested supervisor handles completion and each declared failure path; shutdown is bounded and forced where needed, not a claim of graceful emulator exit. |
| Runtime closure and OS interaction | Loaded images in packaged runs came only from the bundle or system locations. Strict signature verification passed. Display and CoreAudio initialized; observation found no new unexplained or consent window. | The measured workload works with its declared resources and package, without expanding host access. Window sampling is not exhaustive OS-consent evidence. |

The emulator package came from a **completed installed-runtime measurement**:
51 non-system images, 111.38 MiB before packaging resources, including SDL3 and
the two Qt plugins actually used. Capture runs observed 53 non-system images
when the native coordinator and helper are included. The installed runtime was
unchanged. Every fresh ROM, Lua job and manifest was issued after signing through
read-only descriptors; trace and capture returned through exclusive write-only
descriptors. The coordinator did not stage files inside the app container.

Both traces contained marker 165 and palette 33, counter 115→125 and frame
counter 119→129, followed by completion. Control, sandbox and prior shakedown
captures were byte-identical. Acceptance checked five image points; whole-image
equality is an additional observation. The image includes the emulator's speed
overlay. The 32 protected probes comprise ten Lua file accesses and eleven each
in native child and grandchild processes. Network denial here is descendant
evidence; the separate native probe supplies the in-process socket result.

## Decision and limits

Proceed with App Sandbox as the demonstrated candidate for **declared macOS
worker runtimes** when worker integration is scoped. The investigation resolves
the principal feasibility risk behind that choice. It does not complete W2/W3,
2C, the launcher or fresh-game operation. The
[early-feasibility criteria](STEP_2_COVERAGE.md#early-confinement-feasibility)
and integrated acceptance obligations remain authoritative.

- **Reviewer second layer remains open.** Every protected Read was stopped by
  the PreToolUse hook with `STRUCTURED_PASS_DENY`. Restricted mode was present,
  but not independently exercised. Add a disabled/failing-hook case to the next
  separately authorized reviewer smoke; do not report the broken-hook criterion
  as satisfied. The alternate-path denial used the same code without the other
  results' hook-error prefix; that is not a second layer.
- **Integration is still work.** Packet/maturity analyzer launch paths were
  inspected, not run through this boundary. Their current subprocess invocation
  is not an OS boundary. Job admission, resource/output limits, cancellation,
  result validation and service publication need production contracts and tests.
- **Bundling has a recurring cost.** Each runtime and analyzer dependency needs
  a pinned, self-contained package. Python packaging does not establish support
  for arbitrary third-party imports; the emulator measurement covers this job's
  loaded libraries, not every future plugin or mode. Record maintenance effort
  before deciding whether a VM is cheaper. A Linux VM would also require capture
  comparability checks; none were performed here.
- **Client evidence is specific.** It covers one reviewer client/model/platform,
  a restricted tool set, selected media and a synthetic facts service. It does
  not OS-sandbox the native client or exhaustively exclude hidden ambient inputs.
  It does not establish reference-media delivery for the Codex implementer.
  Process sampling is not a syscall trace; fixture quality gates were simulated.
- **Not an unattended fresh game.** No full workflow, throughput improvement,
  token saving, cross-platform boundary or cost per completed game was measured.
  Login was an owner action before the reviewer clock started.

## Failed observations and effort

The retained record includes external-Python spawn refusal and an incomplete
embedded framework, an emulator bundle missing runtime-loaded SDL3, an installed
probe assuming unavailable LuaSocket, a guessed frame floor and an inadequate
shutdown grace. These are distinct packaging or harness findings, not failed
sandbox denials. A reviewer attempt also stopped on an unnecessary total-order
constraint among independent reads. Its failed verdict was not changed after
the validator was corrected.

The installed-emulator shakedown used one 45-minute allowance, retaining two
harness corrections and finishing in about 13 minutes. The final packaged
sequence used about 20 of its separately authorized 60 minutes, with no runtime
retry or provider call. Its eight cases occupied about 65 seconds; that is not
the engineering cost. A relative-lock-path preparation refusal occurred before
the build and is retained. Earlier failures, packaging and review effort still
count. These local intervals do not supply a fully reconciled active-hour total
for the whole checkpoint or calibrate the roadmap's delivery estimate.

Raw observations were retained before reduction. The shakedown's early window
log hash was reconciled as a prefix of the final log; the packaged run sealed
after the observer exited. Final integrity checks covered protected files,
runtime/package pins, signatures, and cleanup. Private packets preserve the
attempts, authorizations and diagnostic records rather than promoting them into
operating prerequisites.

## Evidence references

The following SHA-256 values identify locally retained evidence indexes. Their
contents include private machine paths, so they are not distributed with this
decision. The 13 detailed research notes and the failed-attempt packets remain
preserved locally; this record consolidates their conclusions without rewriting
their historical verdicts.

| Packet / index | SHA-256 |
| --- | --- |
| Native boundary / `INDEX.json` | `41a23a4af2ca6c3d20106aa660304999e119a4fcb2dffb0b75f8bee64c3e758f` |
| Python transfer / `INDEX.json` | `c478ae6d2f04c4291484e5abe866700b6ffe0e6f82f6e710416b76e8dc79f8c4` |
| Accepted reviewer / `LIVE_EVIDENCE_INDEX.json` | `e4be75a9ce438a93436f251d1e40d0a4dfb968dba088b2203fe7fc72b412d1c8` |
| Installed emulator shakedown / `EVIDENCE_INDEX.json` | `1b55920a8e3c73ebbca586360d59c3c3a27e560e2dd59cae32fea0cff5b752eb` |
| Packaged emulator / `EVIDENCE_INDEX.json` | `0e6039d4c14929d0efe255ba2c91b05086f9158ed14ee4a10933920db843e611` |

## Next decision

Scope typed instruction and registered-document search first, using the
assessment's **89 retained search calls** and eight-request practicality limit.
Search can be implemented and checked offline without a worker or launcher.
Owner approval of its scope is still required; a scripted result would not prove
that an unscripted reviewer can complete its work without fallback.

Workflow jobs, worker integration and a separate intake contract remain on the
[minimum path to a fresh-game pass](TRIAL_WORKLOAD_COVERAGE.md#minimum-path-to-one-fresh-game-pass-through-the-service).
The 80–176-active-hour envelope is an uncertain planning estimate, not a new
allowance or measured remaining cost. Record actual effort by component and
reassess it. The [launcher](LAUNCHER_DECISION.md) must precede any live structured
pass; none of these dependencies is an automatic implementation queue.
