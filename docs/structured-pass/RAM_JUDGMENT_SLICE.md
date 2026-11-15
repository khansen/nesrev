# RAM evidence and judgments: slice 1

15 November 2026. Authorized offline under the
[post-intake slice plan](FRESH_GAME_PASS_MEASUREMENT.md#proposed-slices-costs-and-checkpoints):
12 active hours maximum, a checkpoint by two hours, one review round, no provider
calls. The owner authorized the compact view and an independently deliverable
D3 writer. This work removes a required write gap for FG-1; it does not complete
a semantic pass or authorize one.

## Early checkpoint decision

**Park compaction; continue the judgment writer.** The first service measurement
missed the fixed eight-request bound, so the compact endpoints are not shipped.
The checkpoint was recorded at 20.8 charged minutes, within the two-hour limit.
No new analysis engine, broader access or raised request limit was introduced.
The private packet `structured-ram-slice-20261115` retains the failed experiment,
its complete responses and code, alongside the original prototype.

The prototype losslessly encoded the existing native RAM facts as columns and
rows. It shared only unresolved indirect destinations, whose membership is
independent of the requested byte. Indexed possibilities stayed per-byte because
their membership changes across address ranges. No unknown was treated as an
exact access or discarded.

| Question | Complete evidence rows | Cold requests, including status | Requests after shared-set reuse, including status |
| --- | ---: | ---: | ---: |
| Measured field A, through the service | 311 | 8 | 5 |
| Measured field B, through the service | 312 | 9 | 6 |
| Two addresses outside zero page, prototype only | 125 / 118 | 5 / 5 | 2 / 2 |

Both service expansions equal the existing complete RAM view, including stable
record identities, access categories and alias-proof fields. The prototype had
predicted eight requests for both measured fields: it removed another repeated
field and used less response metadata. The actual endpoint preserved that field
and included the full metadata, adding a page for the second field. Service
checks outside zero page were not reached after the stop. Their prototype
numbers are not service acceptance. The legacy RAM endpoint is unchanged.

## Independent writer

`raw_ram_judgments` updates existing rows through the existing candidate,
validation, publication, review and application path. The
[API contract](README.md) permits authored status/name/notes only. Address
identity, row membership and generated facts remain protected. File and row
preimages bind changes to the selected generation; the service supplies the
pass number. It does not infer a semantic judgment or make evidence sufficient.

Validation reconstructs the expected authored result from the recorded operation
before accepting trusted factual refresh. Restoring the whole original file
cannot silently erase a requested judgment. Retained review distinguishes
authored fields, the derived pass number and generated refresh. No root-document,
policy, friction-import, launcher or runtime operation is added.

## Evidence and limits

- Seven new tests cover immutable addresses and facts, both preimages, status
  validation, derived pass identity, multiline record preservation, unauthorized
  refresh changes and wrapper restoration of the old file. The synthetic
  lifecycle includes reviewer write refusal, preview, validation, publication,
  restart, retained review, closeout and repeat-safe application.
- Five deliberate in-memory faults were caught by failing assertions: granting
  a factual column, ignoring a row preimage, omitting the derived pass number,
  accepting an unrequested judgment and ignoring restoration of the whole file.
- The structured suite ran 324 tests successfully, with one opt-in client check
  skipped. An earlier sandboxed run could not inspect local processes; its
  failures are preserved separately from the successful unrestricted offline run.
- Full `make test` passed: 692 shell cases and 1,206 Java checks. The strict
  playbook checker reports zero warnings; hygiene and relative links pass.
- On the accepted intake, a disposable judgment edit passed inventory,
  naming-only verification, process and documentation checks. Published retained
  review shows the authored note and derived pass number. Source bytes remained
  identical. This uses the current-project editing service directly; it does not
  substitute for the corridor's required scorecard/closeout operation.

The synthetic lifecycle uses explicitly simulated quality gates; the real-code
probe uses actual gates but stops at publication and retained inspection. No
real-game closeout, independent agent review, semantic pass or provider call is
claimed. No probe judgment is applied to the owner's project.

Preparation first refused an empty fresh toolchain store, before running checks;
the already pinned runtime was then copied into it. The first writer harness
correctly met `CORRIDOR_WRAPPER_REQUIRED` when it omitted closeout. The corrected
probe explicitly tests the editing service rather than claiming a complete pass.
Its reducer then read the wrong publication response key; the retained result
was reduced correctly without rerunning validation or publication. All attempts
remain in the private packet.

The working interval was about half an hour, conservatively charged in full
including local test waits. This is below the shared 12-hour limit; no owner
wait or overnight interval is included. The unchanged protected-state record
covers the main project head, owner files, supplied inputs, review state and
all four stashes.

The complete RAM-read practicality gap remains a required FG-1 dependency. A
later decision may compare denser transport with safe indexed-set reuse. This
slice does not select that work, and the eight-request and 24 KiB limits remain
fixed. D3 can be reviewed and delivered independently of it.

Subsequent owner decision: a separate two-hour [compact-read follow-up](RAM_COMPACT_FOLLOWUP.md)
was authorized and reached the unchanged request limit through the service.
The stopped experiment above remains its historical result; the follow-up has
separate code, evidence and review.
