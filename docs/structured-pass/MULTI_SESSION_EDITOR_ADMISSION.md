# Bound editor admission: stopped

The next step after the [integration checkpoint](MULTI_SESSION_INTEGRATION_CHECKPOINT.md)
was to bind the editor's actual launch artifacts before building shared budgets
and recovery. That check **fails**. The agreed stop rule applies: no further
reductions, no native recipe, and no live attempt. The owner must choose between
splitting editing across contexts and using the ordinary workflow.

| Charge | Checkpoint | Bound preparation |
| --- | ---: | ---: |
| Initial instructions, opening message and declaration allowance | 12,678 tokens | 13,102 tokens |
| Startup including those initial inputs | 80,909 tokens | 81,333 tokens |
| Complete editor estimate | 232,509 tokens | 232,933 tokens |
| Remaining context | 25,891 tokens | 25,467 tokens |
| Required margin | 25,840 tokens | 25,840 tokens |
| Surplus against the margin | 51 tokens | **−373 tokens** |

The initial charge uses the existing measured baseline of 7,800 tokens and
2,000-token framing cushion. It adds positive byte growth at the unchanged
worst rate of 2.58 bytes per token, with at least 256 declaration bytes reserved.
The client receives the task in both its assembled instructions and its opening
message. Compared with the retained baseline, those two artifacts grew by
4,948 and 3,314 bytes respectively. The final declaration candidate is smaller
than that baseline, so it receives no negative credit and keeps the 256-byte
reservation. The prior 12,678-token initial charge remains a floor.

Fresh preparation used the production assembler, input assembly and Codex
profile builder, without launching a client. It delivered the same 274 edit
targets and 67,489 edit-record bytes, with all 19,648 hash characters still
charged at one token each. The reference grew by 3,819 wire bytes, inside its
unchanged 8 KiB reservation. The 64 KiB handoff cap, 8 KiB transition reservation,
48K lifecycle reserve, measured unscripted overhead, next-response reservation
and 10% margin remain unchanged. Required response volume is 231,878 of the
264,604-byte allowance; the token margin is what refuses admission.

The new binding records the actual assembled instructions, opening message,
startup inputs, generated service listing, native declaration envelope, plan
and edit targets. Pair preparation/verification and the initial Codex launch
check require that binding for a prepared investigation workflow with startup
inputs. Drift or a failed price refuses. A reference reservation cannot pay for
growth in another startup input, and smaller deliveries do not lower the prior
charge. The final native declaration remains a **candidate**, not a recaptured
or admitted pin; the ordinary native pin is deliberately unchanged.

The fresh layout's bound report was written before the launch check, which
refused it. No subsequent price reduction was attempted. Forty-five focused
tests cover the admission calculation, whole-corridor pricing, investigation
workflow and pair integration. Three faults—omitting opening-message growth,
skipping the reference cap and skipping artifact binding—are caught. Restoring
the code passes the admission tests again.

This is a stopped implementation checkpoint, not release acceptance. The
earlier full suite still has two stale native declaration fixtures; it has not
been rerun for this change. `make test`, final native recapture and CI remain
pending. This step uses zero native invocations and zero provider calls: two of
ten invocations remain used, with eight unspent. Shared-budget/recovery work
and the final recipe have not started.
