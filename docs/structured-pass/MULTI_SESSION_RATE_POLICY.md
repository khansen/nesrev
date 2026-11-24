# Measured format rates for session admission

The owner selected this policy before repricing the complete retained workloads.
It replaces the earlier assumption that 2.58 bytes per token bounded all new
formats. The edit probe passed its fixed decision; its diagnostic source and
RAM-set pages also established less favorable rates, which this policy uses.

| Charge | Bytes per token |
| --- | ---: |
| Edit responses | 2.398 |
| Source responses | 2.113 |
| RAM-set responses | 2.035 |
| Unscripted overhead and the next-response reservation | 2.035 |
| Other unmeasured bytes | 2.580 |

Use each format's lowest measured page, rounded down to bytes per 1,000 tokens.
Every measured page counts. Pair a tool output with the following request's
input-token count; retain intervening assistant, reasoning and framing costs.
The neutral [rate witness](../../tests/fixtures/structured_format_rates.json)
records the capture identity, page hashes, sizes and native counter locations.
No project text or credentials are included.

Preserve the prior request-argument charges and rounding, including conservative
hash premiums. Replace only the measured response charge. The overhead request
allowance uses 2.035 with its unknown responses. Future handoffs, assignments,
receipts and reference-growth reservations retain 2.58: the one synthetic
handoff does not justify discounting arbitrary future content.

Startup rates, input selection, coverage, all caps, the 48K lifecycle reserve
and at least 10% margin remain unchanged. Both the byte allowance and the token
gate must pass. Reports identify `measured-formats-v2`; a report computed under
an earlier policy cannot pass a recomputation under this policy.

The retained bound editor passes by 1,112 tokens beyond the margin; the tightest
investigator passes by 536. These are feasibility results, not final admission.
Rebind the editor after changes to prompts, declarations or inputs. A failed
editor gate still stops for an owner decision; an oversized investigation may
split by the already authorized whole-root or whole-RAM-range mechanism.
