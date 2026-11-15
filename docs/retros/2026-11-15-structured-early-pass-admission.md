# Retrospective: structured early-pass admission

15 November 2026. Milestone: [PR #192](https://github.com/khansen/nesrev/pull/192),
merged as `65704d7b0` at the independently reviewed head `5f568c645`.
This records learning, not new policy or authorization.

## Outcome

The structured service can now admit an early semantic source whose sole
verification exception is incomplete naming. Eligibility comes from the sealed
starting source; an initially clean source stays strict. Preparation, candidate
validation, closeout, archived review and application retain the qualification.
Gold and maturity standards are unchanged.

The [measurement checkpoint](../structured-pass/EARLY_PASS_ADMISSION_CHECKPOINT.md)
ran the full preparation obligations on three retained states before estimating
implementation. All other checks passed. The
[implementation evidence](../structured-pass/EARLY_PASS_ADMISSION_IMPLEMENTATION.md)
then exercised the complete service lifecycle on one of those states, alongside
clean-start fixtures and real defects in four verification families. Independent
review accepted the change; both required CI jobs passed on the reviewed head.

This removes a demonstrated process barrier. It does not demonstrate a live
fresh-game pass, lower operator effort or lower provider cost. The real-code
sample remains one game. Its offline review verdict tested the protocol, not
independent semantic judgment.

## What worked

Measuring beyond the first failing check prevented the original naming refusal
from being mistaken for the complete admission problem. The proposed exception
was tested against every later check before it became an implementation plan.
Reusing the existing verifier's naming-only mode kept the change narrow; the
service owns when it is permitted and preserves evidence of strict refusal
followed by a complete successful naming-only run.

The failure controls tested meaningful boundaries: byte parity, warning
baseline, stale comments, data extents, initially clean sources and attempts to
override the policy. Independent review also challenged the policy and reporting
logic with deliberate faults. The implementation did not require a live client
or another game pass to establish those properties.

The measurement took about 14.5 minutes. Implementation and local validation
took about 40 minutes, including local test and command-approval waits, against
an eight-hour bound. Its two-hour checkpoint was met at 17.4 minutes. These
figures exclude independent review and remote CI; they are not a forecast for
other structured components.

## Friction and limits

An initial comment-defect fixture placed text after the source terminator and
failed syntax before reaching its intended audit. Correcting the fixture, while
retaining the failed attempt without credit, made the evidence discriminating.
Another initial fixture omitted required rename-ledger data. An execution-sandbox
refusal of process inspection also interrupted the local suite; it was recorded
separately from product failures. These were bounded harness corrections, not
reasons to weaken the gates or broaden the feature.

Admission also made an existing usability limit measurable through the service:
four broad early-source searches required 14, 9, 11 and 20 requests against the
fixed limit of eight. Their complete results matched the independent oracle.
Correctness is established for those questions; practical access is not. The
finding belongs in the next integrated pass's dependency decision, rather than
automatically starting another search project.

## Suggested next improvement

Scope one complete, independently reviewed first semantic pass on an unfamiliar
game after explicit owner-run intake. Use the retained first-pass activity to
identify likely dependencies, then confirm them against that game's starting
state. Keep runtime claims conditional on actual evidence and include all
required artifact writes, reference access and handoffs. A static pass can be a
useful process milestone without claiming the whole fresh-game workflow is done.

The important habit to retain is measurement before commitment: identify the
smallest complete outcome, expose its missing operations, and estimate those
operations before starting the next integration.
