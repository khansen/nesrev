# Structured RAM closure

The milestone was complete RAM evidence and authored judgments for one first
structured pass on an unfamiliar input. [PR #193](https://github.com/khansen/nesrev/pull/193)
delivered the judgment writer; [PR #194](https://github.com/khansen/nesrev/pull/194)
delivered compact reads. Both are merged. This establishes offline capabilities,
not completion of that pass or a live cost saving.

The writer preserves address identity and generated facts while carrying authored
status, proposed name and notes through validation, retained review and application.
Independent review found a missing control-character refusal test; nine cases now
protect the existing guard. The original compaction experiment stopped at eight
and nine requests. Keeping the writer independently deliverable avoided coupling
its acceptance to that transport problem.

The separately authorized follow-up factored repeated field values and shared
only address-independent unknown destinations. Both measured questions now take
eight requests cold, with every legacy fact retained. Two bytes outside zero
page take five. These are one game's service measurements; correct decoding and
route choice by unscripted agents remain open. Both client tool declarations
changed and need fresh pins at launcher admission.

Recorded working intervals were about 32 minutes for the writer slice and 21
for compaction, including local test waits. Review, owner decisions and CI/merge
waits are separate and are not a calibrated engineering forecast. No provider
calls were made. The detailed [writer](../structured-pass/RAM_JUDGMENT_SLICE.md)
and [read acceptance](../structured-pass/RAM_COMPACT_FOLLOWUP.md) retain failures,
controls, evidence limits and private packet identifiers.

The next-slice review corrected an incorrect dependency diagnosis. A refused
root-document request did not establish that root access was needed: the notes
were misplaced, and temporary run instructions had been stored in durable docs.
The existing canonical notes path is already supported. Before expanding an
interface, check the requested artifact against its documented location and role.
The [revised input-delivery scope](../structured-pass/INPUT_DELIVERY_SLICE.md)
therefore proposes a small intake correction and retains the current root boundary.

The next outcome remains one complete, independently reviewed structured pass.
Input delivery, learning-candidate import and the launcher are the remaining
selected dependencies; this retrospective does not authorize them.
