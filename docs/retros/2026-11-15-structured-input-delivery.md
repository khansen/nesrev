# Structured input delivery

[PR #195](https://github.com/khansen/nesrev/pull/195) delivered the declared
inputs needed by both roles for the first structured corridor. Preparation
captures reference text, page images, historical intake evidence, guidance and
two operator-selected analogues. Fixed-ID reads and retained captures preserve
their identities after the original input folders move. This is an offline
capability result, not a completed pass or a demonstrated reduction in cost.

The [acceptance record](../structured-pass/INPUT_DELIVERY_ACCEPTANCE.md) reports
60 byte-equal text comparisons across implementer, reviewer and restored-review
contexts. Thirty analogue question contexts used at most six navigation calls,
counting oversized-page refusals. Complete text downloads took up to ten calls;
that is disclosed separately from the eight-request search practicality limit.
Independent review reproduced the records and reran the structured suite.

The earlier decision to correct misplaced notes and stale run instructions
avoided expanding root-document access. Historical stop instructions remain in
the immutable intake archive, but that archive is delivered only on demand and
labelled historical on every page. Both assembled prompts state the current
scope and omit the archive text. Live instruction handling remains unproven.

The implementation took 4,444 seconds, about 74 minutes, against an eight-hour
bound, including local test waits. External review, owner decisions and CI waits
are separate. No provider calls or semantic passes ran. This does not calibrate
the cost of the remaining launcher or live integration work.

Review clarified that both adapters already place images in their workspace for
on-demand reads; they do not attach every page at startup. Actual media usage
and cost still need live observation. Both tool declarations changed and must
be re-pinned at launcher admission, alongside the reviewer hook-disabled test
and observation of compact-RAM decoding.

The code passed review with test gaps parked for its next change: in-repository
dot-segment traversal, committed symlinks, the fixed archive location, text and
item-count caps, assembly media/scope rechecks, and pagination one character
before EOF. These are coverage gaps in enforced rules, not reasons to expand the
next slice. Preserve them when the input implementation is next touched.

The next outcome remains one independently reviewed, unscripted pass on a fresh
input. The next proposed dependency is
[learning-candidate import](../structured-pass/FRICTION_IMPORT_SLICE.md), followed
by launcher admission and a separately authorized live pass. Neither finishing
the validation game nor implementing the full remaining service roadmap is
selected by this result.
