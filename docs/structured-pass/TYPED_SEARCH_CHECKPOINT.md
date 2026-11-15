# Typed search: first translation checkpoint

**15 November 2026 — decision before service implementation.** The owner
authorized the [offline scope](TYPED_SEARCH_SCOPE.md), including this checkpoint
within two active hours. All 89 retained search-bearing calls have been read and
translated. No search route, client, permission or admission code has changed.

**Recommendation:** continue with the approved native-instruction and
literal-text contracts, retaining the unsupported predicates below as explicit
gaps. Do not add a regex engine or broader input admission to make the census
look complete. The owner makes the go/no-go decision at this checkpoint.

This slice advances reusable inspection without client-specific shell rules.
It still needs the launcher for live use; it does not supply workflow jobs,
worker integration or fresh-game intake.

## What the translation establishes

The [translation ledger](TYPED_SEARCH_TRANSLATIONS.csv) has one row for each of
the original 89 call IDs: 60 implementer and 29 reviewer. It records the questions,
candidate routes, required input families, expected witnesses or absence claims,
request sequence, other capability gaps and evidence limits. Exact arguments,
operands, input identities and retained results remain in the private record.
The [original census](TRIAL_WORKLOAD_COVERAGE.csv) is unchanged.

| Search input categories | Calls | Meaning |
| --- | ---: | --- |
| All requested locations have an in-scope source/document category | 34 | Current source or default authored-document/guidance candidates. This is not verified admission, predicate coverage or successful search. |
| Only a subset falls within those categories | 44 | The remainder includes extra guidance, scripts, peer projects, reference text, mixed/generated artifacts or protected history. |
| No search input falls within those categories | 11 | Deferred under this slice. A matcher test on synthetic text cannot turn these into covered historical calls. |
| Total | 89 | Mixed calls retain their non-search needs. |

An optional authored document is not assumed registered just because the current
registry mechanism could accept it. Broad directory searches do not silently
shrink to the default document set. The ledger distinguishes those input limits
from predicate limits and unverified historical snapshots.

The ledger uses these evidence/sequence codes to avoid repeating the same
contract in every row. `I`: query native predicates and exhaust pages/context,
returning record IDs, owners, locations, final modes and evaluated value/status.
`T`: select admitted document identities (catalogue if needed), exhaust text
pages, and return hashes, line/position/term witnesses and requested context.
`G`: read the pinned guidance window at the returned location. `E`: reuse the
specific existing symbol/RAM/identifier/data/evidence route named in the row,
counting its requests too. `Z`: only a complete selection may establish absence;
unresolved, unsupported and unavailable remain distinct. `DEFER`: retain the
unadmitted input or unsupported predicate, without opening or substituting it.
`other_capability_gaps` retains the original census codes, defined in the
[coverage assessment](TRIAL_WORKLOAD_COVERAGE.md). Empty measured-request fields
mean unmeasured, not zero.

## Predicate decisions exposed by the workload

The native facts support mnemonic/mode selection, literal versus bound operands,
integer sets/ranges, and short instruction sequences without an assembler change.
Three qualifications matter:

- A broad assembly grep can match directives, constants and comments. Returning
  matching instructions answers the operand question, not the entire textual
  request. Such rows remain partial until their independently stated question is
  satisfied; there is no assembly-text search fallback.
- R3-068 used adjacent physical source lines for two short sequences. The proposed
  route uses consecutive native instructions and byte continuity. Labels or
  comments between instructions can make those sets differ. Record and test the
  distinction; do not call a semantic replacement an exact replay.
- C3-022 also searches a pointer-table value. An instruction query cannot cover
  that arm. An existing bounded data selection must be demonstrated or that need
  stays deferred.

Eight calls contain text predicates not fully expressible by the initial
literal/any-of/whole-token/prefix contract:

| Predicate | Call IDs | Disposition |
| --- | --- | --- |
| Ordered terms on one line | C3-078, C4-262, R4-029 | Defer the unsupported arm. Do not return a broad single-term match as equivalent. |
| Exactly one arbitrary character between terms | C4-011, C4-146, R4-033, R4-107 | Defer that arm; a guessed space or hyphen is not an equivalent predicate. |
| Numbered-heading pattern | R3-074 | Both the predicate and reference input are outside this slice. |

These are overlapping limitations of calls already in the input-domain table,
not eight additional calls. Literal alternatives within the same request can
still be useful; the complete request is not thereby covered. A later bounded
ordered-literal predicate is a possible extension, but is not selected here.

## Independent guidance comparison

The comparison used complete `rg` results on pinned guidance copies, with output
limits removed, as the oracle. A separate literal/prefix selector was compared
against its matched-line identities. Neither code path is a service route.

- 39 guidance questions from 38 calls were checked; C3-078 contains two.
- 36 candidate selectors returned the same complete line sets.
- Three selectors missed lines: C2-001 missed one heading, C3-078 one ordered-term
  match, and C4-262 two ordered-term matches. None returned extra lines.
- Across these question/input pairs, the oracle found 1,108 matching lines;
  the largest question had 153. Repeated searches of a line count separately.

C2-001 asks to read the handoff section. Its anchor plus an existing guidance
window can deliver that section: on the pinned input the old context union is
lines 131–333, within the existing 400-line guidance limit. This is a candidate
two-route translation, not equality of the anchor-only matched-line set. Its
actual wire size and request count still need service acceptance.

R4-029's unsupported ordered arm adds no unique match on the pinned guidance;
it nevertheless remains unsupported. Accidental equality on one document does
not establish a general predicate. Likewise, treating a regex dot as literal
punctuation is only credited for a pinned comparison that actually agrees.

These results establish translation evidence for the selected guidance subset.
They do not establish full historical replay, service admission, eight-request
practicality, or reduced operator effort.

## Snapshot and admission limits

All eight transcript hashes were verified against the retained source index.
Guidance was exported at four recorded setup commits, giving 32 file/hash
records. Seven guidance files are unchanged across those commits; the tooling
guide has three versions, so each segment uses its own copy.

Eleven inspected historical commits exist. The pre-intake commit lacks the two
project admission documents checked; ten later commits pass the service's
scorecard and deferral parsing prechecks. **Full current-project admission was
not run.** Its gates and producer capture are additional requirements; passing
two parsers does not satisfy them.

Reviewer handoff heads are retained, but a recorded head alone does not prove
the working bytes of every search. Implementer searches often occurred between
edits and commits. Nearby commits must not stand in for those exact snapshots.
A retained instruction cache lacks a source-hash binding sufficient to identify
every historical request, so it has not been credited as their oracle.

The ledger therefore makes **zero fully verified historical-call claims** and
leaves actual service-request counts empty. No full admission refusal was
observed; none is invented. Subsequent acceptance must record each case as
verified, missing exact inputs, present but admission-refused (with the reason),
or still unverified. Synthetic analogues test behavior, not historical coverage.
If reconstructing snapshots becomes a separate project, stop under the agreed
bound rather than quietly substituting newer inputs.

**Real-code corpus decision (15 November):** for the ten reviewer instruction
calls, use the recorded review head only when retained evidence establishes that
the searched code stayed unchanged throughout the review window, including no
concurrent implementer edits. The reviewer's read-only role alone is not that
proof. Otherwise keep historical verification unverified. For the nineteen
implementer instruction calls, select the nearest retained committed snapshot
in the recorded work sequence that passes full current-project admission, and
label every result **proxy**. Record the chosen commit, selection reason, input
hashes and any admission refusal. Run the independent native-fact oracle and
the service queries on the same admitted snapshot; measure all requests against
the unchanged eight-request limit. Report historical verification, proxy
correctness/practicality and synthetic-fixture results separately. Proxy results
never become historical replay or erase the original unverified disposition.
Both paths require full admission without weakening any gate. Establish and pin
at least one admitted real-code snapshot before building the routes; if neither
path works within the bound, return that finding before implementation rather
than silently reducing acceptance to fixtures alone.

## Bounds selected for implementation

These are caps, not a promise that every allowed query fits eight requests.
The 24 KiB serialized response ceiling and eight-total-request practicality
limit remain unchanged. Overflow is a gap, never silent truncation.

| Dimension | Initial cap and basis |
| --- | --- |
| Instruction predicate alternatives | 8; separates the small disjunctions in the retained audits without an expression language. |
| Mnemonics / final modes per predicate | 16 each, restricted to producer-supported values; accommodates the transfer and write families and native mode enumeration. |
| Explicit integer values / inclusive ranges | 32 values and 4 ranges; the large observed address set has 20 values, and page sweeps stay range queries. |
| Consecutive instructions | 2; both retained sequence tests are pairs. Other proximity checks use bounded context, not a new graph language. |
| Instruction context | At most 10 records on either side; accommodates the retained neighboring-window requests while bounding each witness. |
| Text terms/prefixes and selected input identities | 32 each; accommodates the retained literal lists and current guidance/default-document catalogue. Unsupported patterns are not expanded into enumerations. |
| Term length | 256 Unicode code points; longer input is refused, not truncated. |
| Page size | At most 40 witnesses, possibly fewer to meet the wire limit. Context/long-line continuations also count toward the eight-request limit. |

Text positions must refer to the original text. Case-insensitive matching needs
explicit Unicode case-folding and original-position tests; whole-token matching
keeps Q09's identifier boundary. Final field names can follow existing service
conventions. No host paths or caller expressions are accepted.

## Next implementation and evidence boundary

On a go decision, implement these bounded routes and run the approved offline
acceptance. First establish source/model and document hashes for each retained
case that can be admitted; keep unavailable or refused cases visible. Compare
complete results with independent native-fact/text oracles, including no-match,
later-page, full-page, unresolved and stale-generation cases. Measure every page,
catalogue selection and context request. Preserve all 89 ledger rows even when
only a subset can be verified.

The estimate and checkpoints stay at 8–16 active hours, with the next progress
checkpoint at eight hours total and a hard ceiling at sixteen. No implementation
review round or live allowance has been consumed by this translation checkpoint.
No game pass follows automatically.

## Verification and effort record

The ledger accounts for all 89 original IDs exactly once and agrees with the
private translations and original capability codes. The original requests and
public census are unchanged. Eight retained transcript hashes and 32 exported
guidance hashes were checked. All nine relative links in the scope/checkpoint
resolve; the shared files passed the project-neutrality scan.

`check_agent_playbooks.py --strict`, `make check-repo-hygiene` and
`git diff --check` passed after the final documentation edit. No service tests
were run because no service code changed. Provider calls, assembler/emulator
runs, full project admission and heavy jobs were all zero.

Work began at 23:29:20 UTC on 14 November (15 November locally), with the final
documentation edit at 23:54:11 UTC. The corrected private record charges a
**provisional 35 active minutes**, excluding the overnight approval wait before
the commit. This is a conservative estimate, not an exact active/wait split;
the original elapsed-time charge is retained as a superseded reduction. The
record also retains the initial ledger-writer error, corrected before outputs
were produced; no observation or failed service result was replaced.
