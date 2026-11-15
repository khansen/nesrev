# Typed search: offline acceptance

15 November 2026. Implementation, corpus checks and local regression validation
are complete. Independent implementation review is pending.
This is the result of the [authorized scope](TYPED_SEARCH_SCOPE.md), not
authorization for a client smoke, game pass or another service slice.

Both corridor roles now have the [typed search operation](TYPED_SEARCH.md).
Instruction queries use the existing native facts; text queries use only the
existing authored-document registry and pinned guidance. No gate, admission
mode, client sandbox, permission grant or assembler behavior changed.

## Corpus and claims

The owner approved the mature pilot corpus after current-project admission
refused the early-pass trial source. A fresh isolated copy of the pilot passed
inventory, verification, process and documentation checks, and native source
certification. Its source and reference hashes match the retained pins. The
independent oracle and service read identical admitted bytes.

The original census and [translation ledger](TYPED_SEARCH_TRANSLATIONS.csv)
are unchanged. The separate [acceptance ledger](TYPED_SEARCH_ACCEPTANCE.csv)
has exactly the same 89 call IDs. Blank measurements mean unmeasured. **No
original full call is credited as historically verified**, and all 29 original
instruction-search calls retain that status.

| Evidence | Result | Interpretation |
| --- | --- | --- |
| Instruction questions derived from all 29 instruction-bearing calls | 39 questions; all complete witness sets equal the independent oracle; 1–5 requests per question | Cross-project proxy, measured on mature code. The oracle independently joins the producer's instruction, expression, evaluation, syntax and location records in SQL. It does not invoke the new matcher. |
| Guidance questions derived from 38 calls | 39 questions; 36 equal complete independent `rg` line witnesses; three retain missing predicate arms | Service queries use the admitted proxy's policy snapshot, not substituted historical inputs. Catalogue and additional context reads are included in the 2–5 request totals. |
| Mature-code density | 26 of 39 instruction questions have zero matches; 273 witnesses across the questions | Many operands are already named. These request counts do not predict new-game throughput. |
| Direct query-code volume check on refused early-pass source | 39 questions, four above eight pages, maximum twenty; eleven zero-match questions | Unit-level evidence only. Native source certification is not full service admission. No historical or service-coverage credit. |
| Scripted cases represented by the proxy measurements | Selected subquestions from 64 of the 89 calls | This is not 64 completed original calls. Other inputs, predicates, context meanings and non-search operations remain visible in the ledger. |

The three text mismatches remain C2-001, C3-078 and C4-262. Literal/prefix
subsets omit ordered-term or heading alternatives. Their partial results are
not presented as successful translations, even where the request count fits.
The other previously deferred regex predicates and unadmitted document domains
remain deferred as recorded at the translation checkpoint.

The four unit-level page overflows are the two broad stack-context questions in
R3-067, the operand set in C4-049 and the global proxy for the scoped question
in R4-079. The latter has no corresponding cross-project source window. Neither
the eight-request threshold nor the query contract was expanded to make these
questions pass. This is concrete evidence that mature-code results understate
some early-pass result volumes.

## Correctness, integrity and controls

Native fixtures cover literal/bound/compound expressions, immediate versus
memory operands, indexed bases, indirect pointers, overlaid CPU addresses,
lexical owners, sequence matches and gaps across data/segments. Text fixtures
cover literal punctuation, alternatives, prefixes, Unicode case folding with
original positions, Q09 boundaries including `_` and `@`, dense matches and
long lines reconstructed across pages.

The checks include complete absence, a witness only on a later page, an exactly
full final page, context spanning pages, changed query/generation tokens,
successful explicit historical reads, published-artifact identities, unknown
IDs, unavailable inputs and changed source bytes. Both role declarations offer
search; search leaves the service state byte-identical. Serialized bridge
responses stay within 24 KiB, with no dropped rows. Evidence rows are generated
as needed rather than accumulating all result/context dictionaries in memory.

Five deliberately faulty in-memory implementations were each caught by the
corresponding test: dropping a later-page result, treating unknown as zero,
labeling an indexed base as a direct operand, accepting a stale token, and
exposing source through the text catalogue. Production files were not mutated
for these controls.

The admitted and synthetic producer models have integer instruction operands.
An undefined-symbol source is refused at certification. The unknown-as-zero
control tests defensive matching on an explicitly non-certified unit value;
it is not evidence of an admitted unresolved model.

## Validation and retained evidence

The private packet retains admission/profile/baseline/source/model hashes,
the query specifications and independent oracles, every response page, refusal
records, failed harness attempts, test logs and heavy-run receipts. Public
documents and fixtures contain no project identities, source excerpts or
personal paths.

Two initial test-harness errors were corrected: a temporary retention directory
that the existing guard correctly refused, and two hand-counted Unicode column
expectations. The first acceptance reduction also tried to put a 190-line policy
window into the ten-line search context field. It was refused. The corrected
reduction uses the existing guidance reader for larger windows and counts each
request. None of these failures was converted into a passing observation.

The MCP operation enum and description add `search`; the retained-only reader's
declaration is unchanged. Native client adapter code and its pinned code-mode
tool declaration are unchanged. Existing live evidence does not automatically
cover the expanded MCP interface: new profiles must pin the changed service,
and live acceptance remains separate.

| Final check | Result |
| --- | --- |
| `make test-structured-pass`, using the pinned producer and shared heavy-run lock | 307 tests, all passing; one opt-in client-version check skipped. Includes the 14 new search tests and the existing offline client tests. |
| `make test` | Strict playbook and repository hygiene checks passed; 691 shell tests and 1,206 Java tests passed. |
| Deliberate fault controls | Five of five caught by their relevant assertions, with no unrelated errors. |
| Corpus acceptance | Complete independent witness comparisons, all continuation pages, response sizes and unchanged service state recorded. |

The first full structured-suite attempt ran inside an execution sandbox that
refused `/bin/ps`, producing client-process test errors and two dependent
failures. The unrestricted offline rerun passed; both logs are retained. No
test or cleanup rule was weakened to get a passing result.

The work finished before the eight-active-hour checkpoint. Timing is recorded
as a conservatively charged working interval, including local test execution;
the earlier checkpoint's overnight authorization wait remains excluded. No
provider calls were made.

## What remains

The [early-pass admission blocker](TRIAL_WORKLOAD_COVERAGE.md#minimum-path-to-one-fresh-game-pass-through-the-service)
is unchanged. Intake, workflow jobs, worker integration and launcher delivery
remain separate dependencies. Additional input admission, regex predicates,
whole-source text scans and general computation are not supplied by search.

An authorized unscripted reviewer must still choose these routes and finish its
evidence obligations without shell fallback or missing evidence. That test needs
the launcher and the capabilities of its selected task. The reviewer's
hook-disabled protection test belongs in the next appropriate client smoke.
No such run follows automatically from these offline results.
