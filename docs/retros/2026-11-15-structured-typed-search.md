# Typed search: milestone retrospective

15 November 2026. [PR #187](https://github.com/khansen/nesrev/pull/187)
merged the independently accepted implementation. This account suggests
improvements; it creates no policy or authorization for another slice.

## Outcome against the purpose

The service can now answer bounded instruction queries from native assembler
facts and search registered text. This removes a measured capability gap in
the reusable process. It does not demonstrate a fresh-game workflow, lower
operator effort or live reviewer adoption. The
[acceptance record](../structured-pass/TYPED_SEARCH_ACCEPTANCE.md) separates
those limits from the offline results.

All 89 retained search-bearing calls stayed visible in the ledger. On the
admitted mature-code proxy, all 39 instruction questions matched the independent
oracle; 36 of 39 guidance questions matched, with three unsupported predicate
arms still open. No original full call was credited as historically verified.
The recorded effort was about 90 minutes, including local verification; this
is one slice's working interval, not an estimate for later integration.

## What helped and what we learned

The complete translation ledger, independent oracle and fixed response and
request limits prevented selective success claims. Synthetic dense and later-page
cases complemented real code. Review distinguished missing snapshots from
refused admission and made the corpus substitution explicit.

The mature proxy was useful for correctness but weak for fresh-game volume:
four questions on unadmitted early-stage code exceeded eight requests, reaching
20 pages. Those were unit-level measurements. They identify a future practical
limit without proving that service admission or an unscripted review works.

Corpus preparation also exposed a larger dependency: strict admission stops on
generic names. The follow-up over 11 commits checked only that naming predicate.
It did not establish that naming was their sole strict failure. Neither the
later verification checks nor process and documentation checks were measured
by that investigation. Calling admission a small wiring change would therefore
be premature.

Linux CI failed once in an unchanged adapter audit test, then passed on retry.
The failed attempt is retained and tracked in
[#188](https://github.com/khansen/nesrev/issues/188). A fixture race is suspected,
not established; the green retry does not resolve it.

## Suggested next improvement

Measure the remaining checks on retained early-stage snapshots before estimating
admission work. Keep the mode decision in the trusted service and its evidence,
with strict completion unchanged. Re-measure the four heavy queries after a
snapshot is admitted; decide any search redesign separately. This follows the
[process objective](../MANIFESTO.md) by testing the next barrier to unfamiliar
games without resuming game completion as an end in itself.
