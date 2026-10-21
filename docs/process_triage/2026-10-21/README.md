# Friction triage — 2026-10-21

Triage only, against shared tools at `a751d3378040e342ef467f1383e99a9134a99358`.
No production fix, grant change, new gate, installation or agent session is
part of this assessment. Project observations and source excerpts remain on
the corpus branch. The
[plan](../../../PROCESS_IMPROVEMENT_PLAN.md#friction-triage-2026-10-21)
owns proposed routes, priorities and boundaries; none authorizes implementation
or applies a receipt disposition.

This dated package lives under `docs/process_triage/` because it covers several
components rather than one tool. It preserves historical diagnostics, not a
maintained test suite or a new CI entry point.

The four-project queue inventory contains nine substantive observations and
three provenance headings parsed as candidates. Two queues are empty; their
previous receipts were inspected, not reopened. An empty queue does not prove
the absence of semantic debt, platform limitations or future approval prompts.

## Findings and evidence

| ID | Finding and evidence |
|---|---|
| FT-1 | Unrelated staged or unstaged project edits block the handoff clean-tree guard and packet generation. Clean and unrelated-untracked controls pass. |
| FT-2 | Two later reviews needed human-confirmed approval for ad hoc receipt reduction or artifact listing, despite the delivered trace/analyzer grants. These are confirmed historical interventions, not new live reproductions. |
| FT-3 | A project-qualified handoff prompted despite a matching installed prefix. Its recovered argv matches both the project rule alone and project plus current global rules offline. The historical active policy and live parser remain unknown. |
| FT-4 | Unqualified help has no match under the supplied scoped prefix; project-qualified help does. A separate queue-list command was escalated even though ordinary sandbox listing works. |
| FT-5 | A reported intermittent Python failure was a malformed submitted command: the script path and `--repo` token were missing. The successful retry restored them. No intermittent launcher defect is demonstrated by this incident. |
| FT-6 | Existing synthetic analyzer fixtures never enter two newer semantic contracts. Replacing both contracts with unconditional failures leaves all eight tests green. This establishes missing path coverage, not the absence of any analyzer fixture. |
| FT-7 | Policy-manifest validation accepts different nonempty scope rationales; it rejects an empty rationale. Historical xrefs independently contradicted the retained-global explanation. The manifest gate checks accounting, not semantic truth. |
| FT-8 | A source heading plus one bullet becomes two queue candidates. Indenting the source under the bullet yields one; an empty sentinel yields none. Heading delimiters are documented behavior. |

FT-2 combines two independent observations; FT-4 combines two command-usage
observations. FT-8 is derived metadata noise, not three additional operational
incidents. No observation is counted as a fix delivered by this triage.

## Reproduction and controls

For a historical rerun, use the approved checkout at
`5808d4a61626fea14d5de1eec7cb06b2893f252c`; its tool inputs are unchanged from
the recorded baseline above:

```sh
python3 -B docs/process_triage/2026-10-21/reproduce.py \
  --repo . --output /tmp/nesrev-friction-triage-results.json
```

This diagnostic relies on private implementation interfaces and shell-test
helpers, including `ensure_clean_tracked`, `queue_candidates`, the positional
`Marker` constructor and `check_manifest`. It is not maintained or run by CI
or `make test`. A later-master rerun may fail or measure different behavior
without exposing a regression.

[Recorded results](results.json) are the historical record; write reruns
elsewhere. `tool_head` is the checkout's HEAD, not a digest of the tools. It
identifies the full committed tree supplying the probe's dependencies.
`input_sha256` covers five selected files, including only two of the ten
scripts copied for the packet fixture. Matching these hashes is necessary
for a comparable rerun but insufficient if other dependencies changed. A
later documentation-only HEAD can differ while all tool inputs stay identical;
compare the full dependency tree as well as the selected hashes.

The probe creates disposable Git repositories and stub drivers, then removes
them. It does not run FCEUX or mutate installed rules. Git, Python and standard
packet prerequisites are needed; offline prefix checks are explicitly skipped
if `codex` is unavailable. The existing packet fixture uses fake `make`;
production packet and Git guards are unmodified. It calls
`ensure_clean_tracked` directly, not entire handoff state transitions. Clean
packet exit 0 here is a fixture control, not project verification or proof of
handoff completion.

| Probe | Observed result | What it does not establish |
|---|---|---|
| Clean tracked state; unrelated untracked file | Handoff guard accepts; packet exits 0 in both cases | Real quality gates or private fixture availability |
| Other-project tracked edit, staged and unstaged | Handoff guard refuses; packet exits 2 at stale-evidence guard | A safe replacement scoping rule |
| Selected-project edit; shared-tool edit | Same refusal | That ignoring all paths outside the selected project would be safe |
| Heading metadata; indented metadata; empty sentinel | 2, 1, 0 candidates | That all heading-only candidates are noise |
| Two different nonempty rationales; empty rationale | 0, 0, 1 manifest errors | Either nonempty rationale's semantic truth; this is a component probe |
| Python given a directory as its program | Exit 1 and missing-`__main__` error | A defect in the helper, which was not invoked |
| Valid helper dispatch to stub tools | 10 trace and 10 analysis runs preserve cwd/arguments | Real emulator or escalation behavior |
| Scoped help and multiline handoff argv | `allow` under the supplied rule; unqualified/other-project help have no match | Historical loaded-policy state or whether a user saw a prompt |

The original corpus probe separately replaced both new analyzer contracts in
a temporary copy with functions that raise. Eight existing fixtures passed
with zero calls to either contract; two direct calls confirmed the replacements
raised. External review additionally confirmed that `analyze()` reaches each
patched contract when its scenario is selected. These are routing controls,
not synthetic semantic tests of those contracts. Independent real-capture
controls still support the semantic conclusions; synthetic path coverage
remains debt.

The native policy probe used `codex-cli 0.163.0`. Supplying the entire
`/bin/zsh -lc ...` argv directly to `execpolicy check` yields no match for
both a simple and a multiline command, whereas their inner argv match.
External review additionally confirmed the lack of offline wrapper splitting
using bare `bash`, `zsh` and `sh` with plain single-line scripts. The package's
recorded wrapper rows cover only `/bin/zsh`. Together these establish a checker
limitation, not how the live parser handles wrappers or multiline quoting.

The documented live parser splits simple shell commands; complex syntax such
as redirection or substitution is evaluated as a whole invocation. Project-local
rules load only from a trusted configuration layer. The historical learning
argument is 29 single-quoted lines containing backticks; its live classification
remains to be tested, not inferred from these offline results. See the official
[Codex rules documentation](https://learn.chatgpt.com/docs/agent-configuration/rules).

## Validation limits

Reproductions ran on macOS with Python 3.15.0. No Linux run, live default-mode
agent smoke, emulator capture, full suite or new cross-project effectiveness
measurement was performed. No fix exists to mutation-test.

The substantive historical correction is FT-5: original tool-call text and
executed-command records agree that the failed command omitted the helper.
Subsequent reports calling it an unchanged retry are weaker evidence. They
remain preserved; the corpus triage record supplies the dated correction
rather than rewriting approved archives.
