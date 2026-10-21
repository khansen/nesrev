# Friction triage — 2026-10-21

Triage only, against shared tools at `a751d3378040e342ef467f1383e99a9134a99358`.
No production fix, grant change, new gate, installation or agent session is
part of this assessment. Decisions below are recommendations, not receipt
dispositions or implementation authorization. Project observations and source
excerpts remain on the corpus branch. The
[plan](../../../PROCESS_IMPROVEMENT_PLAN.md#friction-triage-2026-10-21)
owns prioritization.

The four-project queue inventory contains nine substantive observations and
three provenance headings parsed as candidates. Two queues are empty; their
previous receipts were inspected, not reopened. An empty queue does not prove
the absence of semantic debt, platform limitations or future approval prompts.

## Findings and proposed routes

| ID | Finding and evidence | Proposed route |
|---|---|---|
| FT-1 | Unrelated staged or unstaged project edits block the handoff clean-tree guard and packet generation. Clean and unrelated-untracked controls pass. | Shared workflow design candidate, highest priority. Preserve exact-commit evidence while allowing unrelated work to remain untouched. |
| FT-2 | Two later reviews still needed user approval for ad hoc evidence inspection, despite the delivered trace/analyzer grants. One reduced a JSON receipt; another listed artifacts with a shell loop. | Repeated shared inspection gap. Evaluate a small read-only inventory/receipt interface from these actual operations, plus existing standalone reads. Do not grant arbitrary shell/Python execution to solve it. |
| FT-3 | A project-qualified handoff prompted despite a matching installed prefix. Its recovered argv matches both the project rule alone and project plus current global rules offline. | Unresolved active-policy/dispatch observation. Retain the prompt as confirmed, its cause as unknown. A bounded diagnostic is needed before changing grants. |
| FT-4 | Unqualified help has no match under the supplied scoped prefix; project-qualified help does. A separate queue-list command was escalated even though ordinary sandbox listing works. | Command usage/ergonomics. Evaluate generated help guidance and sandbox-first inspection. No broad permission expansion is supported. |
| FT-5 | A reported intermittent Python failure was a malformed submitted command: the script path and `--repo` token were missing. The successful retry restored them. | Correct the incident attribution in dated evidence. Reject the launcher-race hypothesis for this incident; no helper code fix is indicated. |
| FT-6 | Existing synthetic analyzer fixtures never enter two newer semantic contracts. Replacing both contracts with unconditional failures leaves all eight tests green. | Project-local validation debt under the existing synthetic-fixture requirement. Add meaningful cases only in separately authorized project work. No shared rule is missing merely because this check was skipped. |
| FT-7 | Policy-manifest validation accepts different nonempty scope rationales; it rejects an empty rationale. Historical xrefs independently contradicted the retained-global explanation. | Existing review miss. The manifest gate documents that it checks accounting, not truth. A future xref advisory must show incremental value and avoid equating lexical ownership with safe localization. No new hard gate is justified yet. |
| FT-8 | A source heading plus one bullet becomes two queue candidates. Indenting the source under the bullet yields one; an empty sentinel yields none. | Queue-authoring mismatch with documented heading delimiters. Preserve source attribution when reconciling metadata; do not globally discard headings, which can contain genuine observations. |

FT-2 combines two independent observations; FT-4 combines two command-usage
observations. FT-8 is derived metadata noise, not three additional operational
incidents. No observation is counted as a fix delivered by this triage.

## Reproduction and controls

Run from the shared branch checkout:

```sh
python3 -B docs/process_triage/2026-10-21/reproduce.py \
  --repo . --output /tmp/nesrev-friction-triage-results.json
```

The probe creates disposable Git repositories and stub drivers, then removes
them. It does not run FCEUX or mutate installed rules. Git, Python and standard
packet prerequisites are needed; the offline prefix checks are explicitly
skipped if `codex` is unavailable. Results are observations of current behavior,
including limitations, not a test suite claiming those limitations are fixed.

[Recorded results](results.json) include component hashes. The checked probe
uses the existing packet fixture and its fake `make`; production packet and
Git guards are unmodified. It calls `ensure_clean_tracked` directly, not the
entire `start-pass` state transition. Clean packet exit 0 here is a fixture
control, not project verification or proof of handoff completion.

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

The corpus probe separately replaces both new analyzer contracts in a temporary
copy with functions that raise. Eight existing fixtures pass with zero calls
to either contract; two direct calls confirm the replacements raise. This
does not refute the semantic conclusions, which also have independent real
capture controls. It establishes missing synthetic coverage of those paths.

The native policy probe used `codex-cli 0.163.0`. Supplying the entire
`/bin/zsh -lc ...` argv directly to `execpolicy check` yields no match for
both a simple and a multiline command, whereas their inner argv match.
This does **not** isolate a multiline parser bug: the simple-wrapper control
fails to match too. Live shell-command extraction and active configuration
must be distinguished from this offline supplied-argv test.

Codex documents literal argument-prefix matching, configuration-layer loading,
and separate handling of shell wrappers. `execpolicy check` evaluates the
rule files supplied to it; this probe is not evidence of what an earlier
session loaded. See the official
[Codex rules documentation](https://learn.chatgpt.com/docs/agent-configuration/rules).

## Boundaries for a later change

1. **Handoff:** preserve the reviewed SHA, target source and shared-tool
   identity, cache isolation, required gate results and state transitions.
   Evaluate a dependency-aware scope or tool-owned temporary export behind the
   normal handoff. Do not require the operator to manage another reviewer
   session/worktree, and do not broadly waive the clean-tree guard. Positive
   unrelated-edit cases must be paired with target/shared dirty-input and
   concurrent-change refusals. No design is selected here.
2. **Inspection:** first distinguish reads already covered from compound shell
   or arbitrary interpreter operations. A helper, if selected, must have
   bounded inputs/outputs and failure cases for malformed data and escaped
   paths. Independent reviewer analysis must remain independent of the
   implementer's conclusion; invoking an implementer-owned analyzer alone is
   not a substitute. Default-mode success needs a later live test.
3. **Qualified prompt:** preserve the exact submitted and executed command,
   rule/config hashes, launcher invocation, visible prompt and approval source.
   Test simple and multiline forms with a harmless fixture at the live boundary
   only in a separately selected diagnostic. Do not infer human approval from
   `require_escalated` alone or call elapsed command time approval latency.
4. **Existing obligations:** retain the synthetic-fixture and whole-scope xref
   review requirements. The former needs project work; the latter does not
   become automatable merely because a rationale was false. Reconcile source
   metadata without losing original candidate content or archive provenance.

## Validation limits

Reproductions ran on macOS with Python 3.15.0. No Linux run, live default-mode
agent smoke, emulator capture, full suite or new cross-project effectiveness
measurement was performed. No fix exists to mutation-test. Probe development
initially failed its cwd assertion because macOS aliases the temporary path;
the final probe resolves that fixture path physically and was rerun.

The substantive historical correction is FT-5: original tool-call text and
executed-command records agree that the failed command omitted the helper.
Subsequent reports calling it an unchanged retry are weaker
evidence. They remain preserved; the corpus triage record supplies the dated
correction rather than rewriting approved archives.

Documentation validation passed: strict playbooks (zero warnings), repository
hygiene, diff whitespace, local links/anchors and the shared added-text scan
for project slugs and personal paths. These checks validate the report, not
the proposed fixes.
