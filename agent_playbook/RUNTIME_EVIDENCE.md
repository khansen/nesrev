# Active runtime evidence

An open runtime deferral is a claim about missing live evidence, not a completed
semantic result. Every open `kind=runtime` deferral and `runtime_gated` blob/family
requires an active question in
`docs/reverse_engineering/inventory/runtime_evidence.json`. Historical review
snapshots remain unchanged. Inputs with no runtime debt need no manifest.

## Required relationships

- `subject` matches an open runtime row in `inventory/deferrals.csv`. Repeated
  pass rows may share one stable subject. Closed/static rows cannot support it.
- `question` states the concrete missing observation; the linked trace plan
  must contain that question, ignoring whitespace wrapping.
- `blobs` contains exact labels/patterns from current `runtime_gated` inventory
  rows, or is empty for a runtime question unrelated to a blob. Every runtime
  blob must be covered and its artifact field must link the associated plan.
- `families` likewise lists exact runtime-marked families from
  `inventory/data_format_targets.csv`, or is empty. Every runtime family must
  be covered and link the associated plan, independently of blob coverage.
- `trace_plan`, `runner`, `analyzer`, and all fixtures are tracked files inside
  the owning project. Paths in the manifest are project-relative. The manifest
  itself must also be tracked; stage new artifacts before validation.
  Optional Markdown fragments must resolve to explicit HTML ids or plain ATX
  headings outside fenced examples; use an explicit id for complex headings.
- `required_signals` names the scenario milestones/observations the analyzer
  requires. Acceptance and missing-signal refusal fixtures cover the complete
  declared set, with one isolated refusal per signal (other required signals
  present). Extra combined-missing cases do not replace these controls.
  Refusal includes an expected nonzero exit and specific diagnostic
  so an unrelated script failure cannot masquerade as accepted negative evidence.

These checks bind the active evidence set and execute the declared analyzer
tests. They do not prove that prose is true, that each synthetic fixture omits
exactly the declared signals, or that the runner's watches emit those signals
on the actual emulator. Independent review must inspect that producer/consumer
contract and mutation sensitivity. A passing fixture is not a real capture.

## Schema and example

Schema version 1 has a `questions` array. Each question supplies the fields
below. The synthetic example assumes its plan states the same question and
its analyzer accepts the named output path followed by input paths.

```json
{
  "schema_version": 1,
  "questions": [
    {
      "subject": "DemoRecordSelection",
      "question": "Which record is selected after the scenario starts?",
      "trace_plan": "docs/reverse_engineering/SELECTION_TRACE_PLAN.md",
      "runner": "scripts/run_selection_trace.sh",
      "analyzer": "scripts/analyze_selection_trace.py",
      "blobs": ["SelectionRecords"],
      "families": ["behavior_state_movement_animation"],
      "required_signals": ["scenario_started", "record_selected"],
      "analyzer_command": ["python3", "{analyzer}", "{output}", "{fixtures}"],
      "checks": [
        {
          "name": "complete",
          "expect": "accept",
          "expected_exit": 0,
          "fixtures": ["tools/trace/fixtures/complete.json"],
          "missing_signals": [],
          "diagnostics": ["accepted scenario"]
        },
        {
          "name": "missing_start",
          "expect": "refuse",
          "expected_exit": 1,
          "fixtures": ["tools/trace/fixtures/missing_start.json"],
          "missing_signals": ["scenario_started"],
          "diagnostics": ["missing scenario_started"]
        },
        {
          "name": "missing_selection",
          "expect": "refuse",
          "expected_exit": 1,
          "fixtures": ["tools/trace/fixtures/missing_selection.json"],
          "missing_signals": ["record_selected"],
          "diagnostics": ["missing record_selected"]
        }
      ]
    }
  ]
}
```

Commands are argument arrays, never shell strings. Execute the tracked analyzer
directly or through `python3`, `bash`, or `sh`. `{fixtures}` expands to absolute
fixture paths; `{analyzer}` names the tracked analyzer; `{output}` is a fresh
temporary output path. All three are required. The working directory is
temporary and each case has a 30-second timeout. The analyzer must honor the
output path and never overwrite fixtures or curated summaries. This executes
trusted project-owned code, not an untrusted-code sandbox. No capture runner,
emulator, ROM, movie, or network download is invoked by the fixture checks.

Acceptance requires exit 0. Refusal requires a declared exit from 1 through 125;
signals/timeouts/missing executables are failures, not successful refusals.
Every case names literal diagnostics expected in stdout/stderr or the freshly
created `{output}` summary; prior cases cannot supply the evidence.
Check names and required-signal names are unique within each question.

## Validation and migration

The blob-disposition checker reconciles this manifest automatically:

- Process mode validates membership, tracked artifacts, command shape and
  fixture coverage. Its output explicitly says fixtures were not run.
- Maturity mode performs the same checks and executes every fixture; output
  reports each actual exit. Failure blocks maturity, not just an advisory KPI.

For a focused executable check:

```sh
python3 scripts/runtime_evidence_check.py \
  --doc-root projects/demo/docs/reverse_engineering \
  --blobs projects/demo/docs/reverse_engineering/inventory/data_blob_dispositions.csv
```

Before activation, reconcile existing runtime classifications with the actual
evidence. Reuse an existing supported trace plan/runner/analyzer and fixtures
where possible; do not invent a capture, a semantic result, or a broad static
deferral merely to avoid the new check. A valid executable plan may remain
capture-pending. WIP inputs with genuinely missing evidence remain failing;
report that scope explicitly. Keep project-specific migrations off shared
branches and do not rewrite archived reviews.

When a question is genuinely resolved, update its active deferral/blob
dispositions and remove its active manifest entry together. The manifest is
not a second history ledger; provenance stays in the existing pass/trace
artifacts. Confidence promotion still follows the established runtime workflow.
