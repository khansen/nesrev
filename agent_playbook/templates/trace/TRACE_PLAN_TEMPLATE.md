# <Domain> Trace Plan (<Project>)

Runtime-evidence plan for resolving the specific behavior that static analysis
cannot prove. No renames are made from this document alone.

## Background

- Static anchor:
- Unresolved question:
- Why static evidence is insufficient:
- Symbols/routines under observation:
- Capture setup:

## Watch List

| Symbol / field | Address | Reason |
|---|---:|---|
| `<state byte>` | `$0000` | transition under test |
| `<mode/context>` | `$0000` | scenario gate |
| `<score/counter/result>` | `$0000` | proves outcome |

## Scenario Gates

The analyzer must reject captures that do not prove the scenario was reached.
List the milestones or context predicates here.

- `scenario_started`:
- `input_accepted`:
- `state_under_test_active`:
- `result_resolved`:

## Target Scenarios

1. Scenario name:
   - Operator action:
   - Helper setup, if any:
   - Expected signal:
   - Promotion criteria:

2. Scenario name:
   - Operator action:
   - Helper setup, if any:
   - Expected signal:
   - Promotion criteria:

## Tooling

```sh
projects/<slug>/scripts/run_trace_fceux.sh
MOVIE=path/to/scenario.fm2 projects/<slug>/scripts/run_trace_fceux.sh
projects/<slug>/scripts/analyze_<domain>_trace.sh <raw.log> [summary.md]
```

Raw logs stay under `projects/<slug>/tmp/traces/` and are not committed.
With no explicit summary path, the analyzer writes `<raw-log>.summary.md` beside
the raw log. Merge accepted evidence manually into the curated transition
summary after capture.

Trace helper mods under `projects/<slug>/mods/` may be used to shorten or
stabilize setup, but they stay untracked unless explicitly curated. If a helper
mod changes the behavior under test instead of only the setup, the capture is
not promotion-grade evidence without corroboration.

## Status

- Harness:
- Synthetic analyzer fixture:
- Real captures:
- Confidence promotions:
