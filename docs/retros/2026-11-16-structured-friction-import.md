# Structured friction import retrospective

The intended outcome was to preserve both roles' process observations without
requiring the owner to copy them into the project queue. The implementation was
accepted for publication at `39737d434`; [PR #196](https://github.com/khansen/nesrev/pull/196)
is open. This records accepted offline evidence, not a merged or live result.

The service now retains every published implementer observation, accepted
rework response and reviewer verdict. Application calls the existing importer
against the target's committed queue and receipts before freezing its write set.
Intervening triage survives. The existing journal recovers interrupted work,
including a failure after commit but before its final receipt.

The [acceptance record](../structured-pass/FRICTION_IMPORT_ACCEPTANCE.md) reports
348 structured tests with one opt-in skip, 692 shell tests and 1,206 Java tests.
Five deliberately broken variants failed their matching tests. Seven retained
learning sections passed through synthetic lifecycles with byte-identical
ordinary-importer queue output. Independent review reproduced the structured
suite and relevant importer checks and accepted the change. Exact-byte testing
protects CRLF responses after inspection found normalization in the first
implementation.

Reuse kept the scope narrow: no new parser, triage mechanism, general root
writer or transaction framework. The checkpoint settled the two key decisions:
where each role submits evidence, and rebuilding against committed triage before
application rather than freezing the queue at closeout.

Effort was provisionally charged at 106 minutes against a four-hour ceiling,
including the checkpoint and excluding the overnight pause. This is a
conservative estimate, not a precise time sheet. Publication required the owner
to push because the coordinator's command policy rejects `git push`; that is
separate from agent-run permission behavior.

Review identified ambiguous no-repeat wording. Only published candidates enter
the import history, so observations on an unpublished candidate must be carried
forward. Correct that instruction before the next declaration pins. Add an
explicit multiple-sections refusal regression when changing the same code.
Neither finding calls for broader importer work.

No provider calls, live observations, autonomous triage or intervention savings
were demonstrated. The next useful step is the
[launcher and client-admission slice](../structured-pass/FG1_LAUNCHER_SLICE.md),
then the separately authorized unscripted pass. Game completion, general worker
coverage and unrelated cleanup remain outside that objective.
