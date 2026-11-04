# TF-handoff fixtures

The suite calls the pinned `handoff.sh` inside a disposable real Git repository; it checks the complete generated JSON, Markdown, stdout, module lists, commits, and file inventory. It does not run Lean, networking, or containers. Gate rows are fixture data and are not evidence that a real gate passed.

Cases: `partial_default` checks the default partial result; `done_passing` checks a clean current gate; `done_failed_gate`, `done_stale_head`, `done_dirty_tracked`, and `missing_gate_head` require refusal for failed, stale, dirty, or unstamped gate evidence; `notes_crlf` and `notes_unicode` check exact notes; `outside_checkout_default` checks the default location; `checkpoint_statuses` checks all three named statuses; `base_and_head` checks commits and changed/deleted modules; `malformed_status` checks invalid status rejection.

Command: `PYTHONDONTWRITEBYTECODE=1 python3 tests/terra-20261103/handoff/accept.py`. Actual result: 12 tests ran; 11 passed and `missing_gate_head` failed. The tool returned exit 0 and reported `done` with no gate HEAD. Full output: `/workspace/terra-artifact-fixtures-evidence/handoff-accept.log`. This is a failed item for Sol, not a passing gate.

Read-only finder pass by the implementer checked all named cases, full output inventory and current/stale/failing gate rows. Read-only skeptic pass checked that each test uses a fresh Git repository, that no real gate is claimed, and that the missing stamp is absent before invoking the pinned tool. Independent coordinator reviews remain pending.
