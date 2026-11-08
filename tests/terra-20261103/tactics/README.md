# TF-tactics: reconstructed backend and cleanup fixtures

H151: the missing final runtime-fixtures delivery at
`f8975f25b12a5e9723b00ec794b261708280092c` and unavailable original captures are
**UNVERIFIABLE**. These new fixtures are a fresh reconstruction from the
authenticated original assignment, not recovery or authentication of that head.
The acceptance script remains byte-identical to the frozen contract (SHA256
`6c91f4dbd4aaffc70d78a7fbc700335857fafecc69e3b3db6aeb000f924bbb05`).

Each test invokes the real pinned `scripts/coord-tools/try-tactics.sh`, copied
byte-for-byte into a private disposable harness so its MCP sibling can be a
recording heavy-backend substitute. Git is real; Lake and MCP record all arguments,
candidate source and identities, then simulate prescribed success/failure. No Lean,
real server, network, container cleanup or host cache is used. Repositories, paths,
logs and HOME contain spaces; scratch cleanup is checked when each runner invocation returns.

The 12 exact frozen cases are:

- `usage`: missing arguments reject without invoking backends or creating scratch.
- `lake_success`: all six standard candidates pass with exact Lake arguments.
- `all_fail`: every candidate fails and the runner exits 1.
- `sorry_rejected`: exit-zero backend warnings using sorry still fail every row.
- `standard_and_custom_candidates`: preserves the full six-plus-custom order and
  individual mixed results; no successful candidate stops later attempts.
- `multiline_goal_line`: real goal-file text and exact MCP line offset are checked.
- `bridge_error_exit`: infrastructure failures produce all FAIL rows and exit 2.
- `mcp_success`: exact MCP invocation and scratch contents for all candidates.
- `mcp_scratch_cleanup`: failed MCP candidates leave no checkout scratch file.
- `lake_scratch_cleanup`: failed Lake candidates leave no source scratch directory.
- `invalid_backend`: refuses the backend with no heavy invocation or source leak.
- `auto_backend`: records one status probe and tests both MCP and Lake selection.

Common assertions enumerate every output row and log, exact candidate sequence,
source text, backend argument vector, HOME, working directory and remaining file
inventory. Forced backends must issue zero status probes; auto mode must issue
exactly one initial probe. A negative control rejects an injected extra probe. Recorded mock PASS means process/protocol success only; it proves no
tactic or theorem. Original statements, budgets and production tools are unchanged.

Run `python3 -B tests/terra-20261103/tactics/accept.py` at readiness. Its optional
commit argument checks the three-file item commit separately. Raw results, resource
records, reviews and handoff belong only in the H145 private archive. Coordinator
rerun and independent acceptance remain required; no runtime gate pass is claimed.

Fresh frozen acceptance passed all 12 cases after a skeptic finding was fixed:
forced backends now reject unexpected status probes, with a negative control.
Independent read-only finder and skeptic confirmed the fix and found no remaining
static blocker; neither reran tests or used Lean. The optional item-commit gate
and coordinator acceptance remain separate, and the full inherited queue is
unfinished. This fixture does not authenticate the lost historical correction.
