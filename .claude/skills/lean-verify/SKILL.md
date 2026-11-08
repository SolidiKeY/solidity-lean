---
name: lean-verify
description: Verify or repair a Lean change in this repo using the MCP server instead of full builds. Use when editing any .lean file, when a proof fails to elaborate, when checks are slow, when splitting Lean work across subagents, when hunting for a lemma or a name, or before committing.
---

# Verifying a Lean change here

No Mathlib, no dependencies; a full build costs ~24 min. Loop: edit, ask the
language server, repeat.

## Checking

- After each edit: `lean_diagnostic_messages` on that file only,
  `interactive=false`, `severity="error"`, with `start_line`/`end_line` around
  the change (a cascade on a big file returns hundreds of kB).
- Before a tactic: `lean_goal`, then `lean_multi_attempt` (no `column` is
  faster) with `grind`, `simp`, `omega`, `decide`, `rfl`, `cases h`.
  No `native_decide` under `Solidity/Calculus/`.
- Names: `lean_local_search` before guessing (Mathlib names do not exist here),
  then `lean_hover_info`. Remote search tools are disabled.
- Large files: `rg -n '^(theorem|lemma|def) ' FILE`, then a ranged `Read`.
  `lean_file_outline` on a big file is slow; never read one whole.
  `docs/module-map/` says which file holds what.

## What is slow

- **`lean_verify`** re-elaborates the whole file (minutes); it and
  `lean_run_code` share one serial slot across all agents. For axioms, append
  `#print axioms T` to the open file, read its diagnostic, delete it. For a
  type, use `lean_hover_info` or an appended `#check`.
- `lean_build` blocks every other MCP call on the project.
- Edits to `Syntax.lean`, `Semantics.lean` or `Calculus/Rules.lean` make every
  downstream check re-elaborate: finish low edits first, then move up.
- `Examples/Tactics/CrossDomain.lean`, `Examples/Tactics/Memory.lean` and
  `Calculus/Decide.lean` take about a minute: check them once, at the end.
- One declaration elaborates on one core: split a proof whose check exceeds
  ~30 s (e.g. one lemma per constructor family instead of `cases d <;> …`).
  `set_option profiler true in` shows where time goes. Develop a long proof in
  a scratch module with the same imports.

## Parallel subagents

- Same checkout: disjoint leaf files or declarations over a frozen upstream;
  nobody edits `Syntax`, `Semantics` or `Rules` meanwhile.
- Separate checkouts: one `git worktree` per lane; the Lake cache
  ([contributing](../../../docs/contributing.md#worktrees-and-memory)) supplies
  master's modules. Pass `lean_project_path` with absolute worktree paths.
- The server keeps 8 files open per project (`scripts/run-lean-mcp.sh`);
  reopening re-elaborates. A worker holds 0.6–1.5 GB (3–4 GB on
  `Calculus/Decide.lean` or `Derived*`): at most two Lean agents at once.
- Tell subagents "invoke the `lean-verify` skill first" instead of restating this.

## Builds

| When | Run |
|---|---|
| edit inside one file | `lean_diagnostic_messages` only |
| new import or module | `lean_build` |
| moved or renamed module | `./scripts/check-doc-paths.sh` |
| final confirmation | `./run-lean.sh` in the background; grep the log for `error` |

Outside the server: `scripts/coord-tools/gate.sh per-file FILE`
(`lake lean FILE -- --tstack=131072`; without the flag Lean aborts on deep
recursion). `lake env lean` sees cache-fetched modules only after
`scripts/ci/restore-lake-artifacts.py`.

## Done

- No new `sorry` or `axiom` (`rg -c sorry Solidity --stats | tail -3` against
  the baseline); `#print axioms` on the headline theorem shows nothing new.
- Minimize: merge rewrites, let `simp`/`grind` absorb steps, drop hypotheses
  `lean_minimal_hypotheses` marks unused.
