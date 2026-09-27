---
name: lean-verify
description: Verify or repair a Lean change in this repo using the MCP server instead of full builds. Use when editing any .lean file, when a proof fails to elaborate, when checks are slow, when splitting Lean work across subagents, when hunting for a lemma or a name, or before committing.
---

# Verifying a Lean change here

This package has **no Mathlib and no external dependencies**, and its default
build costs ~24 minutes of CPU. So the loop is: edit, ask the language server,
repeat. A full build is for import changes and final confirmation, not for
iteration.

## After every edit

`lean_diagnostic_messages` on **that file only**, `interactive=false`. Fix in
this order and re-check between fixes:

1. syntax errors
2. type errors
3. unsolved goals / tactic failures
4. linter warnings

"Unsolved goals" is reported at the `by` or `=>` line, not where the missing
tactic belongs — so fix downstream errors first; they often explain it.

## Writing a proof

**One tactic at a time.** Do not batch five tactics and then look. Before
writing a tactic, call `lean_goal` at the line to see the state, then
`lean_multi_attempt` with three to five candidates. Good first candidates in
this repo: `grind`, `simp`, `omega`, `decide`, `rfl`, `native_decide`,
`cases h`. `lean_multi_attempt` without a `column` is faster.

`sorry` is legitimate scaffolding. Prove the main statement first with helper
lemmas left as `sorry` (a `sorry` is an axiom, so the main proof still
checks), then discharge them. Within one proof, `sorry` the easy cases and do
the hardest case first — it is the one that tells you whether the statement is
right.

Use `done` when you expect more steps: it makes the remaining goals visible.

When a rewrite fails with "motive is not type correct", generalize first and
instantiate with `convert`.

## Finding names

`lean_local_search` **before** guessing a name — there is no Mathlib here, so
a plausible Mathlib name is almost certainly absent. Then `lean_hover_info`
(column at the start of the identifier) instead of opening the file it comes
from, and `lean_declaration_file` when you need the surrounding slice.

The remote search tools (LeanSearch, Loogle, Lean Finder, state search,
hammer) are **disabled** in this project's MCP configuration: they only know
Mathlib.

## Reading files

Several files are large — `Calculus/RuleSyntax.lean` is 1,553 lines,
`Syntax.lean` 1,436, `Calculus/KeyTaclets.lean` 1,348, `Semantics.lean` 1,283.

- `rg -n '^(theorem|lemma|def) ' <file>` first (instant), then `Read` with
  `offset`/`limit` on the one declaration you need. `lean_file_outline` on a
  big file takes minutes and overflows the result limit.
- Never `cat` or `Read` one of those files whole.
- Broad "where is X used" questions: `rg` (it honours `.gitignore`, so it
  skips the 541 MB `.lake/`), or `lean_references`, or delegate the sweep to
  an Explore subagent so the file dumps stay out of this context.
- `docs/module-map.md` answers "which file is this in" without any search.

## Speed

Most of a slow session is model round trips and a few slow files, not Lean in
general. The build cache works: an unchanged file re-checks in 1–4 s.

- **Batch edits.** One multi-hunk `Edit` or script beats ten `sed` one-liners;
  every tool call is a model round trip.
- **Know the slow checks.** `Calculus/Uniqueness.lean` ~150 s,
  `Examples/CrossDomain.lean` and `Examples/Memory.lean` ~75–90 s,
  `Calculus/Termination.lean` and `Calculus/SoundUnfold.lean` ~25–60 s,
  `Calculus/Decide.lean` ~60 s. Check them once, at the end of a change, not
  after every edit elsewhere.
- **Low edits are expensive.** After touching `Syntax.lean`, `Semantics.lean`
  or `Calculus/Rules.lean`, the next check of any downstream file re-elaborates
  the whole chain. Finish the low-level edits first, then move up.
- **One declaration is one core.** Lean elaborates separate theorems in
  parallel, but a single proof runs serially. A `cases d <;> …` over hundreds
  of constructors (`Taclet.eq_step`) should be one lemma per constructor (or
  per family) that the main theorem dispatches to. The check then gets
  parallel, and a new rule only elaborates its own lemma. Split a proof when
  its check exceeds ~30 s. `set_option profiler true in` shows where the time
  goes.
- **Scratch file for a long proof.** Develop it in a scratch module with the
  same imports, so each check re-runs one proof, not the file below it. Move
  it back and check the real file once.
- **Stay on the open file.** An open file re-checks from the first changed
  line down, in seconds. Anything that makes the server elaborate a file
  from the top is expensive:
  - **`lean_verify` is a full re-elaboration.** It copies the whole file
    into a scratch document plus `#print axioms`: 2–5 min on a large file,
    often timing out at 300 s. One agent spent 52 min on 13 of them. Instead
    append `#print axioms T` at the end of the file, read
    `lean_diagnostic_messages` with `start_line` at that line, then delete
    it. Do this once, at the end.
  - **`lean_run_code` and `lean_verify` share one serial slot** across every
    agent on the MCP server. A `#check @Int.foo` behind someone's
    `lean_verify` waited 224–300 s. To see a name's type, use
    `lean_local_search`/`lean_hover_info`, or append a `#check` to the open
    file.
  - **Filter diagnostics.** `severity="error"` and `start_line`/`end_line`
    around the part you changed. A cascade on a big file returned 208k chars.
  - `lean_build` blocks every other MCP call on the project until it finishes.

## Parallel subagents

Parallel proving works; a shared working tree is what breaks it. One agent's
edit to a low module invalidates every other agent's checks.

- **Same checkout:** give each subagent disjoint *leaf* files or
  declarations (`sorry` lemmas split out first), over a frozen upstream.
  Nobody edits `Syntax`, `Semantics` or `Rules` while they run.
- **Separate copies:** `/home` is btrfs, so
  `cp -r --reflink=always . /tmp/wt-N` copies the repo *with* its `.lake`
  instantly and without extra space. The MCP server starts one Lean server per
  project root (up to 8) when given absolute paths into the copy. Merge the
  results back by hand or with `git diff | git apply`.
- The MCP server keeps at most `LEAN_LSP_MAX_OPEN_FILES` files open per
  project (`scripts/run-lean-mcp.sh` sets 8), and closes the oldest beyond
  that. Reopening is a full re-elaboration. With several agents on one
  server, each should keep to one or two files. A worker holds 1.5–4.5 GB, and
  the machine has 64 GB.
- A subagent prompt should say "invoke the `lean-verify` skill first" rather
  than restate these rules.

## Builds

| When | Run |
|---|---|
| ordinary edit inside one file | `lean_diagnostic_messages`, nothing else |
| new import or new module | `lean_build` (restarts the LSP) |
| touched `SortCheck/Annotations.lean` | `lake exe solkeycheck` (must stay at zero) |
| moved or renamed a module | `./scripts/check-doc-paths.sh` (seconds) — the prose cites modules by path, and a docstring naming a file that no longer exists is worse than the move |
| final confirmation | `./run-lean.sh` (~24 min) |

Run the long ones with `run_in_background`, then `grep -n "error"` the log.
Do not read a build log back in full.

Checking a single file outside a target — `lake env lean <file>` — needs
`--tstack=131072`. The lakefile sets it per `lean_lib`, so a bare `lake env
lean` aborts the process on "deep recursion" rather than reporting an error,
and the failure looks nothing like the missing flag.

## Before you call it done

- No new `sorry` and no new `axiom`. Check against the baseline:
  `rg -c 'sorry' Solidity --stats | tail -3`. The existing ones are documented
  at their site and listed in `docs/module-map.md`.
- The axiom set of the headline theorem you touched: `#print axioms T`
  appended to its file, as in Speed above, not `lean_verify`.
- Then **minimize**: collapse redundant rewrites, check whether `simp` or
  `grind` absorbs several steps, delete hypotheses `lean_minimal_hypotheses`
  says are unused. A proof that just went green is the first draft.
