---
name: lean-verify
description: Verify or repair a Lean change in this repo using the MCP server instead of full builds. Use when editing any .lean file, when a proof fails to elaborate, when hunting for a lemma or a name, or before committing.
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

Several files are enormous — `Calculus/RuleSoundness.lean` is 10,864 lines,
`Evm/Correctness.lean` 6,436, `Calculus/Coverage.lean` 4,094, `Calculus/Rules.lean` 3,486.

- `lean_file_outline` first, then `Read` with `offset`/`limit` on the one
  declaration you need.
- Never `cat` or `Read` one of those files whole.
- Broad "where is X used" questions: `rg` (it honours `.gitignore`, so it
  skips the 541 MB `.lake/`), or `lean_references`, or delegate the sweep to
  an Explore subagent so the file dumps stay out of this context.
- `docs/module-map.md` answers "which file is this in" without any search.

## Builds

| When | Run |
|---|---|
| ordinary edit inside one file | `lean_diagnostic_messages`, nothing else |
| new import or new module | `lean_build` (restarts the LSP) |
| touched `Examples/Derivations/Paper.lean` | `./scripts/check-examples.sh` (~30 min) |
| touched `SortCheck/Annotations.lean` | `lake exe solkeycheck` (already failing on 78 rows — compare against that baseline, do not try to reach zero) |
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
- `lean_verify` on the headline theorem you touched, to see its axiom set.
- Then **minimize**: collapse redundant rewrites, check whether `simp` or
  `grind` absorbs several steps, delete hypotheses `lean_minimal_hypotheses`
  says are unused. A proof that just went green is the first draft.
