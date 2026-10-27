# Development and verification

Read the relevant conventions linked from [AGENTS.md](../AGENTS.md) before
editing. [module-map.md](module-map.md) locates modules;
[parallelism.md](parallelism.md) defines the import layers and module splits.

## Checks

Prefer the Lean MCP server for diagnostics, goals, hover and outlines.
After a Lean edit, check that file with `lean_diagnostic_messages`
(`interactive=false`); follow the
[lean-verify skill](../.agents/skills/lean-verify/SKILL.md).
Use a full build for import changes and final confirmation, rather than for
each proof iteration. Documentation-only edits need path and link checks.

| Command | Coverage |
|---|---|
| `./run-lean.sh` | Layer check, default targets, `SolkeyTestSuite`, then the SolKey sort check; see the checkout caveat below |
| `node scripts/check-orphans.mjs` | Every module reachable from a library root |
| `node scripts/check-layers.mjs` | No core module reaches an elaborator, printer or tactic front end; no Lean |
| `./scripts/check-doc-paths.sh` | Backticked Lean file references in tracked prose |
| `lake exe solkeycheck` | Sort annotations against SolKey's rules |
| `./scripts/check-corpus.sh` | `SolidityCorpus` against `tests/solkey/expected.tsv` |
| `./scripts/check-testsuite.sh` | TestSuite rows against `TestSuite/Report.lean`'s pin and SolKey functions; no Lean |
| `node scripts/check-automatic.mjs --strict` | Every TestSuite obligation has an automatic proof/replay or refutation, none pending; no Lean |
| `node scripts/solidity-upstream.mjs` | Pinned solc tests on the typed interpreter, per pipeline; [runner documentation](solidity-upstream-tests.md) |

Run long builds in the background and inspect the log for errors.
`run-lean.sh`'s sort-check wrapper warns and skips when the sibling SolKey
checkout is missing; a successful build alone does not establish that gate.
`lake exe solkeycheck` defaults to `../solkey`; elsewhere, pass `--key` or
set `SOLKEY_RULES` to the actual `solidityProgramRules.key` file.
The frozen inputs and re-pinning procedure live in
[solkey-migration.md](solkey-migration.md).

For rule debugging, [rule-repair.md](rule-repair.md) describes the optional
Bridge Plausible runner, its typed observations and its limited coverage.
Testing supplements the required soundness proof.

Finish each milestone with a read-only finder and skeptic review per area;
neither calls the Lean server. Fix confirmed findings and record their
resolution in that milestone's documentation.

## Toolchain and proofs

The old `SolKey` reader in `side-projects/lean/solkey` no longer builds
against this checkout. Do not edit it or retain compatibility code for it.

Run Lake from the project root. Put elan before `scripts/lean-vscode/bin` on
`PATH` so `lean-toolchain` selects the version; the latter wrappers support
the Nix-provided editor setup.

Symbolic execution needs `--tstack=131072`. It is configured in
`lakefile.toml` for builds, `.vscode/settings.json` for the editor, and
`scripts/lean-mcp/bin/lake` for MCP. The language server does not read
`weakLeanArgs`. For a scratch module, use
`lake lean --tstack=131072 Solidity/Scratch/Example.lean`.
If changing imports leaves a worker stuck elaborating, check from a fresh
scratch module importing the changed module.

Try built-in `grind` before a long manual proof; for Boolean or bitvector
goals, consider `bv_decide` / `omega`. In finished proofs, replace bare
`simp` with the lemma list from `simp?`. Give signatures and `have`s explicit
types, without annotating every subterm. Do not raise `maxHeartbeats`:
reduce proof cost with specific simplification, helper lemmas or smaller
decisions. Use the smallest passing value for a new override and lower
existing overrides when touching them.

## Tactics

1. **Search once, replay cheaply.** A searching tactic gets a `?` twin
   offering an explicit proof as `Try this` (`sol_chain?`, `sol_derive?`,
   `sol_rws?`). Keep the replay in the file so re-checking does not repeat
   the search. The kernel checks every generated line.
2. **Bound searches.** Use a node budget and per-step heartbeats
   (`withCurrHeartbeats`). Catch each timeout with `tryCatchRuntimeEx`;
   a plain `try` does not catch it. A failed step ends with a note rather
   than an error. Search depth first in a fixed order and retain the best
   leaf where greedy choices can dead-end (`Chain.pastSearchFrom`).
3. **Measure before optimising.** Use an uncommitted module in
   `Solidity/Scratch/`: time a term or tactic with `IO.monoNanosNow`, or
   profile one declaration with `trace.profiler`.
   `compilation (LCNF …)` costs come from `evalExpr`; instance specialization
   is a common cause. Mark the class `attribute [nospecialize]` where
   measurements justify it (`FreshNames`). Cache in an `EnvExtension` with
   `asyncMode := .local` so its lifetime ends with the declaration
   (`Chain.runCache`).
4. **Pin output.** Add a `#guard_msgs` suggestion example to
   `Examples/ProofTree.lean` and regressions for each broken shape.
5. **Verify.** Check one file at a time within the limits below, then run
   the milestone review.

## Worktrees and memory

For the current shared checkout, acquire the writer lock and follow the
[resource bounds](refactoring-progress.md#resource-bounds-and-resuming-work)
before edits, builds, Lean checks or generated writes. Reread Git status and
overlapping diffs after acquisition. Preserve unrelated work and other
sessions' workers.

A parallel lane uses a Git worktree on its own branch:
`git worktree add ../solidity-lean-<lane> -b <lane>`.
Lake's artifact cache is enabled in `lakefile.toml`; worktrees reuse unchanged
artifacts under `~/.elan/toolchains/<toolchain>/lake/cache`.
Edit low modules before checking their dependents to avoid repeated rebuilds.

Memory grows with open Lean files. Workers commonly hold 0.6–1.5 GB, with
`Calculus/Decide.lean` and `TestSuite/Derived*` reaching 3–4 GB. MCP may retain
eight open workers per checkout. Keep only three or four files open and run
at most two Lean agents, reduced to one during a large rebuild; current
resource guards may impose tighter limits.
After merging a lane, stop only its workers and remove its worktree.

## AGENTS cleanup review

The finder and skeptic reviews preserved canonical `save` / `find` spelling,
the macros-only notation/`rfl` check, the obsolete-reader boundary and the
priority of current resource bounds. Local links and relocated Lean file
references were checked; the repository-wide path check still has unrelated
missing references in archived records and external-source citations.
