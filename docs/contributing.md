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
| `./run-lean.sh` | Layer, root and fragment checks, then the default targets, `SolkeyTestSuite` and `SoliditySlowExamples` in one Lake invocation (`--bridge` adds the Bridge gate) |
| `bash scripts/coord-tools/register.sh --check` | The generated library roots match the file tree (`register.sh` rewrites them); no Lean |
| `bash scripts/coord-tools/fragments.sh --check` | The module map, `docs/README.md`, `TERRA-TODO.md` and `scripts/g07-axiom-pins.json` match their fragment directories (`fragments.sh` rewrites them); no Lean |
| `lake build Solidity` | The library without the examples: a lane checkpoint (`scripts/coord-tools/gate.sh checkpoint`) |
| `lake build SolidityExamples SolkeyTestSuite` | The regular examples and the TestSuite: a checkpoint touching `Syntax`, `Semantics` or `Calculus` adds them |
| `node scripts/check-orphans.mjs` | Every module reachable from a library root |
| `node scripts/check-layers.mjs` | No new core import boundary beyond the pinned107 snapshot; elaborator/parser bans remain unconditional; no Lean |
| `bash scripts/coord-tools/gate.sh touched` | Merge pre-gate: check layers first on the prospective merged tree, then build touched modules; fail before build on new boundary edges |
| `./scripts/check-doc-paths.sh` | Backticked Lean file references in tracked prose; five exact historical/fixture pairs carry explicit reasons, with no basename-wide exemption |
| `node scripts/check-axiom-pins.mjs` | Original axiom-policy errors plus new unrecorded pin changes; exact existing H112 drift uses a SHA256-pinned, shrink-only baseline |
| `solidity-lean rules check --key FILE` | Sort annotations against a SolKey rules file; manual, not part of any gate (H89) |
| `./scripts/check-corpus.sh` | `SolidityCorpus` against `tests/solkey/expected.tsv` |
| `./scripts/check-testsuite.sh` | TestSuite rows against `TestSuite/Report.lean`'s pin and SolKey functions; no Lean |
| `node scripts/check-automatic.mjs --strict` | Every TestSuite obligation has an automatic proof/replay or refutation, none pending; no Lean |
| `node scripts/solidity-upstream.mjs` | Pinned solc tests on the typed interpreter, per pipeline; [runner documentation](solidity-upstream-tests.md) |

H112 records the existing unrecorded pin drift separately from the actual axiom
inventory. The refreshed source snapshot has **99 changes**, not the older
approximate 4,500: zero policy errors were present when it was captured.
`scripts/g07-unrecorded-baseline.json` is immutable, SHA256
`4d98b1810853c54992feb064f1a7b028e23d8212fd2aad8b8b65e81895d7c701`
(also in `scripts/g07-unrecorded-baseline.sha256`). Reproduce its exact bytes from
its pinned Git source with
`python3 -B scripts/h62/item5/statement-graph/reproduce_pin_drift.py`.
The active subset, `scripts/g07-unrecorded-allowlist.json`, may only shrink.
Entries bind the file, printed declaration, change kind, recorded axiom set and
observed axiom set; another file or changed axiom set is new drift. History checks
reject re-additions, deletion/recreation, and merge resurrection. Full ordinary
Git history is required; shallow/grafted or custom history is refused. The CI
`checks` job fetches full history and runs both gates and their regression controls;
the Lean build/audit jobs are unchanged.

This baseline never permits a non-standard axiom, axiom-set growth, a missing
recorded pin, a malformed print or a target/name mismatch. Those remain errors
even when a pin otherwise matches a baseline identity. It does not prove that
source print annotations match the kernel; Lean's unchanged guarded prints do
that during builds. The baseline does not update actual pin fragments or their
combined inventory. Use the existing reviewed `--write`/fragment workflow when
recording drift and remove resolved exceptions from the active subset; never
regenerate the immutable snapshot from today's new failures.

The documentation check's five historical exceptions are exact source/reference
pairs in `scripts/check-doc-paths.sh`, each with its reason. They cover unadopted
proposed module destinations, an off-git failed experiment and a synthetic
negative fixture, not claims that these files exist. A different source citing
the same nonexistent file, or a new missing reference in an exempt source, still
fails. Ambiguous existing references retain the separate `--strict` behavior.

Most examples remain in the default `SolidityExamples` library. H109 moves
three expensive examples and the eleven importers of `DecisionGaps` to the
non-default `SoliditySlowExamples` library; see [parallelism.md](parallelism.md)
for the full list. A checkpoint does not build the slow library. CI and
`./run-lean.sh` (`gate.sh full`) build it explicitly. A checkpoint touching
`Syntax`, `Semantics` or `Calculus` adds the regular examples and TestSuite.
Otherwise it checks the edited regular example and TestSuite modules with their
importers; executables wait for the final full gate. Integration includes the
slow examples.

Run long builds in the background and inspect the log for errors.
The SolKey sort check is no longer a gate (H89, 2026-11-06); the
`solkeycheck` executable is built on demand by `solidity-lean rules check`
([cli.md](cli.md)). The frozen inputs and re-pinning procedure live in
[solkey-migration.md](solkey-migration.md).

### Build cache and CI

Master's Lake build products are published as the `lake-cache` GitHub
release (`master-cache.tar.gz` and its `.sha256`), refreshed after each
merge. After cloning or merging master, run
`bash scripts/ci/fetch-lake-cache.sh` from the repository root: it installs
the pack into Lake's own artifact cache, so every module whose inputs match
master is fetched instead of compiled (a failed download only means a cold
build). Lake serves fetched modules from its cache rather than
`.lake/build`; tools that read `.lake/build` directly, such as
`lake env lean`, first need `python3 scripts/ci/restore-lake-artifacts.py`.
`scripts/coord-tools/gate.sh per-file FILE` uses `lake lean FILE` and needs
no restore step.

CI (`.github/workflows/lean.yml`) runs parallel jobs: `checks` (no Lean),
`editor-parity` (non-blocking for now), `library` (build plus the axiom and
trust audits), `testsuite` (TestSuite build, replay timing, automation gate),
`tools` (regression suites, real-backend editor tests, CLI), `editor` and
`bridge`. The Lean jobs seed the cache first. Runs on master are not
cancelled by later pushes; branch and pull-request runs are.

For rule debugging, [rule-repair.md](rule-repair.md) describes the optional
Bridge Plausible runner, its typed observations and its limited coverage.
Testing supplements the required soundness proof.

Finish each milestone with a read-only finder and skeptic review per area;
neither calls the Lean server. Fix confirmed findings and record their
resolution in that milestone's documentation.

See also the [build-speed audit](audits/build-speed.md) (2026-11-06) for measured per-module time and memory.

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
`scripts/coord-tools/gate.sh per-file Solidity/Scratch/Example.lean`
(`lake lean FILE -- --tstack=131072`).
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
