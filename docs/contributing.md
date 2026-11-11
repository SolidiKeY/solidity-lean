# Development and verification

Source and tests define APIs; this page keeps commands and constraints.

## Checks

After a Lean edit, check that file through the Lean MCP server
([lean-verify skill](../.agents/skills/lean-verify/SKILL.md)). Full builds are
for import changes and final confirmation. Documentation-only edits need the
path, navigation and generator checks.

| Command | Coverage |
|---|---|
| `./run-lean.sh` | Layer, root and fragment checks, default targets, `SolkeyTestSuite`, `SoliditySlowExamples` (`--bridge` adds Bridge) |
| `bash scripts/coord-tools/register.sh --check` | Generated library roots match the tree (without `--check` it rewrites them) |
| `bash scripts/coord-tools/fragments.sh --check` | Module map, `docs/README.md`, `TERRA-TODO.md`, `scripts/g07-axiom-pins.json` match their fragments |
| `lake build Solidity` | Library without examples (`gate.sh checkpoint`) |
| `lake build SolidityExamples SolkeyTestSuite` | Examples and TestSuite; a checkpoint touching `Syntax`, `Semantics` or `Calculus` adds them |
| `bash scripts/coord-tools/gate.sh touched` | Merge pre-gate: layers on the merged tree, then touched modules and their library importers |
| `node scripts/check-orphans.mjs` | Every module reachable from a library root |
| `node scripts/check-layers.mjs` | No new core import boundary beyond the pinned snapshot |
| `node scripts/check-axiom-pins.mjs` | Axiom policy and unrecorded pin changes (H112 baseline shrinks only) |
| `python3 scripts/check-doc-navigation.py` | Every Markdown document reachable from `AGENTS.md` and `CLAUDE.md`; catalog current |
| `./scripts/check-doc-paths.sh` | Backticked Lean paths in prose exist |
| `./scripts/check-private-paths.sh` | No home directories in tracked files (public repo): write `~`, `$REPO` or a relative path |
| `./scripts/check-evidence-files.sh` | No lane evidence under `tests/`; archive it with `scripts/coord-tools/coord-evidence` |
| `./scripts/check-corpus.sh` | `SolidityCorpus` against `tests/solkey/expected.tsv` |
| `./scripts/check-testsuite.sh` | TestSuite rows against `TestSuite/Report.lean` |
| `node scripts/check-automatic.mjs --strict` | Every TestSuite obligation proved, replayed or refuted |
| `node scripts/solidity-upstream.mjs` | Pinned solc tests on the interpreter ([runner](solidity-upstream-tests.md)) |
| `solidity-lean rules check --key FILE` | Sort annotations against a SolKey rules file; manual (H89) |

## Before pushing

The merge pre-gate runs `gate.sh touched` on your head merged onto current `origin/master`;
it builds changed modules and their library importers ([coverage](../scripts/coord-tools/README.md)), not the full library.

1. `git fetch origin master && git merge origin/master` (or use a temporary merge worktree),
   then run `bash scripts/coord-tools/gate.sh touched` there and fix failures: heads that
   build only on an older base or only in changed files are rejected. On lanes, `coord-ask --done`
   runs this check and reports only passing heads or heads already on master. Failure, conflict or an unavailable
   check blocks reporting; use `--no-check REASON` only for failures your change did not cause
   (master broken, tool missing). The push records the checked head and any command override.
2. Changing a module with many importers (e.g. `Solidity/Source/**`) must preserve existing
   statements: add the new form beside the old as a versioned pair (H57) and move importers
   in the same head, or keep the old form until they move.
3. A new gate, baseline or audit must pass on the merged head, not only your base: compute
   ratchet baselines from the merge base or regenerate at merge; keep audits re-runnable
   from committed scripts.

Progress and status go into your result, never into shared documents.

## New modules

Register with `scripts/coord-tools/register.sh`, add the area fragment under
`docs/module-map/<area>.d/`, and run `scripts/coord-tools/fragments.sh`.

## Design and speed

- Read the relevant [audits and prior-art studies](document-index.md#guides-audits-and-performance)
  before freezing an interface.
- Before a refactor that may slow checking, say so and check Git history for a
  speed-motivated change it would undo.
- Symbolic execution needs `--tstack=131072`; use the project wrappers.
- Try `grind`, `bv_decide` or `omega` before long manual proofs. Finished proofs
  use `simp only [...]`, explicit signatures and typed `have`s.

## Tactics

Searching tactics need bounded search and a cheap replay twin. Catch runtime
timeouts with `tryCatchRuntimeEx` (`try` does not). Pin regression examples,
kernel-check generated terms, and profile before optimizing.

## Worktrees and memory

Take the writer lock and follow the
[resource bounds](refactoring-progress.md#resource-bounds-and-resuming-work).
Preserve unrelated work and other sessions' workers; after integration, remove
only your own worktree and workers.

## Build cache and CI

After fetching master, `bash scripts/ci/fetch-lake-cache.sh` installs matching
artifacts; a missing cache means a cold build, not a pass. Tools reading
`.lake/build` may need `python3 scripts/ci/restore-lake-artifacts.py`. The CI
workflow files define the job set.

## Measurements

Compare only under matched source, toolchain, workload, cache and limits, with
full denominators; timeouts count as failures. Runners: `scripts/measure-simple.mjs`,
`scripts/measure-native.mjs`, `vscode/test/measure-proof-speed.cjs`,
`scripts/testsuite-performance.mjs --native`, `web/test/performance.cjs --single --benchmark`.

## Reviews

End each milestone with independent read-only finder and skeptic reviews per
area; neither uses the Lean server. Fix confirmed findings and record their
resolution concisely.

## Documentation

Keep prose only for what code and tests cannot say: commands, non-obvious
constraints, external assumptions and open decisions. Implementation tours and
completed-work histories belong in code and Git. Link new guidance from its
topic guide, add it to Git, then run `python3 scripts/check-doc-navigation.py --write`.
