# Development and verification

Read [AGENTS.md](../AGENTS.md) and the relevant area conventions before edits.
Use `rg` and local imports to find code. Source and tests define APIs;
documentation retains commands, constraints and semantic assumptions.

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
| `python3 scripts/check-doc-navigation.py` | Every retained Markdown document reachable through local links from both agent entry points; generated catalog current |
| `./scripts/check-doc-paths.sh` | Backticked Lean file references in tracked prose; five exact historical/fixture pairs carry explicit reasons, with no basename-wide exemption |
| `./scripts/check-private-paths.sh` | No personal home directories (`/home/<user>/`, `/Users/<user>/`) in tracked files, since the repository is public; write `~`, `$XDG_STATE_HOME`, `$REPO` or a relative path. Run by CI and by every merge gate |
| `./scripts/check-evidence-files.sh` | No lane evidence (receipts, handoffs, provenance, checksum manifests, resource and validation records) under `tests/` or `Bridge/tests/`; lanes archive it in the private coordination repository with `scripts/coord-tools/coord-evidence` and cite the printed path. Run by CI and by every merge gate |
| `node scripts/check-axiom-pins.mjs` | Original axiom-policy errors plus new unrecorded pin changes; exact existing H112 drift uses a SHA256-pinned, shrink-only baseline |
| `solidity-lean rules check --key FILE` | Sort annotations against a SolKey rules file; manual, not part of any gate (H89) |
| `./scripts/check-corpus.sh` | `SolidityCorpus` against `tests/solkey/expected.tsv` |
| `./scripts/check-testsuite.sh` | TestSuite rows against `TestSuite/Report.lean`'s pin and SolKey functions; no Lean |
| `node scripts/check-automatic.mjs --strict` | Every TestSuite obligation has an automatic proof/replay or refutation, none pending; no Lean |
| `node scripts/solidity-upstream.mjs` | Pinned solc tests on the typed interpreter, per pipeline; [runner documentation](solidity-upstream-tests.md) |


## Before pushing

The merge pre-gate runs `gate.sh touched` on your head merged onto current
`origin/master`: it builds the modules you changed and the library modules that
import them, with the coverage described in
[`scripts/coord-tools/README.md`](../scripts/coord-tools/README.md). It is not a
full build. Run the same check first:

1. `git fetch origin master && git merge origin/master` (or a temporary worktree
   with the merge), then `bash scripts/coord-tools/gate.sh touched` in that tree.
   Fix failures there: the pre-gate rejects a head that builds only on an older
   base, or only in the files it changed. On a lane, `coord-ask --done` runs this
   check itself and does not report a head that fails it or conflicts with master
   (`--no-check REASON` when the failure is not yours).
2. A change to a module with many importers (for example `Solidity/Source/**`)
   keeps existing statements: add the new form beside the old one as a versioned
   pair (H57) and move the importers in the same head, or keep the old form until
   they move.
3. A gate, baseline or audit you add must pass on the merged head, not only on
   your base: compute ratchet baselines from the merge base or regenerate them at
   merge, and make audits re-runnable from committed scripts.

Progress and status go into your result, never into shared documents.

## Toolchain and proofs

Run from the repository root with the pinned `lean-toolchain`. Prefer per-file
Lean MCP diagnostics after a Lean edit, following the
[lean-verify skill](../.agents/skills/lean-verify/SKILL.md). Use full builds for
import changes and final confirmation. Documentation-only edits require path,
link and generator checks, not Lean compilation.

Symbolic execution needs `--tstack=131072`; use the configured project wrappers.
Try `grind`, `bv_decide` or `omega` before long manual proofs. Finished proofs
use `simp only [...]`, explicit signatures and typed local facts. Do not raise
`maxHeartbeats` to repair a proof.

## Tactics

Searching tactics need bounded search and a cheap replay suggestion twin.
Catch Lean runtime timeouts with `tryCatchRuntimeEx`; ordinary `try` does not
catch them. Pin regression examples and check generated proof terms with the kernel.
Profile before optimizing; avoid repeating search during replay.

## Worktrees and memory

Acquire the shared writer lock and follow
[resource bounds](refactoring-progress.md#resource-bounds-and-resuming-work)
before writes or Lean checks. Use a separate worktree for a parallel writing
lane; preserve unrelated work. Do not terminate other sessions' workers.
After a lane is integrated, remove only its own worktree and workers.

## Build cache and CI

After fetching master, `bash scripts/ci/fetch-lake-cache.sh` installs matching
artifacts. Missing cache bytes mean a cold build, not a passing check. Tools
reading `.lake/build` may need `python3 scripts/ci/restore-lake-artifacts.py`.
CI workflow files are authoritative for the actual job set and limits.

## Measurements

Use matched source, toolchain, workload and cache conditions, complete result
denominators and the same resource limits. Failures and timeouts remain
failures; component timings are not end-to-end proof times. Representative
runners (their code defines options and required inputs):

```sh
node scripts/measure-simple.mjs .lake/simple-measurement
node scripts/measure-native.mjs .lake/simple-measurement
node vscode/test/measure-proof-speed.cjs .lake/proof-speed.json
node scripts/testsuite-performance.mjs --native
node web/test/performance.cjs --single --benchmark
```

## Documentation reviews

End each milestone with read-only finder and skeptic reviews; neither uses the
Lean server. Fix confirmed findings and record their resolution concisely.
This cleanup preserved live parsed/pinned inputs and model boundaries; the
independent reviews and reference/generator checks cover the removed prose. Keep source,
tests and generated inventories authoritative; do not maintain parallel prose
implementation catalogs or chronological gate receipts.

New guidance must add information not reasonably recoverable from code/tests
and be linked from its topic guide. After adding it to Git, run
`python3 scripts/check-doc-navigation.py --write`; CI checks discoverability.
