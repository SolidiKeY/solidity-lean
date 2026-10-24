# Parallelism: layers, files and theorems

How the package is cut so that Lake can check it in parallel and an edit
rebuilds little: the core apart from the elaborator (P1), large files
split by topic (P2), one soundness file per new rule (P3), and the closer's
clauses as units (P4, gated on speed).  Nothing here changes behaviour:
every `#guard_msgs` pin, the axiom pins and the TestSuite report are
unedited.

The tools: `node scripts/import-fanout.mjs` prints each module's rebuild
fan-out (how many modules import it transitively) and the longest import
chain, `--path A B` one import path from `A` to `B`;
`node scripts/check-layers.mjs` fails when a core module reaches the
elaborator.

## How it is measured

- **Fan-out and chain**: `scripts/import-fanout.mjs` over
  `Solidity/**/*.lean` and `Solidity.lean` (`Solidity/Scratch/` skipped).
- **Builds**: a clean shallow clone in a tmpfs, with an empty private Lake
  cache (`LAKE_CACHE_DIR`, so the shared artifact cache is neither read
  nor written) and `LEAN_NUM_THREADS=12` on a 32-core, 62 GB machine that
  other sessions share.  `lake build` cold, then `lake build
  SolkeyTestSuite` on top of it.  The weighted critical path sums the
  per-module times Lake prints along the heaviest import chain.
- **Files**: `lake env lean --tstack=131072 <file>` in the built clone,
  serially, twice each; the table gives the faster wall time and the larger
  peak RSS (`getrusage` of the child: `/usr/bin/time` is not installed).
  Repeats agree to within 0.3 s.

## P0. Baseline (2026-10-24, master `3b03ac58`)

529 modules.  The task's own count (469 modules, `Syntax.Elab` rebuilding
442) was older: the tree has grown since.

| Module | Fan-out |
|---|---|
| `Syntax` | 508 |
| `Syntax.Scoped` | 505 |
| `Syntax.Elab` | 501 |
| `Syntax.Quote` | 500 |
| `Syntax.Splice` | 499 |
| `Semantics.Run` | 459 |
| `Signature` | 440 |
| `Calculus.Fml` | 423 |
| `Calculus.RuleSyntax` | 304 |
| `Calculus.Rules` | 277 |
| `Calculus.Close` | 255 |
| `Calculus.Decide` | 202 |
| `Frontend.SolcJson` | 55 |

The core reached `Syntax.Elab` only through convenience imports, four in all:

- `Semantics.State → Syntax.Quote → Syntax.Elab` (`State` uses nothing of
  `Quote`);
- `Semantics → Syntax.Splice → Syntax.Quote → Syntax.Elab` (`Semantics.lean`,
  the call data and ABI observations, needs only `AST`), and through it
  `Calculus.Rules → RuleSyntax → Update → Theory.Segs → Semantics`;
- `Semantics.DeferredSource → Syntax.Elab`, unused;
- `Calculus.TermLib → Calculus.PrintTerm`, the term taclets' printers.

**Critical path**: the longest import chain is 53 modules
(`KeySort → AST → … → Syntax → Syntax.Scoped → Syntax.Checked → Syntax.Elab
→ Syntax.Quote → Syntax.Splice → Semantics → … → Calculus.MemRead → … →
Examples.AliasConstraints → Solidity`).  Weighted by build time it is
504 s over 41 modules, 290 s of it `Examples.Tactics.OpenLoops`; `Elab`,
`Quote` and `Splice` are 22 s of it.

**Builds**: cold `lake build` 662.7 s (peak RSS of one process 13.6 GB);
`lake build SolkeyTestSuite` after it 128.1 s.

**The 20 largest files** (lines): `Syntax/Elab` 6389, `Calculus/MemRead` 4292,
`Calculus/Closer` 3959, `Calculus/DecideEval` 2911, `Calculus/RuleSyntax` 2817,
`Calculus/RewritePast` 2813, `Corpus/TestSuite` 2624, `Calculus/TermLaws` 2616,
`Frontend/SolcJson` 2533, `Syntax` 2373, `Calculus/CloseScoped` 2223,
`Semantics/Storage` 2222, `Calculus/Chains` 2221, `Theory/Typed/Obs` 2173,
`Calculus/CallbackSound` 1921, `Typing/CleanTailRun` 1797,
`Calculus/FlattenTotality` 1745, `Calculus/TermLib` 1640, `Calculus/Graft` 1638,
`Semantics/RunWk` 1614.  `Calculus/SoundArms` (1390) and
`Calculus/SoundCalls` (1377) have dropped below the split threshold.

**The 15 largest files, checked alone**:

| File | Wall (s) | Peak RSS (GB) |
|---|---|---|
| `Calculus/MemRead.lean` | 23.8 | 2.69 |
| `Calculus/RuleSyntax.lean` | 20.4 | 1.52 |
| `Syntax/Elab.lean` | 18.0 | 1.68 |
| `Calculus/TermLaws.lean` | 15.6 | 2.44 |
| `Calculus/Closer.lean` | 10.2 | 3.19 |
| `Corpus/TestSuite.lean` | 8.9 | 1.90 |
| `Solidity/Syntax.lean` | 8.7 | 1.35 |
| `Frontend/SolcJson.lean` | 6.5 | 1.30 |
| `Calculus/Chains.lean` | 5.5 | 1.51 |
| `Calculus/RewritePast.lean` | 4.5 | 1.73 |
| `Calculus/CloseScoped.lean` | 4.3 | 1.40 |
| `Semantics/Storage.lean` | 3.8 | 1.38 |
| `Theory/Typed/Obs.lean` | 3.6 | 1.40 |
| `Calculus/CallbackSound.lean` | 2.9 | 1.72 |
| `Calculus/DecideEval.lean` | 2.0 | 1.48 |

**Checks on master before any edit**: `check-orphans` passes on a clean
checkout (a working copy's untracked `Solidity/Scratch/` modules are
orphans by design); `check-doc-paths.sh` already fails (six missing
`Bridge/vendor/CslibBackport` citations and ambiguous bare file names);
`check-automatic.mjs --strict` already fails on one pending obligation
(`invariantClosedFormSum`); `check-testsuite.sh` passes against the frozen
snapshot (`--solkey tests/migration/solkey/keyext.solidity.examples`), and
fails against a newer sibling `../solkey` only because `TestSuite.sol`
moved.  Every milestone below is held to the same output: no new failure,
the same counts.
