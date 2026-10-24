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

## P1. The core apart from the elaborator

### The core

112 modules, `CORE` in `scripts/check-layers.mjs`:

- `KeySort`, `Eqns`, `AST`, `Scope`, `SpecSyntax`, `Hashes`, `Keccak`,
  `RevertBytes`, `Syntax`, `Signature`, `Update`;
- `Syntax.{Scoped,Checked,Inlined,PushSource,Join}`;
- `Semantics` and `Semantics/**` (29), `Typing/**` (12), `Theory/**` (6);
- the rules: `Calculus.{Fml,Rules,RuleSyntax,RuleKit,KeyTaclets,Step,Arms,
  Blocks,Taclet,Proves,Logic,Hyp,Correct,FirstOrder}`;
- their soundness: `Calculus.{Sound*,StmtSound,ProvesSound,PremiseSound,
  UpdRuleScoped,UpdateRules,TermLib.Rules}`;
- what those import: `Calculus.{TermEval,TermEq,TermWk,Lower,LowerRun,Shift,
  WkOver,Lands,StateFacts,ReadWrite,DataIn,SeqRewrite,SyntaxSize,Graft,
  CallSummary}`.

The list is closed under imports: no core module imports a module outside
it.  The elaborator is `Syntax/{Elab,Quote,Splice}` and
`Calculus/{Print*,Surface*,TacticSyntax,Quote,NamedTerm}`.

**A new module** that only states or proves (no `sol{}`, `dl!{}`, `#wp`,
`#guard_msgs` of a printer) belongs in the core if what it imports is: add
it to `CORE` when its name is not matched already.  Examples written in the
surface syntax go above, in `Examples/`.

### The cuts

| Path | Cut |
|---|---|
| `Semantics.State → Syntax.Quote` | import dropped (unused) |
| `Semantics → Syntax.Splice` | replaced by `Syntax.Checked`; the nine modules above the core that wrote programs through it import `Syntax.Splice` themselves |
| `Semantics.DeferredSource → Syntax.Elab` | import dropped (unused) |
| `Calculus.TermLib → Calculus.PrintTerm` | split: the rules and their soundness are `Calculus/TermLib/Rules.lean` (core), the printers and pins stay in `TermLib.lean`, which imports it |
| `Calculus.Blocks → Prog.join` (in `Syntax/Elab.lean`) | `Prog.join` moved, same name, to `Syntax/Join.lean` |
| `Semantics.Run`'s `sol[C]{…}` examples (`guardLowCore` …) | moved to `Examples/ScopedRuns.lean` |
| `Syntax.Quote → Syntax.Elab` | narrowed to `Syntax.Scoped`, all `Quote` uses; `Syntax.Splice` imports `Syntax.Elab` itself |

No notation had to move: the core's `dl{}`/`tm{}` macros already sat below
the elaborator.  Nothing was restated, so there is no `rfl` to show.

### Fan-out, before and after

| Module | P0 | P1 |
|---|---|---|
| `Syntax.Elab` | 501 | 294 |
| `Syntax.Quote` | 500 | 308 |
| `Syntax.Splice` | 499 | 228 |
| `Syntax.Scoped` | 505 | 508 |
| `Syntax` | 508 | 511 |
| `Semantics.Run` | 459 | 461 |
| `Signature` | 440 | 441 |
| `Calculus.Fml` | 423 | 424 |
| `Calculus.RuleSyntax` | 304 | 305 |
| `Calculus.Rules` | 277 | 278 |
| `Calculus.Close` | 255 | 255 |
| `Calculus.Decide` | 202 | 202 |
| `Frontend.SolcJson` | 55 | 55 |

The low modules gain the three new ones (532 modules).  The longest import
chain falls from 53 to 50 modules: `Elab → Quote → Splice` is no longer on
the way to the calculus.  `Decide`, `Closer`, `MemRead` and `TermLaws` no
longer reach `Elab`; what does is the tactics, the printers, the examples,
the TestSuite and the frontends.

## P2. Large files split by topic

Every file over ~1800 lines on the task's list is a directory of pieces of at
most ~1500 lines, cut at its own `section`s and topic headers, each piece
importing the one before; the file itself is the umbrella that imports them
all, keeping its docstring (the whole's rationale) and naming its pieces.
The cutting is mechanical: a piece restates the file's
`namespace`s, `open`s and file-level `variable`s, and a section cut in two is
closed and reopened with its `variable`s.  Nothing else moved, and no
declaration changed name.

| File | Lines | Pieces |
|---|---|---|
| `Syntax/Elab` | 6389 | `Context` 1381, `Values` 1466, `Lower` 1390, `Arms` 1525, `Stmt` 699 |
| `Calculus/Closer` | 3959 | `Facts` 938, `Normal` 621, `Bytes` 1136, `Leaf` 1304 |
| `Calculus/MemRead` | 4292 | `Spine` 1049, `Laws` 1085, `Ok` 1169, `Pass` 1021 |
| `Calculus/DecideEval` | 2911 | `Readers` 1123, `Storages` 894, `Memory` 929 |
| `Calculus/RuleSyntax` | 2817 | `Grammar` 1229, `Schemas` 1175, `Print` 370 |
| `Calculus/RewritePast` | 2813 | `Scope` 805, `Merge` 742, `Apply` 1278 |
| `Calculus/TermLaws` | 2616 | `Storage` 817, `Reads` 833, `Fresh` 983 |
| `Frontend/SolcJson` | 2533 | `Body` 1418, `Contract` 1051 |
| `Syntax` | 2373 | `Raw` 695, `Grammar` 1040, `Contract` 612 |
| `Calculus/CloseScoped` | 2223 | `Leaf` 1188, `Steps` 1024 |
| `Semantics/Storage` | 2222 | `Values` 838, `Ops` 1374 |
| `Calculus/Chains` | 2221 | `Strategy` 892, `Proofs` 674, `Elab` 649 |
| `Theory/Typed/Obs` | 2173 | `Paths` 665, `Values` 888, `Ops` 626 |
| `Calculus/CallbackSound` | 1921 | `Rules` 851, `Calls` 1063 |

Not split:

- `Corpus/TestSuite` (2624) is generated by `scripts/solkey-port.mjs` ("do
  not edit by hand"); a split belongs in the generator, and the module is a
  leaf of the TestSuite, so nothing waits on it.
- `Calculus/SoundArms` (1390) and `Calculus/SoundCalls` (1377) are below
  the threshold (P0).

**Pitfalls met.**

- *A matcher is shared only within its module.* `Semantics/Storage`'s
  `match` twins (`SVal.find_at` …) state a `match` that is, by `rfl`, the
  matcher `SVal.findM` unfolds to: Lean reuses one auxiliary matcher for
  equal `match`es in a module, not across modules.  Cut between the
  definitions and their twins, the `simp only [findM]` steps leave
  `match … = match …` with two matchers.  The cut moved so that
  "Find and save" and the twins are one piece (`Storage/Ops`).
- *A narrowed import can drop a name the importer used transitively*:
  `Calculus/SurfaceNotation` used `synth` and `Calculus/SurfaceSpec`
  `elabStmtsP` through `NamedTerm`'s old `Syntax.Elab` import.  Each now
  imports the piece it uses.  A narrowing is safe only when the pieces it
  drops register no instance, macro or delaborator the importer's output
  reads; `RuleSyntax/Print` holds the delaborators, so no importer of
  `RuleSyntax` is narrowed.
- *The layer check names core modules exactly*: the pieces of a core file
  (`Syntax`, `Semantics/Storage`, `Theory/Typed/Obs`, `RuleSyntax`) are added
  to `CORE`, 123 modules now.

**Narrowing.**  `Calculus.NamedTerm` imports `Syntax.Elab.Context` and
`Calculus.SurfaceNotation` `Syntax.Elab.Values` (it reads `synth`):
an edit to `Elab.Lower`, `Arms` or `Stmt` rebuilds 281–283 modules where
`Syntax.Elab` rebuilt 294.  The gain is small because `Calculus.SurfaceSpec`,
low in the graph, uses the whole elaborator.  For the other files every
importer reaches the last piece anyway (the fan-outs of a file's first and
last pieces differ by at most two modules), so the gain of the splits is the
memory of a worker and the size of what an edit re-checks, not fan-out.

**Speed** (`lake env lean --tstack=131072`, serially, faster of two runs;
peak RSS the larger; a bench clone with the artifact cache off so the
`.olean`s sit in its build dir).  Batch 1 against P1 (`2fe601df`):

| File | Before (s, GB) | Largest piece (s, GB) | Sum of pieces (s) |
|---|---|---|---|
| `Calculus/MemRead` | 23.5, 2.87 | `Spine` 7.8, 2.12 | 26.5 |
| `Calculus/Closer` | 10.3, 3.17 | `Facts` 4.2, 2.02 | 13.4 |
| `Syntax/Elab` | 18.0, 1.75 | `Arms` 9.5, 1.37 | 20.4 |

Downstream files, before → after: `ElimFacts` 1.8 → 1.8, `DecideScoped`
0.9 → 0.9, `SurfaceNotation` 6.4 → 6.4, `NamedTerm` 1.3 → 1.3,
`Syntax/Splice` 2.1 → 2.0, `Examples/Tactics/Decide` 15.7 → 15.7.  No piece
and no downstream file is slower.  A chain of pieces costs about a second
per piece more than the whole (each loads its imports again); on the
critical path that is ~6 s of 504 s.

Batches 2 and 3 against master `e1f65769` (the largest piece's peak RSS is the
largest of any piece):

| File | Before (s, GB) | Largest piece (s, GB) | Sum of pieces (s) |
|---|---|---|---|
| `Calculus/RuleSyntax` | 20.7, 1.51 | `Grammar` 15.6, 1.50 | 21.3 |
| `Calculus/TermLaws` | 15.6, 2.60 | `Fresh` 8.5, 2.06 | 17.9 |
| `Syntax` | 8.3, 1.35 | `Grammar` 4.8, 1.27 | 9.1 |
| `Frontend/SolcJson` | 6.5, 1.30 | `Contract` 4.7, 1.25 | 6.9 |
| `Calculus/RewritePast` | 4.6, 1.76 | `Apply` 3.4, 1.57 | 5.6 |
| `Calculus/Chains` | 5.4, 1.51 | `Strategy` 2.5, 1.43 | 6.5 |
| `Calculus/CloseScoped` | 4.3, 1.40 | `Steps` 3.5, 1.32 | 4.7 |
| `Semantics/Storage` | 3.9, 1.37 | `Ops` 2.5, 1.31 | 4.1 |
| `Theory/Typed/Obs` | 3.6, 1.37 | `Paths` 2.3, 1.30 | 4.5 |
| `Calculus/CallbackSound` | 2.9, 1.69 | `Calls` 2.5, 1.54 | 3.7 |
| `Calculus/DecideEval` | 2.0, 1.47 | `Readers` 1.2, 1.36 | 3.0 |

Downstream files, before → after: `Calculus/ElimWriteFree` 1.1 → 1.1, `Calculus/Hyp` 0.4 → 0.4, `Calculus/RewriteLaws` 0.5 → 0.5, `Calculus/CloseFrame` 0.6 → 0.6, `Calculus/ChainGen` 1.6 → 1.6, `Calculus/CallbackDerive` 1.5 → 1.5, `Syntax/Scoped` 3.5 → 3.5, `Semantics/Heap` 0.8 → 0.7, `Signature` 1.2 → 1.2, `Frontend/Import` 1.8 → 1.8.  Again no piece and no downstream
file is slower.

## P3. Theorems: one lemma per rule

Statement-rule soundness was already split by rule: one lemma per arm in
`Calculus/SoundArms.lean` … `SoundLoops.lean`, dispatched by
`Calculus/SoundStep.lean` (`Stmt.stepSound_arms`) and
`Calculus/StmtSound.lean` (`Stmt.stepSound`, the blocks), each one `cases s`.
That structure stays, and no existing lemma moved.  A rule added from now on
proves its arm in `Calculus/Sound/<KeYName>.lean`, one file per rule
(`Calculus/Sound/README.md`; the template is in `.claude/rules/soundness.md`),
so that it elaborates alone and in parallel with the others.

**Term taclets** (`TermTaclet.sound`, `Calculus/TermLib/Rules.lean`): of its
30 cases, 15 were proved inline by tactic blocks inside the one `match`.
Each is now a named lemma beside it, `TermTaclet.<rule>_sound`, stating the
constructor's own binders and terms, the proof moved as it was; the case
applies it.  The other 15 were one term already: twelve
`Tm.findIn_fill_theq` of the rule's `…_denote`, `delValueLit` by `rfl`,
`theory` its hypothesis, `symm` the recursion.
**Update rules** (`UpdRuleS.sound`, `Calculus/UpdRuleScoped.lean`): each of
its 7 cases already applies one lemma (`holds_upd_seqPar`, …); unchanged.

### Adding a rule: the six places

1. **The constructor**: `Taclet` in `Calculus/Rules.lean`, written in
   `dl{ … }` (`.claude/rules/rule-table.md`, step 1).
2. **Its `Stmt.step` arm**: `Calculus/Arms.lean` or `Calculus/Blocks.lean`,
   dispatched by `Calculus/Step.lean`, with `Taclet.<rule>.toStep`
   (`Calculus/Taclet.lean`) and, where the arm is new, `Stmt.<c>.ruleExists`
   (`Calculus/RuleExists.lean`).
3. **Its soundness file**: `Calculus/Sound/<KeYName>.lean`.
4. **The assembly line**: an import and a case in `Stmt.stepSound_arms`
   (`Calculus/SoundStep.lean`), or in `Stmt.stepSound`
   (`Calculus/StmtSound.lean`) for a block.  The `cases s` is exhaustive:
   a statement whose arm has no lemma fails the build.
5. **The rule map row**: `docs/lean-key-rule-map.md`, the solkey taclets it
   transcribes and the file of its soundness.
6. **The printed tables**: `RuleShapes.tacletOrigins`
   (`Calculus/RuleShapes.lean`) and `PrintedRules.printedOrigins`
   (`Calculus/PrintedRules.lean`); `#check_constructor_table` fails on a
   missing row.  A taclet that reads storage or memory also gets its row in
   `SortCheck/Annotations.lean`, checked by `lake exe solkeycheck`.
