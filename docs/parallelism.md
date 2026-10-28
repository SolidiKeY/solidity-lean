# Parallelism: layers, files and theorems

How the package is cut so that Lake checks it in parallel and an edit
rebuilds little: the core apart from the elaborator (P1), large files split
by topic (P2), one soundness file per new rule (P3); the closer's clauses
stay one function (P4).

The tools: `node scripts/import-fanout.mjs` prints each module's rebuild
fan-out (how many modules import it transitively) and the longest import
chain, `--path A B` one import path from `A` to `B`;
`node scripts/check-layers.mjs` fails when a core module reaches the
elaborator.

## P1. The core apart from the elaborator

### The core

`CORE` in `scripts/check-layers.mjs` is the authority; by family:

- `KeySort`, `Eqns`, `AST`, `Scope`, `SpecSyntax`, `Hashes`, `Keccak`,
  `ERC7201`, `Secp256k1`, `TypeGraph`, `RevertBytes`, `Syntax`, `Signature`,
  `Update`;
- `Syntax.{Raw,Grammar,Contract,Scoped,Checked,Inlined,PushSource,Join}`;
- `Semantics` and `Semantics/**`, `Typing/**`, `Theory/**`;
- the rules: `Calculus.{Fml,Rules,RuleSyntax,RuleKit,KeyTaclets,Step,Arms,
  Blocks,Taclet,Proves,Logic,Preconditions,FiniteMembership,FilteredMembership,
  Hyp,Correct,FirstOrder,Transient,Lifetime,ContractWorld}` and `RuleSyntax`'s pieces;
- their soundness: `Calculus.{Sound*,StmtSound,ProvesSound,PremiseSound,
  UpdRuleScoped,UpdateRules,TermLib.Rules}`;
- what those import: `Calculus.{TermEval,TermEq,TermWk,LoopInvariantWk,Lower,LowerRun,Shift,
  WkOver,Lands,StateFacts,ReadWrite,DataIn,SeqRewrite,SyntaxSize,Graft,
  CallSummary}`.

`Tools.SolCases` is an external-source printer and is explicitly included in
the forbidden frontend set checked from the core.

The list is closed under imports: no core module imports a module outside
it.  The elaborator is `Syntax/{Elab,Quote,Splice}` and
`Calculus/{Print*,Surface*,TacticSyntax,Quote,NamedTerm}`.  Source
extraction for the core's composed models stays above it
(`Frontend/WorldImport`, `Examples/Tactics/TransientStorage.lean`).

**A new module** that only states or proves (no `sol{}`, `dl!{}`, `#wp`,
`#guard_msgs` of a printer) belongs in the core if what it imports is: add
it to `CORE` when its name is not matched already (the checker names core
modules exactly).  Examples written in the surface syntax go above, in
`Examples/`; a core module's `sol[C]{…}` examples live in
`Examples/ScopedRuns.lean`.  The core's `dl{}`/`tm{}` macros sit below the
elaborator; `Prog.join` is in `Syntax/Join.lean` and the term taclets'
rules in `Calculus/TermLib/Rules.lean` (printers in `TermLib.lean`) for this
reason.

## P2. Large files split by topic

A file over ~1800 lines becomes a directory of pieces of at most ~1500
lines, cut at its own `section`s and topic headers, each piece importing the
one before; the file itself is the umbrella that imports them all, keeping
its docstring and naming its pieces.  A piece restates the file's
`namespace`s, `open`s and file-level `variable`s; a section cut in two is
closed and reopened with its `variable`s.  No declaration changes name.
Generated files (`Corpus/TestSuite`) are split in their generator, if at all.

The gain is the memory of a worker and the size of what an edit re-checks,
not fan-out (every importer reaches the last piece anyway).  A chain of
pieces costs about a second per piece more than the whole; measured on the
2026-10-24 splits, no piece and no downstream file got slower, and the
largest workers fell (`Calculus/Closer` 3.2 → 2.0 GB, `Calculus/MemRead`
2.9 → 2.1 GB).  `tests/trust-inventory.json` (`scripts/check-trust.sh`)
names pieces, so a split updates it.

**Pitfalls.**

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
- *The layer check names core modules exactly*: the pieces of `Syntax` and
  `RuleSyntax` are added to `CORE` (those of `Semantics/Storage` and
  `Theory/Typed/Obs` were matched already), 123 modules now.

## P3. Theorems: one lemma per rule

Statement-rule soundness is one lemma per `Stmt.step` arm
(`Calculus/SoundArms.lean` … `SoundLoops.lean`), dispatched by
`Calculus/SoundStep.lean` (`Stmt.stepSound_arms`) and
`Calculus/StmtSound.lean` (`Stmt.stepSound`, the blocks), each one
`cases s`.  A new rule proves its arm in `Calculus/Sound/<Arm>.lean`, one
file per new arm (`Calculus/Sound/README.md`; the template is in
`.claude/rules/soundness.md`), so that it elaborates alone.  Each
`TermTaclet.sound` case (`Calculus/TermLib/Rules.lean`) applies a named lemma
`TermTaclet.<rule>_sound` or is one term.

### Adding a rule: the six places

0. **Start** from `docs/rule-repair.md`: the gates before integration.
1. **The constructor**: `Taclet` in `Calculus/Rules.lean`, written in
   `dl{ … }` (`.claude/rules/rule-table.md`, step 1), its labels kept equal
   to `Taclet.branchLabels` (`Calculus/RuleKit.lean`).
2. **Its `Stmt.step` arm**: `Calculus/Arms.lean` or `Calculus/Blocks.lean`,
   dispatched by `Calculus/Step.lean`, with `Taclet.<rule>.toStep`
   (`Calculus/Taclet.lean`) and, where the arm is new, `Stmt.<c>.ruleExists`
   (`Calculus/RuleExists.lean`).
3. **Its soundness**: a new arm's file `Calculus/Sound/<Arm>.lean`; a taclet
   added to an existing statement extends that statement's `…Step_sound`
   where it is (`Calculus/SoundControl.lean` …).
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
   `taclets_partitioned`/`printed_rules_partitioned` and the claimed and
   unclaimed counts move with the rows.

A new statement form is a larger change than a rule: the syntax, the run,
the typing, the EVM, the quoters and printers (`Syntax/Quote.lean`,
`Calculus/Quote.lean`, `Calculus/PrintStmt.lean`) and `Stmt.isBlockArm`.

## P4. Closer clauses stay one function

`LFml.close` is one `Bool` on purpose, chosen for speed:

- the closer is the reflective half of `sol_prove` (`docs/testsuite-proofs.md`,
  M1 and M4, `3fc9bb4c`): one kernel evaluation runs the strategy and the
  closer per obligation, a leaf costing 50–60 ms and under 1k heartbeats in
  one `decide`, against ~600 ms and 18k heartbeats per leaf
  for a tactic proof of the clauses.  A KeY taclet is a clause of that function,
  not a proof step, so that it costs the kernel one evaluation, not a proof;
- the functions the kernel evaluates keep Gate G0's forms
  (`docs/intrinsic.md`, M0; `docs/kernel-port.md`): recursors and
  `casesOn`, with a `match` twin for compiled code, because a `match` on a
  context-indexed family costs the kernel a context comparison per cast
  (11–13× on symex).

Clauses as records folded over a list would change what the kernel unfolds
on every leaf (structure projections and the fold, on top of each clause),
the cost that design avoided, so the prototype was not written.  Changing
it is the closer owner's decision, gated on measuring
`Calculus/CloseTests.lean`, `Examples/Tactics/Decide.lean`, two
`TestSuite/Derived*` modules and the whole `SolkeyTestSuite`.
