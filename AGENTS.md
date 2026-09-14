# Repositories

The KeY-based Solidity prover this package models:
https://github.com/SolidiKeY/solkey

`lake exe solkeycheck` and `scripts/solkey-port.mjs` expect a checkout of it
beside this repository (`../solkey`); both take an explicit path
(`--key`/`SOLKEY_RULES`, `--solkey`) when it lives elsewhere.

A second, separate consumer of this package is **the `SolKey` reader** — a
Lean reader for KeY `.key` files that path-requires this package and proves
its parsed taclets are these rules. It lives in a separate repository, pins
the same toolchain, and imports only `Solidity.Rules` (and through it
`Solidity.AST` and `Solidity.KeySort`). Those three modules are its whole
dependency surface: renaming a `RuleName` or changing a `ruleEffect` arm
breaks its correspondence proofs, which is the point of it.

# Lean Instructions

Prefer the configured Lean MCP server (diagnostics, goals, hover, validation)
over shell commands; use the shell only when the MCP cannot help or a bulk
project-level check is clearly more efficient.

Lean sources are the `Solidity` Lake package at the project root. Run
Lean/Lake commands from the project root, or use `./run-lean.sh`.
(`scripts/lean-vscode/bin` wrappers exist only so the VS Code extension finds
the Nix-provided `lean`/`lake` on NixOS.)

**The package has no external dependencies.** `lakefile.toml` declares no
`[[require]]` at all: no Mathlib, and no Loom since `Wp/Monad.lean` started
defining `Box.wpB`/`Dia.wpD` outright instead of deriving them from Loom's
`wp` + handler discipline. Keep it that way — every require added here is a
clone that every consumer of this package has to pay for.
Anything a proof needs from Mathlib is a sign the proof should be done
differently, or the lemma stated locally.

File map (`Solidity/` unless noted):

- `KeySort.lean`: solkey's sort lattice as one Lean type — every sort the
  `.key` headers declare plus the per-program `array`/`mapping`/`contract`
  sorts `SolJSONParser` creates, the direct `\extends` edges (`parents`),
  their closure (`ancestors`), the subsort test `KeySort.le`, and the KeY
  spellings (`name`/`ofName`). Imports nothing; `AST.lean` imports it.
  This is the *only* model of the lattice: `TacletAnnotations`,
  `SortFaithfulness` and the `SolKey` reader's decoder all state their sort claims
  against it. Note what it records that the prose did not: array and
  mapping types have their own sorts directly below `StValue`, siblings of
  `Struct`, not below it (`SolJSONParser.java:1015-1030`).
- `AST.lean`: Solidity syntax model — names, fields, types, locations,
  expressions, statements, blocks, expression measures. Types mirror the
  KeY sort hierarchy structurally: `PrimTy` (`bool`/`uint`/`int`) nests
  under `Ty.prim` (KeY `int, bool \extends Prim`); `Ty.keySort` /
  `keySortOf` is the static type's KeY sort as `SolidityInfo` and
  `SolJSONParser` assign it (with the `memoryPayload` reading of
  `FieldExpressionTypeToSortCondition`), `Ty.isMemoryReferenceType` /
  `Ty.isStorageReferenceType` the two Java reference predicates, and
  `localVarSort` the `List`/`Identity` re-sorting of locals; the header
  facts are theorems (`Ty.keySort_le_prim : … = ty.isPrimitive`). A
  `Field` is a name and a declared type, its subsort **computed** by
  `Field.sort = ty.fieldSort` exactly as `SolJSONParser.fieldSortFor`
  stamps it (`map` for a mapping, `ref` for a struct/array, `prim` — KeY's
  bare `Field` — for a value; solkey `0f9b99ad55` dropped the old
  `PrimField`/`IdField` subsorts, and the taclets select a value member by
  `\hasFieldSort(a, \sort(alphaPrim))`), so a field can no longer be
  classified against its own type. The `Typed` layer has the literal trio
  (`PrimField`/`RefField`/`MapField`). The old constructor names
  (`Ty.uint`, …) remain as `@[match_pattern]` abbrevs, so they still work
  in patterns — but `cases`/`induction` see only `prim`/`ref`.
- `KeyTaclets.lean`: the 252 taclets of `solidityProgramRules.key` as one
  Lean type, plus each one's `\heuristics` rule set, and `KeyOrigin` — what a
  `StepEffect` says about where it comes from (`taclet` / `merged` /
  `leanOnly`).  The reason a rule
  can name its taclet without a string: a misspelling is a type error.
  Imports nothing; regenerate from the vendored `.key` with the `awk` recipe in
  its docstring when the table is re-pinned to a newer solkey revision.
- `RuleSyntax.lean`: the `sol_rule` declaration syntax and
  `sol_assemble_rules`, which generate `RuleName`, `ruleEffect`, `ruleNames`
  and `twinPairs` from it.  Imports `Lean` and nothing else — it generates
  syntax, and the names it generates resolve where the generated code lands
  — so the `SolKey` reader's dependency surface is unchanged.  Carries the
  schema-variable table (`schemaVar`): the paper's convention that a
  variable's *kind* is its name, made mechanical.  Two notes for anyone
  extending the grammar: the KeY-side vocabulary is written as
  *applications* (`save(p, t)`, `inBounds(p)`) because Lean's category
  parser never reaches a non-reserved keyword alternative when a bare
  `rule_expr` alternative exists, and reserving those words would change how
  `sol!` programs lex; and Lean's lexer reads `sp.fld` as one identifier, so
  the components are split in `exprView?`, exactly as
  `SoliditySyntax.expandSolPathExpr` splits them for `sol!`.
- `Rules.lean`: one `sol_rule` per rule of the calculus — conditions in the
  calculus's schema variables, goals as KeY's guarded/obligation goals, and
  the fresh-name conventions and helper constructors the residuals use.
  **Organised by family** — Storage (Step 1 unfold RHS / Step 2
  unfold LHS / Step 3 update, then require-assert, conditional, abrupt) ›
  Payment › Memory (same three steps) › Storage→Memory › Memory→Storage ›
  Arithmetic (local / storage / memory targets) › the rules with no upstream
  name — with the same banners in `RuleName`, `ruleEffect` and
  `ruleNames`, and the conditions written in the calculus's schema
  variables (`se`, `sp`, `nsp`, `gsp`, `lsv`, `mv`, `nmp`, `arr`, `map`,
  `i`, `f`, `sadr`), the conjunctive ones as the reducible `abbrev`s
  `isSe`/`isSp`/`isMv`/`isNmp`.  Rules that upstream states as two stacked
  sequents are box/diamond twins named `<rule>Box`/`<rule>Diamond`;
  the box twin is listed first and `CandidateStep.twins_box_first` checks it.
  See the module docstring.
  Includes the memory-target arithmetic family
  (`memory{Field,Index}CompoundAssign`, `memory{Field,Index}IncDec`, their
  `Assignment` and `UnfoldLeftFst` twins) — upstream's `memoryFieldOpAssign`
  / `memoryFieldDivAssign` / `memoryIndexArrayOpAssign` /
  `memoryFieldIncrement`, which the pinned revision predates.  No root
  form (a memory root binds an identity, not a value cell) and no mapping
  form (memory has no mappings).
  **A rule is a taclet, not a rewrite.**  `StepEffect` carries `goals`, not a
  `block`: a list of `RuleGoal`s, each a guard, an update term and a residual,
  read as KeY's weakest precondition — for `⟨stmt; rest⟩post` each goal
  contributes `guard → {update}⟨residual ++ rest⟩post`.  That is what lets the
  table state the four things a `block` could not: the updates
  (`{storage := save(storage, sp, se)}`), the guarded splits (the array
  `"inBounds"`/`"outOfBounds"` pair, `\if(se2 != 0) \then … \else revert()`),
  the constant and obligation goals (`revertBox`'s `\replacewith(true)`,
  `assertSimple`'s "Violated") and the `\heuristics`/taclet provenance
  (`origin`, from `KeyTaclets.lean`).  `StepEffect.block` survives as a *def* —
  `mainBlock (goals stmt h)` — definitionally equal to the old field, which is
  why every `rfl` about a residual still goes through.  The update *syntax*
  lives here and is AST-only (no `State`, no `Res`), so the `SolKey` reader keeps
  importing this file cheaply and the updates cannot be defined as the
  interpreter; evaluation is `Update/Eval.lean`, the wp reading is
  `Update/Wp.lean`, and each rule's update is proved against
  `Wp.terminalUpdate?` in `Update/TacletTable.lean`.
- `RuleShapes.lean`: the checks on that structure — `mainBlock` reduction
  lemmas per goal combinator, `goals_nonempty` (a rule with no goals would
  prove anything), and the origin facts: `taclets_partitioned` (of the 252
  taclets, 246 are claimed by a Lean rule and six are listed with a reason —
  `emptyModality`/`blockEmpty` architectural, the two deleted
  `index*InnerNonSimpleIndexCapture`, `ifSplit`/`ifElseSplit` ported as
  `SolidityJudgment.ite_split`), `twins_origin_eq`, `heuristics_eq_origin`
  and `leanOnlyRules`.
- `Completeness.lean`: `FirstStepCase`/`RuleStep`, the definitional
  bridge `RuleStep.step_of_ruleApplies` ("some rule's condition holds
  ⇒ a step exists") and its converse `ruleApplies_of_ruleStep`. The
  completeness theorem proper lives in `Coverage.lean`.
- `Coverage.lean`: `candidate_applies` (converse of
  `applicable_eq_candidate`), the purely syntactic `ResidueShape` (24
  documented shapes no rule covers), `coverage_residue` /
  `not_covered_iff_residue` (a `stmtWt`-typed statement is covered or
  residue, exclusively), and the completeness theorem over the
  rule-independent fragment, `RuleStep.complete_of_wellTyped`: well-typed
  and not residue ⇒ a first step. The fragment is `stmtWt`'s language
  (no `callStmt`, no memory `delete`, no branch-declaring `ite`, only
  `isArith` compound ops — of which `**=` is residue — no `.length`,
  no calls but `net`) minus the residue shapes.
- `Progress.lean`: progress is **false** for this calculus, and this
  file proves it (`symbolicIte`, a symbolic `if`, has no step under any
  modality; `not_progress`, `not_normalizing`), plus the judgment-layer
  split that handles it (`symbolicIte_judgment_split`). There is no
  catch-all rule tier. `BlockStep.wellFounded` (termination) is the
  documented open `sorry`.
- `MultiStep.lean`: one-step/multi-step relations and lifting theorems.
  `BlockStep` (`⇝`), `BlockReflMultiStep` (`⇝*`) and the rule-name-indexed
  `NamedBlockStep` (`b ⇝[.rule] b'`, the generalization of
  `Wp/TerminalRules.lean`'s `TerminalRuleStep` to nonempty residuals),
  plus the `Trans` instances that let `calc` mix them. The old `—→`/`—↠`
  arrows survive as input-only sugar; goals print `⇝`. See
  § "Never abandon the `sol!` notation".
- `Termination.lean`: termination-certificate interface; a decreasing block
  measure implies well-founded rewriting. The concrete all-rules certificate
  remains open.
- `RuleValidation.lean`: per-rule concrete validation of the unfold rules
  against the executable semantics (`native_decide` on original vs residual
  block). Terminal rules (empty residual) have their update theorems in
  `Wp/Terminal/` and are exercised concretely by
  `Examples/Taclets/` instead.
- `RuleSoundness.lean`: symbolic soundness bridge — a general interpreter
  congruence kit (env-agreement off the scratch alias names), a purity kit,
  capture read-back lemmas, and a `<rule>_sound` theorem per unfold rule:
  the rule's residual block agrees with the original statement under the
  interpreter, modulo the scratch alias bindings. The module docstring
  classifies the theorems by hypothesis shape. The `*WriteUnfoldLeft*`
  family now needs no *semantic* side condition on a primitive value
  operand (`hprim`, syntactic and decidable, is all that remains and is
  about the interpreter — see `Counterexamples/RefSourceOrder.lean`):
  `freezeRhs`
  binds the value into `rv` before any target capture, so `hev`, `hstable`
  and `pureExpr index` are gone from all ten rules (storage *and* memory)
  and the programs they used to exclude — `people[i++].age = i`,
  `values[i++] = i` — are inside the theorems
  (`Counterexamples/EvaluationOrder.lean` now proves agreement, not
  disagreement). The templates are `fieldWriteResolve{Storage,Memory}_sound`
  and `indexWriteResolve{Storage,Memory}_sound`. Exceptions to "one proved
  theorem per rule": the two call rules are stated relative to inlining
  (`functionBodyExpand_sound_inlined` proved,
  `functionCallArgCapture_sound_inlined` a documented `sorry`);
  `storagePushValueUnfoldRightSndArgument_sound` and
  `memoryWriteUnfoldRightSndResult_sound` are stated in full but carry a
  `sorry` for the storage/memory-alias argument case and the memory-kind
  right-hand side respectively (the proved cases are the `_stack_`/
  `_storage_` lemmas they dispatch to).
- `Counterexamples/EvaluationOrder.lean`: `people[i++].age = i` and
  `values[i++] = i`, both directions. The **pre-fix** residual (path
  captured before the RHS-first interpreter reads the RHS) is refuted,
  `¬ ResultsAgree` by `native_decide`, spelled literally so it stays true
  as the historical record; the **current** rules are then shown to agree
  on the same two programs by instantiating the general theorems.
- `Counterexamples/ErrorOrder.lean`: why the freeze cannot be made
  conditional on the path being impure. On `people[1 / 0].age = ghost` —
  pure path, pure simple RHS, inside the rule's condition — the interpreter
  reads the value first and is **stuck** on the unbound `ghost`, while an
  unfrozen residual resolves the path first and **reverts** on `1 / 0`
  (`resolveS` runs `evalInt`, and `checkArith` reverts). A simple RHS can
  only get stuck; a pure path can revert. `unfrozen_not_sound` is the
  refutation. This is what the old `hev : rhsToSVal s rhs = .ok (s, sv)`
  hypothesis was hiding: assuming the RHS *succeeds* deletes exactly the
  states where the unfrozen residual is wrong.
- `Counterexamples/RefSourceOrder.lean`: what the remaining syntactic
  hypothesis `hprim : rhs.ty.isPrimitive = true` carves out — and it is the
  **interpreter**, not the rule. On `people[carol.age++] = carol` (reference
  source, impure index) rule and interpreter disagree, but the real EVM sides
  with the *rule*: solc is right-hand-side-first only for a primitive source,
  while a struct source is copied member by member after the target slot is
  resolved, so the index has already run. Checked on chain as solkey's
  `TestSuite.storageIndexWriteRefSourceImpureIndex`
  (`SolidityRuntimeExecutionTest`). `Semantics.execAssignNested` is uniformly
  value-first and is therefore unfaithful to solc here; `hprim` is what stops
  the soundness theorems asserting the interpreter's answer. Open: make
  assignment target-first for reference sources, then drop `hprim`. See
  `docs/solc-alignment.md` § "Known divergence".
- `Uniqueness.lean`: rule mutual exclusion
  (`UniquenessAux.stepCases_exclusive`,
  `RuleSetDisciplined.mutuallyExclusive`), proved via a total dispatch
  `candidate` mirroring rule conditions (`applicable_eq_candidate`).
  Exclusion is per `Modality` (box/diamond); under the block modality
  `.both` a box/diamond twin pair applies simultaneously and
  `FirstStepCase` takes the box twin — the twelve twin pairs are
  effect-identical up to mode (`CandidateStep.twinEffects`, `rfl`) and
  `FirstStepCase.functional` makes the step relation a partial function
  for every modality. `RuleSetDisciplined` carries exactly three facts:
  exclusion, no duplicate names, every step case is a rule of the calculus. When
  adding/changing a rule, keep its condition disjoint from all others and
  update `candidate` and `applicable_eq_candidate`; a failing uniqueness
  build signals an overlap.
- `Wp/Monad.lean`: the interpreter as a program in
  `SolM := StateT State (ExceptT Halt Id)` (definitional repackaging only,
  `execStmtM`/`execBlockM`), and the two modalities of
  `SolidityJudgment.check` as one weakest precondition each — `Box.wpB`
  (error arm `h = Halt.revert`) and `Dia.wpD` (error arm `False`). Both are
  *defined* by the shape their `_run` lemma states, so `wpB_run`/`wpD_run`
  are `rfl`. This used to be a bridge to Loom's `wp` + `IsHandler`
  discipline; defining the two transformers outright is what let the `Loom`
  and `mathlib` requires go.
- `Wp/Verdict.lean`: `checkResult` and `check_eq_checkResult` — "given
  how the run ended, what is the verdict?", split out of
  `Wp/StepSoundness.lean` so that `Update/Wp.lean` can read a taclet's
  goals without importing the rewrite theory.
- `Wp/TerminalUpdate.lean`: the state update of every *terminal*
  rule (empty residual), written in the interpreter's state vocabulary
  (`findStorage`/`saveStorage`/`setEnv`/`alloc`/`setNet`/…) and never
  through its evaluators — one function per family (`assignStackRead`,
  `storageAssignUpd`, `memoryAssignUpd`, `compoundAssignUpd`, `incDecUpd`,
  `pushUpd`, `popUpd`, `memoryDeleteUpd`, …), the table `terminalUpdate?`
  (`some` exactly for the 83 terminal rule arms), `hasUpdate`,
  `terminalUpdate`. The one arm that keeps an interpreter call is
  `storagePlaceAliasUpd` (an impure captured path; pure form
  `storagePlaceAliasUpd_pure`).
- `Wp/Terminal/Vocab.lean`: the bridges from each interpreter evaluator
  (`resolveS`, `resolveLoc`, `readM`, `evalValue`, `rhsToSVal`, `rhsToMVal`,
  the operators) to the vocabulary readers, on the simple shapes the
  terminal guards admit. `Wp/Terminal/Update{Control,Stack,Compound,
  Storage,Memory,Decl,PushPop}.lean`: one `<rule>_update` theorem per
  terminal rule, `execStmt s stmt = terminalUpdate r stmt s` **under the
  rule's guard** (the guard is what fixes the shapes; a theorem that did
  not use it would be an interpreter fact, not a rule fact).
- `Wp/TerminalRules.lean`: the dispatch `terminalUpdate_sound` over the
  whole table, `TerminalRuleStep` (a first step of a *named* terminal rule)
  and `terminal_step_sound` — the "taclet ⇒ update" bridge — plus
  `isTerminal_of_hasUpdate` (every table rule has an empty residual, checked
  against `ruleEffect`). Not proved: the converse on
  `ruleNames` (no unfold rule is accidentally terminal).
  `Wp/StepSoundness.lean`'s `ConfigStep.exec` now takes the rule name
  and its update; `holds_iff` derives the interpreter step from the bridge.
- `Update.lean`: the symbolic-update algebra the calculus writes its
  derivations in — `Elem` (one state component, one *pre-state* reader),
  `Par` (a parallel update: every reader sees the incoming state, then the
  writes land left to right), `Upd.seq`, and the **merge law**
  `Par.seq_single : {u}{x := t} = {u ‖ x := {u}t}`, the step the calculus's
  last `⇝` line always is.  `UpdJudgment` is `{u} ⟨[ prog ]⟩ φ` with
  `check`/`Holds` in `SolidityJudgment.check`'s verdict shape.
- `Update/Bridges.lean`: the link to `Wp/TerminalUpdate.lean` — for a
  family and target shape, `Par.toUpd [...] = <family> args`.  Built on
  *frame* facts ("this rule writes only the storage component"), which is
  what makes `{storage := …}` the right spelling.  Its docstring
  carries the coverage list and, for each family not covered, the reason.
- `Update/Eval.lean`: what a taclet's `UpdTerm` *means* — one `Upd.Elem` per
  component it writes, each with a pre-state reader, plus `Guard.eval` (which
  returns `Res Bool`, because a guard's premises are read first and may halt)
  and `goalsExec`, the state a rule's goals produce under a modality.  Every
  reader is one of `Wp/TerminalUpdate.lean`'s; nothing is re-derived, which
  is what keeps `Update/TacletTable.lean`'s theorems about the *rules* rather
  than about two of my own definitions.
- `Update/Wp.lean`: the weakest-precondition reading —
  `guard → {update}⟨residual ++ rest⟩post` per goal, conjoined over the goals
  whose modality applies (`StepEffect.wp`).  `wp_terminalGoal`,
  `wp_splitGoals` and `wp_revertGoals` are the shapes that are *exhaustive*
  (whenever no update fires, some goal has accounted for the revert);
  `Rules.assertGoals` is deliberately not among them, because KeY's violated
  branch is an obligation and not a revert.
- `Update/TacletTable.lean`: `goalsExec … = terminalUpdate r …` per rule —
  the proof that a rule's stated update is the one the interpreter performs.
  21 rules are bridged (`bridgedRules`) and the rest are listed with a reason
  (`openBridges`); `bridges_account` checks the two together are exactly the
  rules with an update.  Bridges that need a KeY sort the Lean condition does
  not express carry it as a syntactic hypothesis (`hprim`, `hvar`, `hpure`),
  as the evaluation-order theorems do.
- `Update/Examples.lean`: the headline chain's last two lines
  — the sequential `{sp := …}{storage := save(…)}`, the
  merge into the parallel form, and a `native_decide` that the merged update
  is what the interpreter does to `State.exampleStore`.
- `EvalBattery.lean`: `sol_eval_battery` / `sol_exec_eval`, the tactics
  that normalize a concrete interpreter term. Split out of
  `Wp/Verifier.lean` because they depend on the interpreter alone —
  that is what lets `Spec/Tactic.lean` reuse them without the wp layer.
  Both take an optional `location`, so one lemma list
  serves the goal and `at *`.
- `Semantics.lean`: run-time values mirror KeY `Prim \extends StValue,
  MemValue`: `PrimVal` (`int`/`bool`) is shared by `SVal.prim` and
  `MVal.prim`, and stack `Value` is an abbrev of `PrimVal`
  (`SVal.int v` etc. remain as `@[match_pattern]` abbrevs). Also the
  executable state semantics (storage tree, memory
  heap, `net` ledger, locals, contract `selfBalance`); defines
  `SolidityJudgment.check`/`Holds`
  for the `sol!{ < stmts > (post) }` dynamic-logic syntax. Examples are
  proved with `native_decide`. The interpreter is total (no `partial`):
  Lean checks termination — structural on statements, a
  `4 * WrappedExpr.size + rank` measure on the expression mutual block.
  This Lean-checked totality is the project's termination result for
  evaluation. Where KeY was more liberal, the interpreter follows solc
  (see `docs/solc-alignment.md`): checked `uint256`/`int256` arithmetic
  (`checkArith`), right-hand side before target with a single l-value
  resolution (`rhsToSVal`/`rhsToMVal`/`readLoc`/`writeLoc`), rejection
  of storage copies of mapping-carrying types (`tyHasMapping`), and a
  balance-checked, balance-debiting `transfer`.
- `StuckShape.lean`: the interpreter's counterpart of `Coverage.lean`'s
  `ResidueShape` — `StuckCause`, the documented list of reasons the
  interpreter answers `.error .stuck`, plus the halt taxonomy
  (`copyStToM_never_reverts`, `copyMToSt_never_reverts`,
  `getObj_never_reverts`) and the first leaf characterization,
  `find_stuck_iff`. Deliberately **no** Boolean mirror: unlike residue,
  stuckness already has a decision procedure — the interpreter. Leans on
  the wildcard expansion in `Semantics.lean`, which is what makes
  `SVal.find.induct` a case table with one hypothesis per arm.
- `SemanticsProperties.lean`: association-list, storage read-after-write,
  state-frame, allocation-freshness, heap-well-formedness, and recursive
  storage-to-memory copy-frame theorems.
- `RewriteSoundness.lean`: lifts local rule soundness through untouched block
  suffixes and reflexive-transitive derivations modulo scratch aliases.
- `Examples/Derivations/WorkedExamples.lean`: one `sol_derivation` chain per
  construct of the calculus, grouped by family — the end-to-end reading of the
  rule set, each chain starting at a Solidity program and ending at
  `solbox!{}`. The rule sequences are not written down at all:
  `sol_runs`/`steps!` ask `UniquenessAux.candidate` at elaboration time, so a
  rule rename or a changed residual is a build failure rather than 35 stale
  lists to re-derive. Recover a sequence with
  `set_option trace.solidity.steps true in …`. The exceptions are deliberate —
  the 18 single-rule derivations whose doc comment makes a point *about* that
  rule, and the three chains written out in full because the step-by-step
  shape is what they illustrate. Its closing section is the census of the four
  kinds of program that have no `sol!` spelling — call-valued arguments
  (`Stmt.callStmt` has no surface syntax), bare memory declarations, the
  first-order `sizeNotNegative` side condition, and the state-dependent
  unfunded transfer. Root of its own `SolidityExamples` target, **not**
  imported by `Solidity.lean` (≈30 min of CPU in pinned steps, about as much
  again as the whole default build); run `./scripts/check-examples.sh`.

- `Examples/Taclets/`: ports of the KeY taclet tests
  (`keyext.solidity.examples/taclets`) verified against the semantics.
- `Evm/Machine.lean`: EVM-style stack machine (instruction meanings follow
  NethermindEth/EVMYulLean; documented deltas: no gas, relative forward
  jumps, unbounded stack, arithmetic `MAPSLOT` in place of Keccak slot
  derivation, no value-transfer instruction — the balance is the
  reserved storage word `balanceSlotW`), `Step`/`Steps`/`Reverting`,
  `codeAt`, determinism and runner-soundness lemmas, fuel runner `run`.
- `Evm/Compile.lean`: Solidity-AST → EVM compiler for the verified
  fragment (stack locals via `DUP`/`SWAP`, one slot per primitive global
  root, derived slots for mapping entries and array elements, machine
  bounds checks for array accesses, `push`/`pop`, jump skeletons for
  control flow, zero-divisor guards, overflow guards for `uint`
  `+`/`-`/`*` (`uintChecked`/`checkedOpCode`/`binopTail`), and the
  balance-checked `transfer` (`transferTail`, reserved balance word
  `balanceSlotW` beside the net-ledger region `netSlotW`)); partial —
  `none` = outside the verified fragment.
- `Evm/BoundedSemantics.lean`: uint256-bounded mirror `evalW`/`execW`/
  `execWBlock` of the official interpreter plus the `*_agree` theorems
  tying its `.ok`/`.revert` outcomes to `Semantics.evalValue`/`execStmt`/
  `execBlock`. `applyCheckedW` is the shared operator step: on the
  compiled-guarded `uint` `+`/`-`/`*` it *is* the official
  `applyBinOp >>= checkArith` (overflow reverts), elsewhere the
  word-bounded `applyBinOpW >>= checkArithW` (`.stuck` = no claim); the
  `transfer` arm reverts on an insufficient balance like the official
  semantics and is stuck only on a negative amount or a ledger entry
  leaving `[0, 2^256)`.
- `Evm/Correctness.lean`: semantic preservation (Leroy-style forward
  simulation): `ReprVal`/`ReprSVal`/`ReprRoot`/`ReprState` (the latter
  carrying the net ledger and the balance word, `ReprState.balance`),
  `checkedOp_sim`/`binopTail_sim` (the overflow guards, via
  `mul_overflow_iff`), `compileExpr_sim`, `compileStmt_sim`/`compileBlock_sim`, headline
  theorems `compile_preserves_ok`/`compile_preserves_revert`, verdict
  uniqueness, the verified-inlining corollaries
  (`compileProgramInlined`, `compileInlined_preserves_*`), and the
  judgment-transfer theorems (`compileJudgment`, `judgment_transfer`,
  `judgment_transfer_revert`). See `docs/compiler-verification.md`
  § "Verified EVM compilation".
- `Evm/Examples.lean`: `native_decide` differential tests (interpreter vs.
  machine on compiled code — primitives, mappings, arrays, struct
  fields, transfers incl. insufficient-balance reverts, `uint`
  overflow reverts and boundary successes, inlined calls; the checker
  compares storage roots, the net ledger and the balance word) and
  concrete instantiations of the preservation and judgment-transfer
  theorems (`overflowProg_preserved`, `transferRevertProg_preserved`
  among them).
- `Spec/Assertion.lean`: the SolSpec assertion layer — total readers
  over `Semantics.State` (`intAt`/`boolAt`/`lenAt`/`localInt`), range
  predicates, the annotated block `Ann` (statement / ghost `assert` /
  ghost `assume`) and its verification conditions `vc`/`totalVC`/
  `partialVC`/`revertsVC`, plus the two meta-theorems relating them.
- `Spec/Tactic.lean`: `sol_spec`, the verifier for those obligations.
  Unlike `sol_wp` it runs over a *symbolic* initial state, so it splits
  the branches the interpreter cannot settle and finishes with `omega`.
  The finisher runs under `try`, so an unclosed goal is reported as
  "unsolved goals" rather than a tactic failure.
- `Spec/Syntax.lean`: the specification language as the `solspec!`
  notation — `solspec!{ requires … ensures … modifies … < body > }`
  elaborates to a `State -> Prop` (`Spec.Obligation`); `[ body ]` is the
  partial reading, as in `sol!`. It is its own notation, not another
  `sol!` form, because the two say different things, but it reuses the
  grammar: the body is `sol_stmt` (through `sol_ann`), clause
  expressions are `sol_expr` (through `sol_prop`), and a path with no
  specification-level index goes straight to `sexpr!`. `sol_prop` adds
  only unparenthesized comparisons, `==>`/`<==>` and bounded
  quantifiers; `old(e)` is intercepted from the call syntax. Same
  clauses and same reading as the `.sol` front-end; the difference is
  name resolution, which here goes through `SoliditySyntax.rootExpr`
  (use `name@@Type` for a root it does not know).
- `Spec/SyntaxExamples.lean`: `#check` smoke tests for every clause form
  (grammar only) followed by proved specifications (tactic too), so a
  parser problem and an automation problem are distinguishable.
- `Spec/Metatheory.lean`: the two results relating the modalities
  (`totalVC_imp_partialVC`, and `not_totalVC_of_revertsVC` on
  `assume`-free bodies). Kept out of `Assertion.lean` on purpose: the
  tactic — and therefore the extension — depends on `Assertion.lean`,
  which should carry only definitions and their computation rules.
- `Spec/Examples.lean`: the worked obligations of `docs/spec-language.md`,
  written by hand in exactly the shape
  `vscode-extension/src/spec/emitLean.ts` generates — the reference for
  the code generator.
- `SoliditySpec.lean`: root of the `SoliditySpec` Lake target
  (the six `Spec/` modules). Deliberately *not* imported by
  `Solidity.lean`, like `SolidityCorpus`; built by
  `./scripts/check-spec.sh`.
- `StorageTyping.lean`: storage-layout typing (`Layout`, `SVal.hasTy`,
  `wtStorageExpr`, `stmtTypingOk`), the read-typing lemmas
  (`resolveS_wt_tyAt`, `findStorage_hasTy`, `generic_read_hasTy`), and
  the *runtime* sorts `SVal.keySort`/`MVal.keySort` (every tree node is a
  `Struct`, every storage value `≤ StValue`, every memory value
  `≤ MemValue`; on primitives they agree with `Ty.keySort`).
- `StoragePreservation.lean`: the write-side twin of the read lemmas —
  `save_hasTy` (mirror of `find_hasTy`), `State.saveStorage_wellTyped`
  (under `nodupKeysB L.globals`, which is genuinely necessary),
  `SVal.defaultOf_hasTy`, `defaultOk`/`defaultForTy_hasTy` (the
  `defaultForTyFuel` fuel bound is real), `int_hasTy_numeric`,
  `applyBinOp_arith_int`, `writeLoc_storage_frame`.
- `StateTyping.lean`: the full-soundness invariants — binding context
  `Ctx`/`BTy`, shallow store typing `HeapTy` with `MVal.hasTyH`/
  `MObj.hasTyH` (refs checked against `H`'s claim only, no
  coinduction), `heapTypedB`, `envTypedB` (which also forbids stray
  `spath`/`mref` bindings), the packaged invariant `StateWT`,
  weakening (`HeapTy.Extends`, `_mono` lemmas), the general
  well-annotatedness check `wtExpr`, and the cross-domain copy typing
  (`copyMToSt_hasTy`, `copyStToM_typed`/`CopyOut`,
  `allocDefault_typed`).
- `TypeSoundness.lean`: type soundness of the interpreter. Part 1: the
  expression mutual block preserves `StateWT` with results inhabiting
  their annotations (`resolveS_wt`/`resolveMBase_wt`/`readM_wt`/
  `resolveLoc_wt`/`evalValue_wt`/`evalInt_wt`, one `mutual theorem`
  block on the interpreter's own `4*size+rank` measure; `H` is fixed —
  nothing in the block allocates), plus `readLoc_wt`/`writeLoc_wt` over
  `LocTy`. Part 2: the context-threading checker `stmtWt`/`blockWt`
  and the headline `execStmt_sound`/`execBlock_sound` — **storage
  well-typedness is an inductive invariant of execution** (the
  `wellFormed(storage)` theorem), with corollaries
  `execBlock_preserves_wellTyped`, `run_then_find_int`,
  `step_then_read_hasTy`. v1 scope notes live in the docstrings
  (`ite` branches may not net-declare; memory `delete` and `.length`
  reads excluded; `callStmt` stuck by design).
- `Counterexamples/PreservationNecessity.lean`: "only provable with
  wellformed" — nine refutations, each dropping exactly one invariant
  conjunct or side condition (entry storage typing, env typing,
  `defaultOk` fuel, `nodupKeysB` layouts, heap typing, `op.isArith`,
  `nodupKeysB Γ`, `nodupKeysB H`, `HeapWellFormed`), each next to a
  positive twin, plus a concrete 42-program demo showing the headline is
  not vacuous. Seven refute the headline `execStmt_sound` itself; R4 and
  R8 refute the fixed-typing lemmas (`saveStorage_wellTyped`,
  `setObjField_wt`). `heapTyNodup` is *not* needed by the headline:
  `execStmt_sound_dupHeapTy` proves it without that conjunct, via
  `dedupKeys` (StateTyping.lean), since `HeapTy.Extends` reads through
  `lookupBy`.
- `DecEq.lean`: the hand-written `DecidableEq SVal` (nested inductive;
  deriving fails on this toolchain) and the derived `MObj`/`State`/
  `Except` instances — shared by every module that closes a concrete
  interpreter run by `native_decide`.
- `Reachability.lean`: **tightness** of `wellFormed(storage)` — the
  third property after sufficiency (`TypeSoundness`) and necessity
  (`PreservationNecessity`): is anything *missing*? `Reachable L s`
  (some `blockWt`-checked program produces `s` from `initialState L`,
  the all-defaults state, whose `StateWT` proof `initialState_wt` is
  the missing base case of "assume `wellFormed` once");
  `reachable_wellTyped` (⇒ preservation); `SVal.canonical` = `hasTy`
  plus the three facts execution keeps and `hasTy` forgets (mapping
  default is the type's default, mapping keys unique, struct carries
  exactly its declared fields); `writeProg` builds any canonical
  storage by literal assignments / `push()` / `delete`; headline
  `storage_tight`, `canonical_reachable`, `no_hidden_invariant` (any
  storage property that holds initially and is preserved by well-typed
  programs *from well-typed states* already follows from `canonical`).
  All of these take `layoutOkB L` (nodup roots, nodup `structDef` rows
  for every reachable struct, nesting depth ≤ 8), including
  `initialState_wt`.
  `Witness.uint_negative_reachable` shows `uint` range is *not* an
  invariant (`total = -5;` is well-typed). Open, like
  `BlockStep.wellFounded`: `reachable ⇒ canonical` (the two
  `_not_reachable` witnesses carry a documented `sorry`).
- `WellFormedConsumers.lean`: the table of facts the taclets *consume*
  from a symbolic storage (`pop`'s `size ≥ 0`, index bounds ⇒ read
  succeeds / out of bounds ⇒ revert, unwritten mapping key reads the
  default, declared struct field is never stuck, `delete` keeps
  canonicity), each proved from `wellTypedStorageB`/`canonicalStorageB`,
  with the two `native_decide` twins showing which rows need the
  canonical conjuncts. A row that cannot be proved is a missing
  conjunct — the operational "nothing missing" check. Row C6 is proved
  at the value level only (`SVal.defaultOf_canonical`); its state-level
  form `saveStorage_canonical` is the `delete` instance of the open
  "reachable ⇒ canonical" direction and is a stated, documented `sorry`.
- `docs/lean-key-rule-map.md`: the name-by-name map between this rule set and
  solkey's taclets, plus the open naming drift. It is prose, not a checked
  table — the mechanical check in that direction is `lake exe solkeycheck`.

- `TacletAnnotations.lean`: proof-free table of the solkey taclets'
  read-sort annotations (`fixed s` for a `KeySort` written into the taclet
  — `find<[int]>`, `find<[Struct]>`, and the sort-free `find<[StValue]>`
  as `fixed .stValue` — or varcond-generic), transcribed from
  `solidityProgramRules.key`.
- `KeyTacletParser.lean`: token-level `.key` scanner + `conforms`
  cross-check of the annotation table against the live file.
- `SortFaithfulness.lean`: `SortFaithful` + `sortFaithful_all` — every
  annotation row's sort claim proved against the interpreter (a `fixed s`
  read claims `(v.keySort).le s`), except the explicitly listed
  `openFindings`. `SortFaithful` bites only on storage-domain `value`
  reads; `rows_accounting` (decided against the table) records what the
  headline really covers: of 74 rows, 48 carry a content-bearing claim,
  6 only claim-free `find<[StValue]>` reads, and 20 (memory, `net`,
  `length`/`dflt`-only) are vacuous for it and token-checked by
  `solkeycheck` alone.
- `Counterexamples/PreFixSortAnnotations.lean`: refutation of the
  pre-`12e72a1b4b` annotations (the caught sort bug) and of the
  `openFindings` rows.
- `Counterexamples/StaticRuntimeSort.lean`: the static sort of an array or
  mapping type (`uint[]`, `mapping(K => V)`, below `StValue`) is not the
  runtime sort of its value (a `Struct` node), so a `\hasSort` bound of
  `StValue` (`alphaSt`) on such a path would bind a sort no `selectSt`
  rule consumes; latent while the corpus binds only `alphaPrim`.
- `Counterexamples/DeleteFamilyGenericOverlap.lean`: first-order
  inconsistency proofs (`5 = 7`) for the `0f9b99ad55` delete
  fallthroughs, whose `alphaSt` bound admitted `Struct` and overlapped
  the dedicated `Struct` rules; solkey `e67a0d7c48` re-bounds them by
  `alphaPrim` exactly as the proofs demand. Also records the surviving
  gap: `StValue`-instantiated delete reads (delete-then-copy) are
  stuck terms.
- `Counterexamples/WellTypedNecessity.lean`: `SortFaithfulUntyped`
  (`SortFaithful` minus `wellTypedStorageB`) refuted on the live
  `storageRootReadSelect` row that `sortFaithful_all` proves — the
  well-typedness hypothesis is exactly the boundary; the module
  docstring carries the calculus-side answer (sorts are sound without
  any wellformedness, via underspecified casts; completeness about
  `size` cells is what needs a `wellFormed(storage)` assumption).
- `SolkeyCheck.lean` (root): `lake exe solkeycheck` — runs the
  `conforms` check against a solkey checkout (`scripts/check-solkey.sh`;
  default `../solkey`, override with `--key`/`SOLKEY_RULES`; a missing
  checkout is a warning and exit 0).
  Run it after touching `TacletAnnotations.lean` or when solkey's rule
  file changes; `--list` dumps the parsed reads for updating the table.
  **Currently failing, and pre-existing**: the table has drifted from
  upstream by 78 rows against the live checkout (storage-index taclets split
  array/mapping and the root/decompose pairs merged; three read-sort changes;
  the whole memory-arithmetic family).  Re-syncing it is its own change,
  because it also moves `SortFaithfulness.lean` and
  `Counterexamples/PreFixSortAnnotations.lean`.
- `Solidity.lean`: root import file — add new modules here.

When adding a rule: one `sol_rule` declaration, under the section the
`Rules.lean` banners name.  Declaration order *is* the order of `RuleName`,
`ruleEffect` and `ruleNames`, so put it where it belongs and write a box
twin before its diamond twin (`twins` does both at once and fills
`twinPairs`, which `CandidateStep.twins_box_first` checks; `FirstStepCase`
takes the first applicable rule under `.both`, so the order decides which
name a `⇝[.rule]` derivation pins).  A parameterized family
(`(op : BinOp)` and friends) expands to every instance in `ruleNames` on its
own — classification requires them all, so give a KeY-absent instance an
unsatisfiable guard conjunct.  Then add the `candidate` dispatch branch and
the `applicable_eq_candidate` case in `Uniqueness.lean`; if the rule has a
non-empty residual block, also add a validation entry in
`RuleValidation.lean`.
The condition is generated from the schema variables' *names*
(`RuleSyntax.schemaVar`), so `sp.fld = se` already says
`isSimple sp ∧ isSe se`; `where` appends the conjuncts no name carries and
`where cond := …` replaces the conjunction outright.  Reach for
`sol_rule NAME … := <term>` only where the goals consume the condition
proof or the condition is a bespoke predicate — about ten of the rules.
Membership proofs over the large `ruleNames` list use `decide`
(`simp [ruleNames]` exceeds the recursion limit).
A generated `ruleEffect` arm never has a catch-all `| _ => []`: `block` is
dependent on the condition proof, so pass that proof as a second match
discriminant and list only the arms the `cond` admits — the match compiler
refutes the rest, because the proof's type reduces to `False` there. An empty
residual therefore means *terminal rule* and nothing else. See the `StepEffect`
docstring for the two wrinkles (a `(lhs : WrappedExpr)` scrutinee has to
destructure the place, `match lhs, h with | ⟨PAT, _⟩, _ => …`, because the
condition reaches `block` as an unreduced beta-redex).
If the KeY taclet reads storage/memory (`find`/`read`/`selectSt`/
`valAt`/`defaultValue` tokens), also add or extend its `TacletReadAnn`
row in `TacletAnnotations.lean` and make sure `sortFaithful_all` still
closes (extend `ruleNumericTarget`/`ruleRefTarget` in
`SortFaithfulness.lean` for new `fixed`-sorted value reads); then run
`lake exe solkeycheck` against the solkey checkout.

## Never abandon the `sol!` notation

Derivations are written in the surface notation — `solbox!{ … }`,
`soldiamond!{ … }`, `solboth!{ … }`, `sol!{ < … > (post) }` — and that is the
point of them: a `calc` chain is meant to read as the symbolic execution a
reader could follow by hand. **Do not "fix" a derivation by spelling its
residual out as raw constructors** (`⟨.box, [ sstmt!{ … }, Stmt.assign … ]⟩`,
`SolidityJudgment.mk (SolidityBlock.mk .diamond […])`). That is not a smaller
edit, it is the deletion of the artefact.

When a rule's residual changes and a `calc` step stops elaborating, the cause is
almost never the notation. In order of likelihood:

1. **The residual really is different** — more steps, not different syntax. A
   frozen value operand adds `uint rv = e;`, which costs three steps
   (`localValueDeclInitDrop` → `valueDeclSkip` → `localValueAssign`), each still
   perfectly writable as `solbox!{ … }`. Write the extra steps — or collapse
   them into one `⇝*` line with the rules listed (see below).
2. **A scratch name has no explicit `rootExpr`/`rootPlace` arm.** The default
   arm gives the right term but leaves `decide` goals unreduced, so a step
   tactic fails for a reason that looks like a parse problem and is not. Fix it
   by adding the name to the explicit-arms list in `AST.lean` (that is what
   `"rv"` and `"idx"` are doing beside `"result" | "x" | "y" | "to"`), not by
   dropping to constructors.
3. **The grammar genuinely lacks a form.** Check `syntax … : sol_stmt`
   (`AST.lean:1306-1338`) before concluding this — it already covers bare
   declarations (`uint rv`), plain assignment, every compound operator,
   `push`/`pop`/`delete`, `predec`/`postdec`, and the `.. name` context splice.
   If something really is missing, *extend the grammar*; an escape hatch used
   once becomes the house style.

`Examples/Common.lean`'s `rvExpr`/`idxExpr`/`spExpr` family exists for residuals
whose type is not fixed, not as a general substitute for the notation.

### The rewrite arrows

`Examples/Derivations/` writes symbolic execution as a chain of arrows:

| Lean | Means | Relation | Proof |
|---|---|---|---|
| `b ⇝ b'` | one rewrite step | `BlockStep` | `block_step` |
| `b ⇝[.rule] b'` | one step, by that named rule | `NamedBlockStep` | `rule_step` |
| `b ⇝* b'` | zero or more steps | `BlockReflMultiStep` | `steps [.r₁, .r₂, …]` when the rules are worth reading, `steps!` when they are not |
| `j ⇝ᵈ[.rule] j'`, `j ⇝ᵈ* j'` | the same, on a full judgment | `NamedJudgmentStep` / `JudgmentMultiStep` | `dl_rule_step` / `dl_steps […]` |

Four consequences for how derivations are written:

1. **The rule goes on the arrow, not in the proof.** `NamedBlockStep` takes the
   `RuleName` as an index, so `⇝[.storageFieldWriteSave]` is a claim Lean
   checks. Do not re-list the rules in a docstring above the derivation — that
   duplication is what the index removed.
2. **Elide administrative runs with `⇝*`, and decide whether the rules are
   worth reading.** The `localValueDeclInitDrop` → `valueDeclSkip` →
   `localValueAssign` trio that every frozen value operand costs is one `⇝*`
   line. Two ways to discharge it:

   - `steps [.r₁, .r₂, …]` — the rules are part of what the derivation is
     *showing*. This is the right choice in `Examples/Derivations/`.
   - `steps!` — the rules are bookkeeping nobody should read. It asks
     `UniquenessAux.candidate` (a total computable dispatch that reduces in
     the kernel) for the rule at each step and then discharges it by the
     *same* pinned route, so the emitted proof is identical and only the
     typing of the name moves out of the source. `candidate` is an oracle,
     not an authority: `find_pinned_step` still proves the rule applies, so
     the one case where it overreaches (`Coverage.lean`'s `pushRhsStorageB`)
     fails loudly. No new axioms — in particular no `native_decide`.

   `steps_search!` is the *old* blind loop, which really does walk all ~190
   entries of `Rules.stepCases` per step; keep it only as the oracle-free
   fallback. To see what `steps!` picked:
   `set_option trace.solidity.steps true in …`, or write `steps?` for a
   pasteable `steps [...]` suggestion.
3. **Name the inactive suffix instead of retyping it.** A trailing
   `.. name` splice in any block macro means `[…] ++ name` — the inactive
   `omega` context, with `name` an `abbrev … : Block := sblock!{ … }`. Write
   the suffix out again once it becomes the active statement.
4. **Multi-step block derivations are written with the `sol_derivation`
   command** (`Examples/Common.lean`), which is the chain and nothing else —
   no `calc`, no per-line `:= by …`, and a `where` clause for the
   "Let ℓ = …" abbreviations:

   ```
   sol_derivation rootPostincrementProgram :
       solbox!{ age = 10; age++; result = age }
     ⇝[.storageRootWriteStore]       solbox!{ age++; result = age }
     ⇝[.storageRootIncDec .postInc]  solbox!{ result = age }
     ⇝[.storageRootReadSelect]       solbox!{}
   ```

   It states `theorem <name> : <first> ⇝* <last>`, so each derivation is a
   named, reusable fact rather than an anonymous `example`. Single steps stay
   as `example : A ⇝[.r] B := by rule_step`.

   When the point is only *that* a program runs to the empty block, use
   **`sol_runs`** instead — the modality named once, no `solbox!`, no target,
   no rules:

   ```
   sol_runs deepFieldWrite { alice.account.balance = amount }
   sol_runs arrayRead diamond { result = values[i] }
   ```

   Statements are `;`-separated inside braces, deliberately: newline
   separation parses, but postfix `++` and the call form `ident(…)` reach
   across a line break, and the resulting misparse is *silent* — the merged
   program still reduces to the empty block, so the theorem would be true and
   about a different program. There is no judgment-level
   counterpart yet: `Derivations/DynamicLogic.lean` writes its `⇝ᵈ` chains as
   plain `calc` with `dl_rule_step`/`dl_steps`.

Two scratch-name notes, because both used to force raw constructors:

- **The capture rules' `pv` is a *stack* variable; spell it `pv@uint` /
  `pv@bool`** (likewise `rv@uint`, `idx@uint`). A bare `pv` is a storage
  alias and `SoliditySyntax.aliasKind` is a name-only table that cannot see
  the type, so the kind is decided in the `sol_expr` expanders via
  `SoliditySyntax.isStackScratchAlias`. A *reference*-typed `pv@Account` is
  still the memory path alias it always was.
- **`--` cannot be a Lean token** (it starts a comment), so a decrement is
  `predec(e)` / `postdec(e)`. That is surface notation, not an escape hatch:
  `solbox!{ postdec(age) }` is the `IncDec.postDec` statement.

Keep imports acyclic and local: syntax in `AST.lean`, rule enumeration in
`Rules.lean`, proof relations in later files. Validate edits with MCP
diagnostics/goals first, then run the relevant Lake build if useful.

## `grind`

This project (Lean 4.24.0, see `lean-toolchain`) has `grind` built in. Try `grind` (or
`grind [lemma1, lemma2]`) before long manual scripts for equality propagation,
propositional facts, case splits, E-matching, and linear arithmetic. Tag safe
reusable lemmas `@[grind]` when they don't blow up the search space. For
combinatorial Boolean/bitvector goals prefer `bv_decide`/`omega`/structural
steps. If a `grind` proof is slow or brittle, inspect the goal via MCP, pass
only needed lemmas, or fall back to smaller `simp`/`cases`/`omega` steps.
