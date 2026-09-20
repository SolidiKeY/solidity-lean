# Module map

One line per module: what it defines and why it exists. Open the module's
own `/-!` docstring for the detail; this file is the index, not a summary of
them. Modules not listed here are examples or small helpers whose name says
what they are.

Open problems are flagged **OPEN** inline. Layering: syntax in `AST.lean`,
rule enumeration in `Rules.lean`, proof relations in later files. New modules
go in `Solidity.lean`.

## The calculus

| Module | What it is |
|---|---|
| `KeySort.lean` | solkey's sort lattice as one Lean type: `parents`, `ancestors`, `KeySort.le`, KeY spellings. The *only* model of the lattice. Array/mapping sorts sit directly below `StValue`, siblings of `Struct` (not below it). Imports nothing. |
| `AST.lean` | Solidity syntax; the `sol!` notation and its `sol_stmt`/`sol_expr` grammars. `Ty.keySort` mirrors the KeY hierarchy structurally; `Field.sort = ty.fieldSort` is *computed*, so a field cannot be classified against its own type. Old constructor names survive as `@[match_pattern]` abbrevs. Holds the struct table `Semantics.structDef`, its rank certificate and `Semantics.tyHasMapping` (solkey's `StorageReferenceTypes.containsMapping`), so `TypedStmt.Assign.mk` can refuse a storage-to-storage copy of a mapping-carrying type (`mapFree`), as solc ≥ 0.7 and `ParserUtils.parseAssignmentMaybe` do. |
| `KeyTaclets.lean` | The 252 taclets of `solidityProgramRules.key` as one type, plus `\heuristics` sets and `KeyOrigin`. Regenerate with the `awk` recipe in its docstring. Imports nothing. |
| `RuleSyntax.lean` | The `sol_rule` declaration syntax and `sol_assemble_rules`; carries the schema-variable table (`schemaVar`). Imports `Lean` only. |
| `Rules.lean` | One `sol_rule` per rule, organised by family. A rule is a taclet, not a rewrite: `StepEffect` carries `goals` (guard, update, residual), read as KeY's weakest precondition. Update syntax here is AST-only. |
| `RuleShapes.lean` | Structural checks: `mainBlock` reduction, `goals_nonempty`, `taclets_partitioned` (246 of 252 claimed, six listed with a reason), `twins_origin_eq`, `heuristics_eq_origin`. |
| `Completeness.lean` | `FirstStepCase`/`RuleStep` and the bridge `RuleStep.step_of_ruleApplies` with its converse. |
| `Coverage.lean` | `candidate_applies`, the syntactic `ResidueShape` (24 shapes no rule covers), and `RuleStep.complete_of_wellTyped` over the rule-independent fragment. |
| `Uniqueness.lean` | Rule mutual exclusion via the total dispatch `candidate` (`applicable_eq_candidate`). `RuleSetDisciplined` carries exactly three facts. A failing uniqueness build signals a condition overlap. |
| `Progress.lean` | Progress is **false** here and this proves it (`symbolicIte`, `not_progress`), plus the judgment-layer split that handles it. **OPEN**: `BlockStep.wellFounded` is a documented `sorry`. |
| `MultiStep.lean` | `BlockStep` (`⇝`), `BlockReflMultiStep` (`⇝*`), `NamedBlockStep` (`⇝[.rule]`) and the `Trans` instances. Framing (`appendStmts`, `append_suffix`, `inContext`, and the rule-level `NamedBlockStep.inSuffix`): a chain carries a *suffix*, and a prefix is consumed rather than carried, because `⇝` fires at the head. |
| `Termination.lean` | Termination-certificate interface. **OPEN**: the concrete all-rules certificate. |
| `RuleValidation.lean` | Per-rule `native_decide` validation of unfold rules against the executable semantics. |
| `RuleSoundness.lean` | `<rule>_sound` per unfold rule: residual agrees with the original modulo scratch aliases. **OPEN**: `functionCallArgCapture_sound_inlined`, and one case each of `storagePushValueUnfoldRightSndArgument_sound` / `memoryWriteUnfoldRightSndResult_sound`. |
| `RewriteSoundness.lean` | Lifts local soundness through untouched block suffixes and `⇝*`. `BlockExecAgree.append_left`/`append_right` are the context congruence the rewrite layer cannot have — unconditional on a prefix, freshness-guarded on a suffix. |

## The data-structure theories

solkey's `find`/`save`/`read`/`write` are uninterpreted symbols whose meaning
is a taclet set. These modules are that theory as terms, with each taclet a
theorem and, for the memory algebra, a denotation into the interpreter
(`Update/Theory.lean`).

| Module | What it is |
|---|---|
| `Theory/Storage.lean` | `structRules.key`'s taclets, over `Theory/Terms.lean`'s sorts. Stated about **`findSt`**, the read that does not cross into memory, because that is the reader `structRules.key` has — `copyMem` is declared in `structMemoryRules.key`. `save`, `storeAt`, the delete family and `diverges` are here. Every taclet a theorem, in the *pre-fold* shape: the leaf of a write collapses (`saveOnEmpty`, `saveOnStoreCons` with its `isEmpty(flds)` split, `selectOnSaveEmpty`), because the copy on which solkey's non-collapsing leaf differs — a storage-to-storage copy of a mapping-carrying type — is not a statement (`TypedStmt.Assign.mk`). `storeAt` is the one-segment walk; `selectOnSaveCons` with no well-formedness hypothesis; the four `find`-over-`save` laws (`find_save_same`/`_extends`/`_prefix`/`_frame`) plus `find_append` — `Semantics` had only the first. The delete family is eager (`delNode`/`delValue`/`delAt`) and states every `selectStDelNode*` rule but `Map`: a `Seg` carries no `MapField`, so the mapping-preserving `delete` is the interpreter's alone. No pre-state leaf and no denotation: it is a theory over free terms, as upstream's is. |
| `Theory/Memory.lean` | `memoryRules.key`'s taclets, over `Theory/Terms.lean`'s sorts, plus the `new` predicate. Every taclet a theorem, including the chain-walking family (`readREmpty`, `readRCons`, `idCCDef`, `defaultDefIdentity`) and `newFromAdd`/`readOnAddM` in KeY's branching form. Resolving a path identity against a heap is the denotation's job (`Update/Theory.lean`). `copySt`/`copyMem` are `Theory/CrossDomain.lean`. |
| `Theory/Terms.lean` | The sorts, because `structMemoryRules.key` ties the other two files together: `copyMem` is a `Struct` constructor and `copySt` a `Memory` one, as KeY declares them, so `Struct`/`StValue`/`Memory` are one mutual inductive. With them the readers that are mutual for the same reason — `selectSt`, `findSt` (the storage read that stops at a view), `find` (the one that crosses into `readR`), `readIn`/`readId`/`readR`/`readRId`, and the path-identity resolver. All structural: the cycle is cut by `readIn` reading its copied struct with `findSt`, so every equation stays `rfl` and a closed term reduces in the kernel, which is how half the taclets are checked. `Struct.inductionOn`/`Memory.inductionOn` are the one-sort recursors a mutual inductive does not give. |
| `Theory/CrossDomain.lean` | `structMemoryRules.key`'s four taclets on those sorts: `findCopyMem`, `readCopySt`, `readCopyStIdentity`, `readCopyStOther`. `readCopyStIdentity` falls out of `defaultDefIdentity` because a copied struct member reads as `dflt`. Not modelled: a view nested in a view — `StValue.find_eq_findSt` is where that is stated, and no worked example nests one. |
| `Theory/Rewrite.lean` | The theory layer's answer to `Rules.lean`: `TheoryRule`, one constructor per rewrite rule of the paper's signature, under **the paper's** name rather than KeY's, and `lemmaNames` saying which theorem each one is at each sort. What lets a `sol_rewrite` line write `=[.findOnSave]` and have it checked. `#theory_rules` prints the table; `./scripts/check-theory-rules.mjs` checks it against the paper's `\namedRwRule` declarations. |
| `Update/Theory.lean` | A rule's stated *memory* update read as a KeY term: `heapRhs_eq_theory` over `Rules.MemTerm`, covering a `write` on the `memory` variable — `addM`/`copySt` are not read back, because denoting them means reconciling KeY's lazy allocation with `Semantics.allocDefault`'s eager one; `denoteMem`/`denoteMV` resolve a path identity against the heap, and `denoteMem_new` discharges KeY's freshness premise. The storage half is gone with `Theory/Storage.lean`'s pre-state leaf: what it reconciled — solkey's mapping-keeping leaf against the interpreter's plain write — differs only on a copy the AST cannot express. |

## Updates and the sequent layer

| Module | What it is |
|---|---|
| `Update.lean` | The symbolic-update algebra: `Elem`, `Par`, `Upd.seq`, and the merge law `Par.seq_single`. |
| `Update/Eval.lean` | What an `UpdTerm` means; every reader is one of `Wp/Terminal/Table.lean`'s. |
| `Update/Wp.lean` | The wp reading, `guard → {update}⟨residual ++ rest⟩post` per goal. |
| `Update/TacletTable.lean` | `goalsExec … = terminalUpdate r …` per rule. 21 bridged; the rest listed in `openBridges` with a reason. |
| `Update/Bridges.lean` | `Par.toUpd [...] = <family> args`, built on frame facts. Coverage list in its docstring. |
| `Update/Step.lean` | The derivation line `Γ ⟹ {U₁}…{Uₙ} goal`, `Frontier`, `NamedFrontierStep`, `Frontier.Equiv` (the merge line). Arrows `⇝ᵘ`, `⇝ᵘ*`, `⇝ᵘ[r]`, `≡ᵘ`. |
| `Update/SequentSyntax.lean` | The `seq!{ … }` surface notation and the `=>` derivation line (`sol_line`), including the paper's bare `(φ)` goal. |
| `Update/Merge.lean` | Reader lemmas a merge line needs, all `@[upd_merge_set]`. |
| `Update/Examples.lean` | The headline chain's last two lines, written out of `Upd.Elem` functions. |

`Update/Step.lean` also carries `CalculusHolds`: the rule table drives a
program to a frontier with no statement left, and that frontier holds at a
store. That is what a proof *by the calculus* is, as opposed to `sol_wp`,
which is the interpreter. `Frontier.isClosed` is the conjunct that makes it a
claim — `⇝ᵘ*` is reflexive, so without it the start frontier is its own
witness.

## Weakest preconditions

| Module | What it is |
|---|---|
| `Wp/Monad.lean` | The interpreter as `SolM`, and the two modalities as one wp each (`Box.wpB`, `Dia.wpD`). Both *defined* by the shape their `_run` lemma states. |
| `Wp/Verdict.lean` | `checkResult` and `check_eq_checkResult`. |
| `Wp/Terminal/Table.lean` | The state update of every terminal rule in the interpreter's state vocabulary, never through its evaluators. `terminalUpdate?` is `some` for exactly the 83 terminal arms. |
| `Wp/Terminal/Vocab.lean` | Bridges from each interpreter evaluator to the vocabulary readers. |
| `Wp/Terminal/Update*.lean` | One `<rule>_update` theorem per terminal rule, **under the rule's guard**. |
| `Wp/Terminal/Soundness.lean` | `terminalUpdate_sound`, `TerminalRuleStep`, `terminal_step_sound`. Not proved: no unfold rule is accidentally terminal. |
| `EvalBattery.lean` | `sol_eval_battery` / `sol_exec_eval`; depend on the interpreter alone. |

## Semantics and typing

| Module | What it is |
|---|---|
| `Semantics.lean` | Run-time values and the executable state semantics; `SolidityJudgment.check`/`Holds`. Total, no `partial` — Lean checks termination. Follows solc where KeY was more liberal (`docs/solc-alignment.md`). The struct schema and `tyHasMapping` live in `AST.lean`. `SVal.array` carries the slots a `pop` cleared and gave back beside the live elements, and `pushSlot` is upstream's `delAt` at the pushed slot: a mapping nested in a popped element survives into the next `push`. |
| `Semantics/Properties.lean` | Association-list, read-after-write, frame, allocation-freshness, copy-frame theorems. |
| `Semantics/StuckShape.lean` | `StuckCause`, the halt taxonomy, and `find_stuck_iff`. Deliberately no Boolean mirror. |
| `Typing/Storage.lean` | `Layout`, `SVal.hasTy`, read-typing lemmas, and the runtime sorts `SVal.keySort`/`MVal.keySort`. |
| `Typing/StoragePreservation.lean` | The write-side twin: `save_hasTy`, `State.saveStorage_wellTyped`, `defaultForTy_hasTy`. |
| `Typing/State.lean` | The full-soundness invariants: `Ctx`, `HeapTy`, `StateWT`, weakening, `wtExpr`, cross-domain copy typing. |
| `Typing/Soundness.lean` | Type soundness: the expression block preserves `StateWT`, then `execStmt_sound`/`execBlock_sound` — storage well-typedness is an inductive invariant. v1 scope notes in the docstrings. |
| `Typing/Reachability.lean` | Tightness of `wellFormed(storage)`: `Reachable`, `SVal.canonical`, `storage_tight`, `no_hidden_invariant`. All take `layoutOkB L`. `canonical` is the **shadow-free** fragment — what `writeProg` can build, since it builds with assignments and pushes and never a `pop`. **OPEN**: `reachable ⇒ canonical` (two `sorry`s), now also because a popped array carries a recycled slot. |
| `Typing/WellFormedConsumers.lean` | The table of facts the taclets consume from a symbolic storage. **OPEN**: row C6's state-level form `saveStorage_canonical`. |
| `Semantics/DecEq.lean` | The hand-written `DecidableEq SVal` and derived instances; shared by every `native_decide`. |

## Sort faithfulness (the solkey cross-check)

| Module | What it is |
|---|---|
| `SortCheck/Annotations.lean` | Proof-free table of the taclets' read-sort annotations, transcribed from the `.key` file. |
| `SortCheck/Parser.lean` | Token-level `.key` scanner plus the `conforms` cross-check. |
| `SortCheck/Faithfulness.lean` | `sortFaithful_all`: every annotation row's sort claim proved against the interpreter, except the listed `openFindings`. `rows_accounting` records what the headline really covers. |
| `SolkeyCheck.lean` (root) | `lake exe solkeycheck`. **Known failing, pre-existing**: 78 rows of drift against the live checkout. Re-syncing is its own change — it also moves `SortCheck/Faithfulness.lean` and `Counterexamples/PreFixSortAnnotations.lean`. |

## Counterexamples

Each is a refutation that pins down why a hypothesis or conjunct is there.

- `EvaluationOrder.lean` — the pre-fix residual refuted; the current rules shown to agree on the same two programs.
- `ErrorOrder.lean` — why the freeze cannot be conditional on the path being impure (`unfrozen_not_sound`).
- `RefSourceOrder.lean` — what `hprim` carves out: it is the **interpreter**, not the rule, that is unfaithful to solc for a reference source. **OPEN**: make assignment target-first for reference sources, then drop `hprim`.
- `PreservationNecessity.lean` — nine refutations, one per dropped invariant conjunct, each with a positive twin.
- `PreFixSortAnnotations.lean` — the caught sort bug, and the `openFindings` rows.
- `StaticRuntimeSort.lean` — the static sort of an array/mapping type is not its value's runtime sort.
- `BinopOperandCapture.lean` — `binopUnfoldLeft` and `binopUnfoldRight` share
  one scratch name, so a binop with *two* nonsimple operands computes the
  right one twice. The rule table proves `r == 10` of a program that computes
  `10 + 5`; the interpreter refutes it. KeY's `*CaptureLhs` takes a
  `SimpleExpression` on the right and introduces two `\new` variables, which
  is why it does not have this. **OPEN**: the rule-table fix.
- `DeleteFamilyGenericOverlap.lean` — first-order inconsistency proofs for the `0f9b99ad55` delete fallthroughs; records the surviving gap.
- `WellTypedNecessity.lean` — `SortFaithful` minus `wellTypedStorageB` is false; well-typedness is exactly the boundary.
- `MappingSideConditions.lean` — the `tyHasMapping` side conditions of the storage-copy capture rules, each refuted if dropped: M3 in the capture template on a merely pure path, M4 on `storageIndexReadUnfoldRightSndResult`, where the path *and* index are simple — an index is evaluated, and a storage-kind index variable reads the store. M3/M4 are what only the simple-*field* rule does not need; the AST guarantees the hypothesis (`TypedStmt.Assign.mk`, `stmtTypingOk`), the witnesses are untyped `Stmt.assign` terms no front end produces.

## The EVM compiler

| Module | What it is |
|---|---|
| `Evm/Machine.lean` | EVM-style stack machine; documented deltas from EVMYulLean in its docstring. |
| `Evm/Compile.lean` | Solidity-AST → EVM for the verified fragment; partial, `none` = outside it. |
| `Evm/BoundedSemantics.lean` | The uint256-bounded mirror of the interpreter plus the `*_agree` theorems. |
| `Evm/Correctness.lean` | Leroy-style forward simulation: `compile_preserves_ok`/`_revert`, verified inlining, judgment transfer. See `docs/compiler-verification.md`. |
| `Evm/Examples.lean` | `native_decide` differential tests and concrete instantiations. |

## Examples

- `Examples/Derivations/Solkey/` — **the solkey corpus proved from `Rules.lean`
  alone** (`SolidityCalculus` target, generated by the same pass of
  `scripts/solkey-port.mjs` as `Examples/Solkey/`). One `sol_calculus` per
  obligation: `seq_closes` runs the taclets to a closed frontier and the
  endpoint is decided. Verdicts in `tests/solkey/expected-calculus.tsv`,
  scoreboard in `docs/calculus-parity.md`. Not in the default build.
- `Examples/Derivations/Paper.lean` — **the calculus's worked examples**: the conventions, and the imports of the five modules that hold the chains. Root of the `SolidityExamples` target, **not** in the default build (~30 min CPU); run `./scripts/check-examples.sh`.
- `Examples/Derivations/Paper/` — the chains themselves, written as the calculus writes them (`=> {U} <[ p ]>(φ) ~*> …`), update beside the shrinking program; rule sequences are computed, not written. `Storage.lean` (sections 1–4), `Memory.lean` (5–7), `CrossDomain.lean` (8), `Control.lean` (9–10), `Checks.lean` (the lines run against the interpreter). Which paper example each chain is, and which have none, is `docs/paper-parity.md`, checked by `./scripts/check-paper-parity.sh`.
- `Examples/Taclets/` — ports of the KeY taclet tests, verified against the semantics.
- `Examples/Solkey/` — the ported solkey corpus (`SolidityCorpus` target, generated by `scripts/solkey-port.mjs`).
