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
| `AST.lean` | Solidity syntax; the `sol!` notation and its `sol_stmt`/`sol_expr` grammars. `Ty.keySort` mirrors the KeY hierarchy structurally; `Field.sort = ty.fieldSort` is *computed*, so a field cannot be classified against its own type. Old constructor names survive as `@[match_pattern]` abbrevs. |
| `KeyTaclets.lean` | The 252 taclets of `solidityProgramRules.key` as one type, plus `\heuristics` sets and `KeyOrigin`. Regenerate with the `awk` recipe in its docstring. Imports nothing. |
| `RuleSyntax.lean` | The `sol_rule` declaration syntax and `sol_assemble_rules`; carries the schema-variable table (`schemaVar`). Imports `Lean` only. |
| `Rules.lean` | One `sol_rule` per rule, organised by family. A rule is a taclet, not a rewrite: `StepEffect` carries `goals` (guard, update, residual), read as KeY's weakest precondition. Update syntax here is AST-only. |
| `RuleShapes.lean` | Structural checks: `mainBlock` reduction, `goals_nonempty`, `taclets_partitioned` (246 of 252 claimed, six listed with a reason), `twins_origin_eq`, `heuristics_eq_origin`. |
| `Completeness.lean` | `FirstStepCase`/`RuleStep` and the bridge `RuleStep.step_of_ruleApplies` with its converse. |
| `Coverage.lean` | `candidate_applies`, the syntactic `ResidueShape` (24 shapes no rule covers), and `RuleStep.complete_of_wellTyped` over the rule-independent fragment. |
| `Uniqueness.lean` | Rule mutual exclusion via the total dispatch `candidate` (`applicable_eq_candidate`). `RuleSetDisciplined` carries exactly three facts. A failing uniqueness build signals a condition overlap. |
| `Progress.lean` | Progress is **false** here and this proves it (`symbolicIte`, `not_progress`), plus the judgment-layer split that handles it. **OPEN**: `BlockStep.wellFounded` is a documented `sorry`. |
| `MultiStep.lean` | `BlockStep` (`⇝`), `BlockReflMultiStep` (`⇝*`), `NamedBlockStep` (`⇝[.rule]`) and the `Trans` instances. |
| `Termination.lean` | Termination-certificate interface. **OPEN**: the concrete all-rules certificate. |
| `RuleValidation.lean` | Per-rule `native_decide` validation of unfold rules against the executable semantics. |
| `RuleSoundness.lean` | `<rule>_sound` per unfold rule: residual agrees with the original modulo scratch aliases. **OPEN**: `functionCallArgCapture_sound_inlined`, and one case each of `storagePushValueUnfoldRightSndArgument_sound` / `memoryWriteUnfoldRightSndResult_sound`. |
| `RewriteSoundness.lean` | Lifts local soundness through untouched block suffixes and `⇝*`. |

## The data-structure theories

solkey's `find`/`save`/`read`/`write` are uninterpreted symbols whose meaning
is a taclet set. These modules are that theory as terms, with each taclet a
theorem and a denotation into the interpreter.

| Module | What it is |
|---|---|
| `Theory/Storage.lean` | `structRules.key` as a term algebra: `StValue`, `selectSt`, `save`, `find`, the delete family. Every taclet a theorem; `selectOnSaveCons` with no well-formedness hypothesis. The four `find`-over-`save` laws (`find_save_extends`/`_same`/`_prefix`/`_frame`) — `Semantics` had only the first. Paths are `Seg`; `size` is `Seg.field "length"`. |
| `Theory/Memory.lean` | `memoryRules.key` as a term algebra: `Identity` (KeY's path identity `idC(idp, flds)`), `MemValue`, `Memory`, `readIn`, `readR`, `new`. Every taclet a theorem, including the chain-walking family (`readREmpty`, `readRCons`, `idCCDef`, `defaultDefIdentity`) and `newFromAdd`/`readOnAddM` in KeY's branching form. Resolving a path identity against a heap is the denotation's job (`Update/Theory.lean`). **Not** modelled: `structMemoryRules.key`'s `copySt`/`copyMem`. |
| `Theory/Denote.lean` | What a storage term means: `slotOf`/`putAt` (one step of `SVal.save`, split), `denoteSt`, and `denote_save` — the theory's `save` on the pre-state tree *is* `SVal.save`, errors included. `denote_find`, `denote_delAt`. No type parameter and no well-formedness predicate; the reasons are in the docstring. |
| `Update/Theory.lean` | A rule's stated update read as a KeY term: `storageRhs_eq_theory`, `heapRhs_eq_theory`; `denoteMem`/`denoteMV` resolve a path identity against the heap, and `denoteMem_new` discharges KeY's freshness premise. This is what makes every taclet above a fact about the wp semantics rather than about a private model. Push/pop and the copy rules deviate from KeY's spelling; the docstring says how and why. |

## Updates and the sequent layer

| Module | What it is |
|---|---|
| `Update.lean` | The symbolic-update algebra: `Elem`, `Par`, `Upd.seq`, and the merge law `Par.seq_single`. |
| `Update/Eval.lean` | What an `UpdTerm` means; every reader is one of `Wp/TerminalUpdate.lean`'s. |
| `Update/Wp.lean` | The wp reading, `guard → {update}⟨residual ++ rest⟩post` per goal. |
| `Update/TacletTable.lean` | `goalsExec … = terminalUpdate r …` per rule. 21 bridged; the rest listed in `openBridges` with a reason. |
| `Update/Bridges.lean` | `Par.toUpd [...] = <family> args`, built on frame facts. Coverage list in its docstring. |
| `Update/Step.lean` | The derivation line `Γ ⟹ {U₁}…{Uₙ} goal`, `Frontier`, `NamedFrontierStep`, `Frontier.Equiv` (the merge line). Arrows `⇝ᵘ`, `⇝ᵘ*`, `⇝ᵘ[r]`, `≡ᵘ`. |
| `Update/SequentSyntax.lean` | The `seq!{ … }` surface notation and the `=>` derivation line (`sol_line`), including the paper's bare `(φ)` goal. |
| `Update/Merge.lean` | Reader lemmas a merge line needs, all `@[upd_merge_set]`. |
| `Update/Examples.lean` | The headline chain's last two lines, written out of `Upd.Elem` functions. |

## Weakest preconditions

| Module | What it is |
|---|---|
| `Wp/Monad.lean` | The interpreter as `SolM`, and the two modalities as one wp each (`Box.wpB`, `Dia.wpD`). Both *defined* by the shape their `_run` lemma states. |
| `Wp/Verdict.lean` | `checkResult` and `check_eq_checkResult`. |
| `Wp/TerminalUpdate.lean` | The state update of every terminal rule in the interpreter's state vocabulary, never through its evaluators. `terminalUpdate?` is `some` for exactly the 83 terminal arms. |
| `Wp/Terminal/Vocab.lean` | Bridges from each interpreter evaluator to the vocabulary readers. |
| `Wp/Terminal/Update*.lean` | One `<rule>_update` theorem per terminal rule, **under the rule's guard**. |
| `Wp/TerminalRules.lean` | `terminalUpdate_sound`, `TerminalRuleStep`, `terminal_step_sound`. Not proved: no unfold rule is accidentally terminal. |
| `EvalBattery.lean` | `sol_eval_battery` / `sol_exec_eval`; depend on the interpreter alone. |

## Semantics and typing

| Module | What it is |
|---|---|
| `Semantics.lean` | Run-time values and the executable state semantics; `SolidityJudgment.check`/`Holds`. Total, no `partial` — Lean checks termination. Follows solc where KeY was more liberal (`docs/solc-alignment.md`). |
| `SemanticsProperties.lean` | Association-list, read-after-write, frame, allocation-freshness, copy-frame theorems. |
| `StuckShape.lean` | `StuckCause`, the halt taxonomy, and `find_stuck_iff`. Deliberately no Boolean mirror. |
| `StorageTyping.lean` | `Layout`, `SVal.hasTy`, read-typing lemmas, and the runtime sorts `SVal.keySort`/`MVal.keySort`. |
| `StoragePreservation.lean` | The write-side twin: `save_hasTy`, `State.saveStorage_wellTyped`, `defaultForTy_hasTy`. |
| `StateTyping.lean` | The full-soundness invariants: `Ctx`, `HeapTy`, `StateWT`, weakening, `wtExpr`, cross-domain copy typing. |
| `TypeSoundness.lean` | Type soundness: the expression block preserves `StateWT`, then `execStmt_sound`/`execBlock_sound` — storage well-typedness is an inductive invariant. v1 scope notes in the docstrings. |
| `Reachability.lean` | Tightness of `wellFormed(storage)`: `Reachable`, `SVal.canonical`, `storage_tight`, `no_hidden_invariant`. All take `layoutOkB L`. **OPEN**: `reachable ⇒ canonical` (two `sorry`s). |
| `WellFormedConsumers.lean` | The table of facts the taclets consume from a symbolic storage. **OPEN**: row C6's state-level form `saveStorage_canonical`. |
| `DecEq.lean` | The hand-written `DecidableEq SVal` and derived instances; shared by every `native_decide`. |

## Sort faithfulness (the solkey cross-check)

| Module | What it is |
|---|---|
| `TacletAnnotations.lean` | Proof-free table of the taclets' read-sort annotations, transcribed from the `.key` file. |
| `KeyTacletParser.lean` | Token-level `.key` scanner plus the `conforms` cross-check. |
| `SortFaithfulness.lean` | `sortFaithful_all`: every annotation row's sort claim proved against the interpreter, except the listed `openFindings`. `rows_accounting` records what the headline really covers. |
| `SolkeyCheck.lean` (root) | `lake exe solkeycheck`. **Known failing, pre-existing**: 78 rows of drift against the live checkout. Re-syncing is its own change — it also moves `SortFaithfulness.lean` and `Counterexamples/PreFixSortAnnotations.lean`. |

## Counterexamples

Each is a refutation that pins down why a hypothesis or conjunct is there.

- `EvaluationOrder.lean` — the pre-fix residual refuted; the current rules shown to agree on the same two programs.
- `ErrorOrder.lean` — why the freeze cannot be conditional on the path being impure (`unfrozen_not_sound`).
- `RefSourceOrder.lean` — what `hprim` carves out: it is the **interpreter**, not the rule, that is unfaithful to solc for a reference source. **OPEN**: make assignment target-first for reference sources, then drop `hprim`.
- `PreservationNecessity.lean` — nine refutations, one per dropped invariant conjunct, each with a positive twin.
- `PreFixSortAnnotations.lean` — the caught sort bug, and the `openFindings` rows.
- `StaticRuntimeSort.lean` — the static sort of an array/mapping type is not its value's runtime sort.
- `DeleteFamilyGenericOverlap.lean` — first-order inconsistency proofs for the `0f9b99ad55` delete fallthroughs; records the surviving gap.
- `WellTypedNecessity.lean` — `SortFaithful` minus `wellTypedStorageB` is false; well-typedness is exactly the boundary.

## The EVM compiler

| Module | What it is |
|---|---|
| `Evm/Machine.lean` | EVM-style stack machine; documented deltas from EVMYulLean in its docstring. |
| `Evm/Compile.lean` | Solidity-AST → EVM for the verified fragment; partial, `none` = outside it. |
| `Evm/BoundedSemantics.lean` | The uint256-bounded mirror of the interpreter plus the `*_agree` theorems. |
| `Evm/Correctness.lean` | Leroy-style forward simulation: `compile_preserves_ok`/`_revert`, verified inlining, judgment transfer. See `docs/compiler-verification.md`. |
| `Evm/Examples.lean` | `native_decide` differential tests and concrete instantiations. |

## SolSpec (own Lake target, `scripts/check-spec.sh`)

`Spec/Assertion.lean` (readers, `Ann`, `vc`/`totalVC`/`partialVC`/`revertsVC`),
`Spec/Tactic.lean` (`sol_spec`, over a *symbolic* initial state),
`Spec/Syntax.lean` (the `solspec!` notation),
`Spec/Metatheory.lean` (the two modality results),
`Spec/Examples.lean` (the reference for the code generator in
`vscode-extension/src/spec/emitLean.ts`),
`Spec/SyntaxExamples.lean` (grammar smoke tests then proved specs).
Root: `SoliditySpec.lean`, deliberately not imported by `Solidity.lean`.

## Examples

- `Examples/Derivations/Paper.lean` — **the calculus's worked examples**, one chain each, written as the calculus writes them (`=> {U} <[ p ]>(φ) ~*> …`), update beside the shrinking program. Rule sequences are computed, not written. Root of the `SolidityExamples` target, **not** in the default build (~30 min CPU); run `./scripts/check-examples.sh`.
- `Examples/Taclets/` — ports of the KeY taclet tests, verified against the semantics.
- `Examples/Solkey/` — the ported solkey corpus (`SolidityCorpus` target, generated by `scripts/solkey-port.mjs`).
