# Module map

One line per module: what it defines and why it exists. Open the module's
own `/-!` docstring for the detail; this file is the index, not a summary of
them. Modules not listed here are examples or small helpers whose name says
what they are. Open problems are flagged **OPEN** inline.

```
Solidity/  KeySort.lean  AST.lean  Semantics.lean   the three that stay at the root
           Semantics/   the interpreter's satellites: properties, stuck shapes,
                        DecidableEq, the callback relation
           Calculus/    the rule table and everything proved about it
           Theory/      the data-structure theories as free-term algebras
           Typing/      storage typing, state typing, type soundness, reachability
           SortCheck/   the annotation table, the `.key` scanner, faithfulness
           Tactics/     the derivation engine: `sol_derivation`, `sol_rewrite`,
                        `sol_runs`, `sol_calculus`, and the simp sets they need
           Update/      the symbolic-update algebra and the sequent layer
           Wp/          the weakest-precondition verifier and `sol_wp`
           Evm/         the EVM compiler and its correctness proof
           Kernel/      the typed calculus ported from mini-solkey (`docs/kernel-port.md`)
           Counterexamples/  one refutation per hypothesis that carries weight
           Examples/    worked examples in the default build
           Paper/       the paper's chains (`SolidityPaper`, its own target)
           Corpus/      the ported solkey corpus (two targets, two routes)
```

**Directories group by topic, not by dependency order.** `Calculus/` does not
sit below `Typing/`: `Calculus/Coverage.lean` imports `Typing/Soundness.lean`,
while `Typing/Storage.lean` imports `Calculus/RuleSoundness.lean`. Lean is
content — there is no module cycle — but a reader who takes a directory for a
layer will be wrong. The layering that does hold is the small one: syntax in
`AST.lean`, rule enumeration in `Calculus/Rules.lean`, proof relations after
both. New modules go in `Solidity.lean`.

## The calculus

| Module | What it is |
|---|---|
| `KeySort.lean` | solkey's sort lattice as one Lean type: `parents`, `ancestors`, `KeySort.le`, KeY spellings. The *only* model of the lattice. Array/mapping sorts sit directly below `StValue`, siblings of `Struct` (not below it). Imports nothing. |
| `AST.lean` | Solidity syntax; the `sol!` notation and its `sol_stmt`/`sol_expr` grammars. `Ty.keySort` mirrors the KeY hierarchy structurally; `Field.sort = ty.fieldSort` is *computed*, so a field cannot be classified against its own type. Old constructor names survive as `@[match_pattern]` abbrevs. Holds the struct table `Semantics.structDef`, its rank certificate and `Semantics.tyHasMapping` (solkey's `StorageReferenceTypes.containsMapping`), so `TypedStmt.Assign.mk` can refuse a storage-to-storage copy of a mapping-carrying type (`mapFree`), as solc ≥ 0.7 and `ParserUtils.parseAssignmentMaybe` do. |
| `Calculus/KeyTaclets.lean` | The 310 taclets of `solidityProgramRules.key` (solkey `8c5c69ca25`) as one type, plus the three `\heuristics` sets and `KeyOrigin`. Regenerate with the `awk` recipe in its docstring. Imports nothing. |
| `Calculus/PaperRules.lean` | The paper's rule tables (`rules/*.tex`) as one type, `paperOrigin` per `RuleName`, and `paper_rules_partitioned`: every rule of the paper is claimed but `ifElseSplit`, and each Lean rule the paper lacks is filed under a reason (`keyTier`, `plumbing`, `calculus`). `./scripts/check-paper-rules.mjs` checks the enumeration against the paper. The port checklist in the other direction. |
| `Calculus/RuleSyntax.lean` | The `sol_rule` declaration syntax and `sol_assemble_rules`; carries the schema-variable table (`schemaVar`). Imports `Lean` only. |
| `Calculus/Rules.lean` | One `sol_rule` per rule, organised by family. A rule is a taclet, not a rewrite: `StepEffect` carries `goals` (guard, update, residual), read as KeY's weakest precondition. Update syntax here is AST-only, and updates are *terms*: `StTerm` at `structRules.key`'s signature, `MemTerm` at `memoryRules.key`'s. |
| `Calculus/RuleShapes.lean` | Structural checks: `mainBlock` reduction, `goals_nonempty`, `taclets_partitioned` (306 of 310 claimed, four listed with a reason), `twins_origin_eq`, `heuristics_eq_origin`. |
| `Calculus/Completeness.lean` | `FirstStepCase`/`RuleStep` and the bridge `RuleStep.step_of_ruleApplies` with its converse. |
| `Calculus/CandidateStep.lean` | `FirstStepCase` built from mutual exclusion instead of a ~190-entry list walk (`firstStepCase_box`/`_diamond`/`_both`). What makes a pinned step cheap. |
| `Calculus/Coverage.lean` | `candidate_applies`, the syntactic `ResidueShape` (26 shapes no rule covers), and `RuleStep.complete_of_wellTyped` over the rule-independent fragment. |
| `Calculus/Uniqueness.lean` | Rule mutual exclusion via the total dispatch `candidate` (`applicable_eq_candidate`). `RuleSetDisciplined` carries exactly three facts. A failing uniqueness build signals a condition overlap. |
| `Calculus/Progress.lean` | Progress is **false** here and this proves it (`symbolicIte`, `not_progress`), plus the judgment-layer split that handles it. **OPEN**: `BlockStep.wellFounded` is a documented `sorry`. |
| `Calculus/MultiStep.lean` | `BlockStep` (`⇝`), `BlockReflMultiStep` (`⇝*`), `NamedBlockStep` (`⇝[.rule]`) and the `Trans` instances. Framing (`appendStmts`, `append_suffix`, `inContext`, and the rule-level `NamedBlockStep.inSuffix`): a chain carries a *suffix*, and a prefix is consumed rather than carried, because `⇝` fires at the head. |
| `Calculus/Termination.lean` | Termination-certificate interface. **OPEN**: the concrete all-rules certificate. |
| `Calculus/RuleValidation.lean` | Per-rule `native_decide` validation of unfold rules against the executable semantics. |
| `Calculus/RuleSoundness.lean` | `<rule>_sound` per unfold rule: residual agrees with the original modulo scratch aliases. **OPEN**: what the ledger below lists. |
| `Calculus/SoundnessLedger.lean` | `#soundness_ledger`: each `<rule>_sound`'s hypotheses beyond `hcond`/`hfresh`, missing theorems and `sorry`s, pinned by `#guard_msgs` as a ratchet. `hypKind` ties a semantic hypothesis to its refutation. Prose in `docs/soundness-hypotheses.md`. |
| `Calculus/JudgmentSplit.lean` | KeY `ifthenelse_split` as a theorem about `SolidityJudgment.Holds`, not a rule: a single-successor `BlockStep` cannot yield two goals. |
| `Calculus/RewriteSoundness.lean` | Lifts local soundness through untouched block suffixes and `⇝*`. `BlockExecAgree.append_left`/`append_right` are the context congruence the rewrite layer cannot have — unconditional on a prefix, freshness-guarded on a suffix. |

## The data-structure theories

solkey's `find`/`save`/`read`/`write` are uninterpreted symbols whose meaning
is a taclet set. These modules are that theory as terms, with each taclet a
theorem and, for the memory algebra, a denotation into the interpreter
(`Update/Theory.lean`).

| Module | What it is |
|---|---|
| `Theory/Storage.lean` | `structRules.key`'s taclets, over `Theory/Terms.lean`'s sorts. Stated about **`findSt`**, the read that does not cross into memory, because that is the reader `structRules.key` has — `copyMem` is declared in `structMemoryRules.key`. `save`, `storeAt`, the delete family and `diverges` are here. Every taclet a theorem, in the *pre-fold* shape: the leaf of a write collapses (`saveOnEmpty`, `saveOnStoreCons` with its `isEmpty(flds)` split, `selectOnSaveEmpty`), because the copy on which solkey's non-collapsing leaf differs — a storage-to-storage copy of a mapping-carrying type — is not a statement (`TypedStmt.Assign.mk`). `storeAt` is the one-segment walk; `selectOnSaveCons` with no well-formedness hypothesis; the four `find`-over-`save` laws (`find_save_same`/`_extends`/`_prefix`/`_frame`) plus `find_append` — `Semantics` had only the first. The delete family is eager (`delNode`/`delValue`/`delAt`) and states every `selectStDelNode*` rule but `Map`: a `Seg` carries no `MapField`, so the mapping-preserving `delete` is the interpreter's alone. `findDelAtFields` carries a read through the fields of a deleted node. Still a theory over free terms, as upstream's is: the pre-state leaf `Struct.cur` is a view like `copyMem`, and what it denotes is `Update/Lower.lean`'s business. |
| `Theory/Memory.lean` | `memoryRules.key`'s taclets, over `Theory/Terms.lean`'s sorts, plus the `new` predicate. Every taclet a theorem, including the chain-walking family (`readREmpty`, `readRCons`, `idCCDef`, `defaultDefIdentity`) and `newFromAdd`/`readOnAddM` in KeY's branching form. Resolving a path identity against a heap is the denotation's job (`Update/Theory.lean`). `copySt`/`copyMem` are `Theory/CrossDomain.lean`. |
| `Theory/Terms.lean` | The sorts, because `structMemoryRules.key` ties the other two files together: `copyMem` is a `Struct` constructor and `copySt` a `Memory` one, as KeY declares them, so `Struct`/`StValue`/`Memory` are one mutual inductive. With them the readers that are mutual for the same reason — `selectSt`, `findSt` (the storage read that stops at a view), `find` (the one that crosses into `readR`), `readIn`/`readId`/`readR`/`readRId`, and the path-identity resolver. All structural: the cycle is cut by `readIn` reading its copied struct with `findSt`, so every equation stays `rfl` and a closed term reduces in the kernel, which is how half the taclets are checked. `Struct.inductionOn`/`Memory.inductionOn` are the one-sort recursors a mutual inductive does not give. `Struct.cur p` is the storage a derivation line started from, below `p`: the leaf a read is lowered onto. |
| `Theory/CrossDomain.lean` | `structMemoryRules.key`'s four taclets on those sorts: `findCopyMem`, `readCopySt`, `readCopyStIdentity`, `readCopyStOther`. `readCopyStIdentity` falls out of `defaultDefIdentity` because a copied struct member reads as `dflt`. Not modelled: a view nested in a view — `StValue.find_eq_findSt` is where that is stated, and no worked example nests one. |
| `Theory/Rewrite.lean` | The theory layer's answer to `Calculus/Rules.lean`: `TheoryRule`, one constructor per rewrite rule of the paper's signature, under **the paper's** name rather than KeY's, and `lemmaNames` saying which theorem each one is at each sort. What lets a `sol_rewrite` line write `=[.findOnSave]` and have it checked. `#theory_rules` prints the table; `./scripts/check-theory-rules.mjs` checks it against the paper's `\namedRwRule` declarations. |
| `Update/Theory.lean` | A rule's stated *memory* update read as a KeY term: `heapRhs_eq_theory` over `Rules.MemTerm`, covering a `write` on the `memory` variable — `addM`/`copySt` are not read back, because denoting them means reconciling KeY's lazy allocation with `Semantics.allocDefault`'s eager one; `denoteMem`/`denoteMV` resolve a path identity against the heap, and `denoteMem_new` discharges KeY's freshness premise. The storage half is gone with `Theory/Storage.lean`'s old pre-state leaf: what it reconciled — solkey's mapping-keeping leaf against the interpreter's plain write — differs only on a copy the AST cannot express. Storage *reads* are related to the theory by `Update/Lower.lean` instead. |

## Updates and the sequent layer

| Module | What it is |
|---|---|
| `Update.lean` | The symbolic-update algebra: `Elem`, `Par`, `Upd.seq`, and the merge law `Par.seq_single`. |
| `Update/Eval.lean` | What an `UpdTerm` means; every reader is one of `Wp/Terminal/Table.lean`'s. `storageRhs` and `memEval` are recursions over `Rules.StTerm` and `Rules.MemTerm`. `setSizeOn`/`pushAtOn` are the two writes a *program* cannot make — assigning `a.length`, and writing one past the end — and are the only users of `SVal.saveExt`. |
| `Update/Wp.lean` | The wp reading, `guard → {update}⟨residual ++ rest⟩post` per goal. |
| `Update/TacletTable.lean` | `goalsExec … = terminalUpdate r …` per rule. 21 bridged; the rest listed in `openBridges` with a reason. |
| `Update/Bridges.lean` | `Par.toUpd [...] = <family> args`, built on frame facts. Coverage list in its docstring. |
| `Update/Step.lean` | The derivation line `Γ ⟹ {U₁}…{Uₙ} goal`, `Frontier`, `NamedFrontierStep`, `Frontier.Equiv` (the merge line). Arrows `⇝ᵘ`, `⇝ᵘ*`, `⇝ᵘ[r]`, `≡ᵘ`. A line's `rigid` reads (`{v := ⟦t⟧}`, `t` a storage-theory term over the pre-state) are woven into its stack by `weaveUpd`. |
| `Update/LowerLaws.lean` | The interpreter's read after a write (`find_save_extends`/`_frame`, `find_append`, `find_defaultOf`) beside the theory's reads of a deleted node, and `Sim`: the theory term and the storage agree on every read the term answers with a literal or the untouched pre-state. `sim_save`/`sim_delAt` carry it across a write and a delete. |
| `Update/Lower.lean` | `lowerLine`: a line's storage reads become rigid reads of the storage theory, the writes before them folded into the term. `lowerFrontier_equiv` makes that a merge line — for one root, literal writes, deletes and any binding, stopping at the first update it does not know, and leaving a read whose theory answer is no literal (a mapping entry after `delete` of its struct). `raiseFrontier_equiv` writes a literal rigid read back as a binding. |
| `Update/SequentSyntax.lean` | The `seq!{ … }` surface notation and the `=>` derivation line (`sol_line`), including the paper's bare `(φ)` goal. |
| `Update/SequentPP.lean` | The other direction: a delaborator printing a `Sequent` back as its `seq!` line, so a goal between two steps reads as the calculus draws it. Falls back per line on anything it cannot account for; `pp.solidity.seq` switches it off. |
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
| `Wp/Terminal/Table.lean` | The state update of every terminal rule in the interpreter's state vocabulary, never through its evaluators. `terminalUpdate?` is `some` for exactly the 95 terminal arms. |
| `Wp/Terminal/Vocab.lean` | Bridges from each interpreter evaluator to the vocabulary readers. |
| `Wp/Terminal/Update*.lean` | One `<rule>_update` theorem per terminal rule, **under the rule's guard**. |
| `Wp/Terminal/Soundness.lean` | `terminalUpdate_sound`, `TerminalRuleStep`, `terminal_step_sound`. Not proved: no unfold rule is accidentally terminal. |

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
| `Semantics/Callback.lean` | KeY `transferSemantics:withCallback` as a *relational* layer over `execStmt` (`ExecC`, `HoldsC`): a havoc branch is nondeterministic, so it cannot live in the total interpreter. |

## The derivation engine

The tactics and command elaborators every worked example is written with.
They are infrastructure, not examples, which is why they are not under
`Examples/`.

| Module | What it is |
|---|---|
| `Tactics/Derivation.lean` | `sol_derivation`, `sol_runs`, `sol_calculus`, the `steps`/`steps!` navigation, the sequent layer's `seq_step`/`seq_done`/`seq_steps?`/`seq_norm`, `upd_norm`/`upd_merge`, and the alias helpers. The single largest shared dependency in the package. |
| `Tactics/Rewrite.lean` | `sol_rewrite` and the `theory_step` family: the equality-arrow sibling of `sol_derivation`, resolving a rule name through `Theory/Rewrite.lean`'s `theoryRuleLemma`. `theory_rw` is the same rules as `rw` spells them, on an `Eq` goal or on a `⇝ᵘ*` goal, which it lowers first (`seq_lower`); `seq_raise` closes the latter once every rigid read is a literal. |
| `Tactics/RuleSimpAttr.lean` | `register_simp_attr rule_simp_set`, the `solidity.steps` trace class, and the `sol_rule` command that tags rules into the set. Its own module because a simp attribute must be initialized in a module imported by its users. |
| `Tactics/EvalBattery.lean` | `sol_eval_battery` / `sol_exec_eval`; depend on the interpreter alone. |

## Sort faithfulness (the solkey cross-check)

| Module | What it is |
|---|---|
| `SortCheck/Annotations.lean` | Proof-free table of the taclets' read-sort annotations, transcribed from the `.key` file. |
| `SortCheck/Parser.lean` | Token-level `.key` scanner plus the `conforms` cross-check. |
| `SortCheck/Faithfulness.lean` | `sortFaithful_all`: every annotation row's sort claim proved against the interpreter, except the listed `openFindings`. `rows_accounting` records what the headline really covers. |
| `SolkeyCheck.lean` (root) | `lake exe solkeycheck`. At zero against solkey `8c5c69ca25`: 110 read-bearing taclets, 110 rows, `openFindings` empty. |

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

## The typed kernel

The port of mini-solkey's calculus, phase by phase; `docs/kernel-port.md` is
the plan and the tracker. No `sorry`, `native_decide` or axiom here.

| Module | What it is |
|---|---|
| `Kernel/Contract.lean` | `Contract` (its storage roots; struct bodies stay `structDef`), `contract!{}`/`sol_ty!()`, the eight ported contracts, each checked against its interpreter store. |
| `Kernel/Syntax.lean` | The typed syntax, indexed by contract and local context: `SPath`/`Loc`/`Val`/`Src`, `Stmt C Γ Γ'`, `Prog`. Storage slice so far. |
| `Kernel/Erase.lean` | Erasure into the untyped AST, spelled as the rule table spells names; `Stmt.erase_wt`/`Prog.erase_wt`: the erasure is `stmtWt`-typed, no hypothesis. |
| `Kernel/Print.lean` | `Prog.toStr`/`Prog.show`: a kernel block printed as Solidity. |
| `Kernel/Semantics.lean` | The denotation (`SPath.resolve`, `Val.eval`, `Stmt.run`) by structural recursion, and adequacy: `Stmt.run_eq`/`Prog.run_eq`, `execStmt σ s.erase = s.run σ` from every state. |
| `Kernel/Frame.lean` | `Fresh`, `Ctx.Sub` and weakening (erasure unchanged), and the frame lemmas: a term typed at `Γ` does not see a name fresh at `Γ`. |
| `Kernel/Taclet.lean` | The taclet judgement `Taclet C m s pr`, one constructor per solkey taclet (storage family: 41), with `Hole` for the paper's `lhs = •`, `Upd` and `Premise`. |
| `Kernel/Sound.lean` | `Premise.Correct` and `Taclet.sound`, no hypothesis beyond the constructors' freshness proofs; `SameOk` is the agreement an unfolding rule owes. |
| `Kernel/Elab.lean` | `ksol[C]{ … }`/`ksol{ … }`: raw syntax, the elaborator (`synth`/`check`/`elabProg`), the quoters; evaluated at compile time, re-checked by the kernel. |

## Examples, chains and corpora

Three trees, told apart by the *proof route*, not by the subject:

| Tree | Target | Route |
|---|---|---|
| `Examples/` | `Solidity` (default) | the rule table, through `Tactics/Derivation.lean` |
| `Paper/` | `SolidityPaper` | the same, written as the calculus writes it |
| `Corpus/Wp/` | `SolidityCorpus` | `sol_wp` — the interpreter, never the rule table |
| `Corpus/Calculus/` | `SolidityCalculus` | `sol_calculus` — the rule table, never the interpreter |

- `Examples/` — the block-rewriting examples (`—→`/`—↠`, anonymous, numbered
  1–37 across the eight files) and `Examples/Derivations/` (named
  `sol_derivation` theorems in `⇝[.rule]`, so a rule rename is a build
  failure). `Examples/Derivations/StorageSteps.lean` is `Paper/Storage.lean`
  written the other way round — endpoints in the statement, rules in the proof
  — which is what `seq_step` is for, and which puts the storage chains in the
  default build. `Examples/Taclets/` ports the KeY taclet tests and
  checks them against the semantics with `native_decide`.
- `SolidityPaper.lean` and `Paper/` — **the calculus's worked examples**: the
  root carries the conventions and the imports, `Paper/` the chains, written
  as the calculus writes them (`=> {U} <[ p ]>(φ) ~*> …`), update beside the
  shrinking program; rule sequences are computed, not written.
  `Paper/Storage.lean` (sections 1–4), `Paper/Memory.lean` (5–7),
  `Paper/CrossDomain.lean` (8), `Paper/Control.lean` (9–10),
  `Paper/Checks.lean` (the lines run against the interpreter). Not in the
  default build (~30 min CPU); run `./scripts/check-paper.sh`. Which paper
  example each chain is, and which have none, is `docs/paper-parity.md`,
  checked by `./scripts/check-paper-parity.sh`.
- `Corpus/Wp/` — the ported solkey corpus, nine contracts, generated by
  `scripts/solkey-port.mjs` (except `Corpus/Wp/Net.lean` and
  `Corpus/Wp/Rules.lean`, which are hand-written because there is no `.sol`
  to port). Verdicts in `tests/solkey/expected.tsv`, scoreboard in
  `docs/solkey-parity.md`.
- `Corpus/Calculus/` — **the same obligations proved from `Calculus/Rules.lean`
  alone**, from the same pass of the same generator. One `sol_calculus` per
  obligation: `seq_closes` runs the taclets to a closed frontier and the
  endpoint is decided. Verdicts in `tests/solkey/expected-calculus.tsv`,
  scoreboard in `docs/calculus-parity.md`.

The two halves of `Corpus/` are **not** the same size: `Corpus/Wp/` covers
nine contracts, `Corpus/Calculus/` only `TestSuite`. That gap is the real
state of the calculus, not a gap in the layout — `docs/calculus-parity.md` is
where it is accounted for. Keeping them as siblings is what makes it visible.
