# Module map

One line per module: what it defines and why it exists. Open the module's
own `/-!` docstring for the detail; this file is the index, not a summary of
them.

```
Solidity/  KeySort.lean  AST.lean  Syntax.lean  Semantics.lean  Update.lean
           Semantics/   the interpreter's satellites: properties, the frame kit
           Calculus/    the taclets and everything proved about them
           Theory/      the data-structure theories as free-term algebras
           Typing/      value typing: storage layouts, state invariants
           SortCheck/   the annotation table and the `.key` scanner
           Counterexamples/  refutations that pin a design decision
           Examples/    the worked examples, in the default build
```

**Start at `Theorems.lean`**: the main theorems on one page, in notation
(`⊢ φ → ⊨ φ`, `(P, σ) ⇓ σ'`, `⟦P⟧`), each proved by the original's name.

The layering: types and names (`AST.lean`), the typed syntax
(`Syntax.lean`), the interpreter (`Semantics.lean`), terms and formulas
(`Update.lean`), the taclets (`Calculus/Rules.lean`), then what is proved
about them. New modules go in `Solidity.lean`; `scripts/check-orphans.mjs`
fails on a module nothing imports.

**Formulas read storage through the Theory.** Programs and updates run in the
interpreter, but a formula's equation reads its terms in the storage theory:
`a ≐ b` (`Fml.eq`) compares `Term.denote`s over `State.abs`, the state as a
Theory term — total, as KeY's `=` is, so it holds or fails of terms that
halt too. A program comparison `a == b` is `Fml.eqD a b`, printed `a = b`:
`defined(a) ∧ defined(b) ∧ a ≐ b`, the interpreter's equation
(`holds_eqD_iff`). `Theory/Bridge/` proves once that the interpreter's
reads and writes are the Theory's on `abs`, up to observational equality
(`StValue.Equiv`), so a Theory law is a rule of the calculus with no
soundness proof of its own: a `Term.Theq` between the terms denoting its
sides (`Calculus/TermRules.lean`, the laws in `Calculus/TheoryLaws.lean`),
applied to a sequent by `Proves.theoryRw` (`rw [h]`).

## The language

| Module | What it is |
|---|---|
| `KeySort.lean` | solkey's sort lattice as one Lean type: `parents`, `ancestors`, `KeySort.le`, KeY spellings. Imports nothing. |
| `AST.lean` | The static vocabulary: `PrimTy`/`Ty`/`RefTy` (dynamic and fixed-size arrays, `RefTy.fixed`) and their KeY sorts, the struct table `structDef`, operators typed at the primitive type they accept, and `Var` (a program name, or a fresh one a rule declares). |
| `Syntax.lean` | The typed syntax, indexed by contract and type: `Val C p`, `SPath C T`, `Loc`, `MPath`, `Stmt C`. A statement no rule can run cannot be written. `Contract` (its roots and its functions, `FunDecl`, the body as read), the named example contracts, and `sol[C]{…}`: a call (`Stmt.call`) carries its callee inlined, every callee local fresh, a function calling only the ones declared before it; the elaborator, run at compile time and re-checked by the kernel; it captures `++`/`−−` inside an expression and a conditional of references before their statement, in solc's order (`hoist`), and folds a fixed-size array's `.length` to its literal. Array paths carry `ArrTy` (`dyn`/`fixed`), so one rule covers both kinds. Beyond Solidity's own spelling it accepts `else if`, a block statement without its trailing `;`, `constructor` (read as `init`) and `constant`; an error points at the statement that failed and names the expression. |
| `FreshNames.lean` | `FreshNames.ofTable`: the examples' names for the rules' fresh variables (`pv` for `se1`, `acc` for `sp1`), one table per example, and `FreshNames.clashes`, which checks that a printed line reads back. |
| `Semantics.lean` | The interpreter, `Stmt.run`, by structural recursion on the typed syntax. KeY's state (storage tree, identity heap, locals, `net`), following solc where KeY was more liberal (`docs/solc-alignment.md`). |
| `Semantics/Properties.lean` | Association-list, read-after-write, frame and allocation lemmas about the interpreter's state operations. The path, run and result-monad lemmas every later layer shares (`SVal.find_append`, `State.saveStorage_ok_inv`, `Prog.run_append`, `Res.bind_eq_ok`, …) live here once. |
| `Semantics/Agree.lean` | `EnvAgreeExcept ns`: states that agree off a few scratch names, and a frame lemma per evaluator. What every unfolding rule's soundness composes. |
| `Semantics/DecEq.lean` | The hand-written `DecidableEq SVal`. |
| `Semantics/Callback.lean` | The callback semantics of `transfer`: `ExecS`/`ExecP`, a relation over `Stmt.run` in which a transfer may resume from any state (`State.havoc`) keeping the contract `Invariant`, or break it; `holdsC`; `TransferSem` and `holdsT`, the judgement parameterised by it; the deterministic run is a callback run (`Prog.exec_run`), the readings agree with no transfer (`holdsC_iff_holds`), frames. |
| `Update.lean` | Terms (`Term`, `PTerm`, `STerm`, `ITerm`, `MTerm`, …) read by the interpreter's own functions, and read in the Theory (`Term.denote`, over `State.abs`, total), parallel updates, formulas with both modalities (`Fml`, `holds`: `=` through `denote`, `defined` through `eval`, `Fml.eqD` both; `Valid`), and lowering program expressions to terms. |

## The calculus

| Module | What it is |
|---|---|
| `Calculus/RuleSyntax.lean` | The notation `dl{ … }`: schemas whose names carry their kind, and the delaborators that print taclets, premises and goals back in it. |
| `Calculus/Rules.lean` | The rules, two lists: `Taclet C k m s p`, solkey's, one constructor per taclet, named as solkey names it, written in `dl{ ⟨[ s; ]⟩ ⇝ p }`; `LeanTaclet`, the rules solkey lacks; `Rule`, either; and `CallbackTaclet`, the other `transferSemantics`. |
| `Calculus/KeyTaclets.lean` | The 311 taclets of `solidityProgramRules.key` (solkey `f2eb3d98eb`) as one type, their `\heuristics`, and `KeyOrigin`. Regenerate with the recipe in its docstring. |
| `Calculus/Completeness.lean` | `Stmt.step`: the rule for every statement, a total function; `Stmt.complete`. |
| `Calculus/RuleShapes.lean` | Which solkey taclets each constructor transcribes (`tacletOrigins`), checked against the constructor list, and `taclets_partitioned`. `#enum_ctors` generates a constructor list and name table (used for `PrintedRule.all`/`name`). |
| `Calculus/PrintedRules.lean` | The printed rules as a type and which constructor each is. |
| `Calculus/SoundKit.lean` | `SameOk`, `Premise.Correct`, and the lemmas and tactics the soundness proofs are made of. The `writeRes`/`heapRes` equations, the `binding*` readers `envVal` is defined through, and `upd_unfold_with [..]`. |
| `Calculus/SoundUpdate.lean` | Every taclet with an update premise has the statement's effect. |
| `Calculus/SoundUnfold.lean` | Every unfolding taclet runs like its statement off the fresh names. |
| `Calculus/RuleSoundness.lean` | `Taclet.sound`: every taclet, no hypothesis but freshness; `LeanTaclet.sound`, `Rule.sound`. |
| `Calculus/Logic.lean` | `Premise.fml`, the sequent calculus `Proves R Γ φ` at a `RuleSet` (among its rules `theoryRw`: a Theory equation `Term.Theq` rewrites every equation of the sequent, `Hyp.rwEq`; `updRw`: a rewrite that keeps what a run returns, `Term.EvalRefines`, in the box updates' right-hand sides, `Hyp.rwUpd`; the update rules `merge`, `mergeStorage`, `simplify`, `applyOnRigidBox`, `applyStorageBox`, so they apply with a modality left) (`Γ ⊢ φ` all rules, `Γ ⊢ₖ φ` solkey's) and `Proves.sound`; `close` only on a sequent with no modality left (`Fml.modalFree`); sequents print as `dl{ Γ ⟹ φ }`. The context walk (`Hyp.Reaches`, `Hyp.boxOnly`, `wrap_of_reaches`) is here; `⊢ₖ` goals print as `dl{ Γ ⟹ₖ φ }`. `dl{}` also reads `∨`, `↔`, `∃`, as the negated shapes they abbreviate. |
| `Calculus/Callback.lean` | The calculus with callbacks: `CallbackTaclet.sound` (`transferWithCallbackBox`/`Diamond`, premises the funds `F` (diamond only), `F → {U} I` and `F → {U} {havoc} (I → ⟨[ ω ]⟩ φ)`, read by `CbResume`), the judgement `ProvesC` and `ProvesC.sound`. |
| `Calculus/Quote.lean` | Quoters from formulas back to terms, so a computed goal is re-checked by the kernel. |
| `Calculus/Symex.lean` | Symbolic execution: `Fml.step` fires `Stmt.step`'s rule, `symex`, `symex_sound`; tactics `sol_step`, `sol_symex`, and `sol_derive`, the strategy as a `Proves` derivation. |
| `Calculus/SolkeyFragment.lean` | The refined syntax: `Stmt.inSolkey` (every call's arguments simple), on which solkey's rules alone are the calculus (`Stmt.step_taclet`, `Taclet.premise_inSolkey`, `Proves.toSolkey`); off it they fall short (`Proves.solkey_lt_calculus`). |
| `Calculus/Notation.lean` | `dl[C]{ … }` and `dl!{ … }`: concrete formulas read against a contract. |
| `Calculus/ReadWrite.lean` | What a state reads after a write: the four-way path comparison, memory addresses, copies member by member. Registers the simp sets `close_rw`, `decide_eval`, `decide_evalA`. |
| `SpecSyntax.lean` | The specification language as read: solkey's `SolSpec.g4` (`SpecExpr`, `spec!(…)`), and a function's clauses (`FunSpec`), which `contract!{ … }` reads as members above the function (`requires e;`, `ensures e;`, `skip;`, `invariant e;`). |
| `Calculus/Close.lean` | `sol_close`: a first-order goal in an arbitrary state, by weakest preconditions and `ReadWrite.lean`'s facts; `a = b` (`Fml.eqD`) through `eval`, `a ≐ b` of literals and locals through `denote` (`Close.holds_eqD`, `Close.holds_eq`). Its docstring lists what it does not close. |
| `Calculus/CloseTests.lean` | What `sol_close` closes, pinned. |
| `Calculus/Decide.lean` | `sol_decide`: reads of writes eliminated into case trees on key equalities (the four-way path comparison), `delete` included; `Fml.valid_iff_reduce`. The storage fragment, read live (`SVal.findLive`/`saveLive`) and bridged to the program's checked paths (`PTerm.toL_chk`). A delete below a key is exact by the read's shape (`KShape`, `delBelow`): a mapping kept, a fixed-size array's length kept. `values.length` read through writes (`LStor.lenU`). `sol_decide_heuristic`: the finishing step without constraints. Its equations are `a = b` (`Fml.eqD`, recognised by `Fml.eqDView`) and `a ≐ b` of a literal and a literal or a local (`Term.eqLit`), where the Theory's reading and the interpreter's agree. |
| `Calculus/Spec.lean` | Specifications compiled to dynamic logic, solkey's `SpecCompiler`/`SolidityProblemSynthesizer`: a clause against a storage term (`storage`, or the storage variable `old` under `\old`), `\forall` as `Fml.all`; `spec[C]{f}`, the box obligation `R ∧ L ∧ I ∧ requires → {old := storage} [ f(…); ] (I ∧ ensures)` with the layout premises `L`; `sol_spec`. |
| `Calculus/DecideComplete.lean` | The reads of the starting storage realizable: `Obs`, the constraint `ChildOk` (`childOk_findLive`), `realize_findLive`; the reduction over free reads (`LTerm.evalA`), `LFml.valid_iff_cons`/`Fml.valid_iff_cons`; `sol_decide`, deciding under the constraints. |
| `Calculus/Uniqueness.lean` | One rule per statement: every derivation's premise is `Stmt.step`'s. |
| `Calculus/Progress.lean` | A formula with a modality always steps: `Fml.active_iff_step`. |
| `Calculus/Termination.lean` | The weights, `Premise.Smaller` (of `Stmt.step`, and of every derivation: `Rule.smaller`), `Fml.measure`, `Fml.step_wellFounded`, `symex_normalizes`. |
| `Calculus/Chains.lean` | Derivations as values: `φ ~[r]~> ψ`, `~>`, `~*>`, `calc` chains of `dl!{…}` lines, `sol_chain`, `#derivation`. |
| `Calculus/UpdateRules.lean` | KeY's update simplification as `UpdRule`, each an iff: `sequentialToParallel`, `simplifyUpdate`, `applySkip`, `applyOnRigid` (an update that cannot halt, `Fml.sortedFor`). Below `Logic.lean`, the semantics of its update constructors: `Fml.subst_box`/`subst_box_st` (applied under the box, no totality premise), `Upd.mergeStorage_holds` (`withSt`, for terms whose storage reads are all `storage` terms), `Fml.withSt_box`, `Upd.defined_box`; `Term.EvalRefines` (`of_theq`: a Theory equation onto a literal), `Upd.rw` and `Upd.rw_box`, the rewrite of an update's right-hand sides. |
| `Calculus/TermRules.lean` | Theory equations as rewrite rules: `Term.Theq` (one Theory value in every state; a `Setoid`), `Term.rw` (not inside memory terms), `Fml.rwEq` (every total equation at any depth; not `defined`, update right-hand sides or programs), and `Fml.rwEq_holds`, the one soundness proof, through `Term.rw_denote` up to `StValue.Equiv`. `Proves.theoryRw` (`Calculus/Logic.lean`) applies one. |
| `Calculus/Rewrite.lean` | The steps after the program, KeY's way: `Proves.eqClose`; under `open Proves`, `rw [h]` with `h : Term.Theq t t'` is `Proves.theoryRw` (and `Proves.updRw` when `t'` is a literal) with the sequent computed (`sol_rw`; open arguments found at the first instance, as Lean's `rw`), `rw [h₁, ← h₂]` several or right to left; a rule may be a Theory lemma itself (`find_copyTo_same`, `delValueDefault`) or a definition to unfold, a run of them one `theoryRewrite` (`sol_rw [..]` the same, never Lean's `rw`). Under the box: `Proves.eqDSplit` (`a = b` into `defined(a)`, `defined(b)`, `a ≐ b`), `Proves.andSplit`, `Proves.definedLit`, `Proves.definedWritten` (`defined(x)` from the `x := t` that wrote it), `Proves.andSplitUpd`, `sol_apply_upd` (`applyStorageBox` or `applyOnRigidBox`), `Proves.eqRefl` (`t ≐ t`); `sol_upd`, `sol_merge` on `⊨`. |
| `Calculus/TheoryRewrite.lean` | A Theory lemma as a rewrite rule, as mini-solkey's `sol_rw`: `theoryRewrite` unfolds a term's `denote` (`denote_*`, `Calculus/TermRules.lean`), rewrites with the lemmas by `simp`, reads the result back as a term (`reifyTerm`) and returns `Term.Theq.of_eq`; side conditions on literal paths by `decide`. `normProves` computes a sequent's context and formula (compiled, quoted back by `Hyp.quote`/`Fml.quote`) so its terms are there to find; `snocProves` puts the context back in the `Γ ++ [h]` shape the update rules match. |
| `Calculus/TheoryLaws.lean` | The Theory's read-back laws as `Term.Theq` rewrite rules, each `denote` unfolded plus the Theory lemma it names (no `eval`): `findOnSave` (`find_copyTo_same`, a literal word), `findOnSaveFrame`, `findOnDelAt`/`findOnDelAtSave` (`find_delAt_same`), `findOnDelAtFrame`, `findOnPushFrame`, `findOnPopFrame`. Side conditions are syntactic Bools on `PTerm`s closed by `rfl`: `PTerm.hasSeg` (never `[]`), `PTerm.diverges` over `PTerm.segs?` (paths of members and literal indices). |

## The data-structure theories

solkey's `find`/`save`/`read`/`write` are uninterpreted symbols whose meaning
is a taclet set. These modules are that theory as terms, each taclet a
theorem.

| Module | What it is |
|---|---|
| `Theory/Storage.lean` | `structRules.key`'s taclets, over `Theory/Terms.lean`'s sorts. Stated about **`findSt`**, the read that does not cross into memory, because that is the reader `structRules.key` has — `copyMem` is declared in `structMemoryRules.key`. `save`, `storeAt`, the delete family and `diverges` are here. `save` is the collapsing write — the word write and `delAt`'s — in the *pre-fold* shape (`saveOnEmpty`, `saveOnStoreCons` with its `isEmpty(flds)` split, `selectOnSaveEmpty`); the non-collapsing one is `Theory/Copy.lean`'s `copyTo`. `storeAt` is the one-segment walk; `selectOnSaveCons` with no well-formedness hypothesis; the four `find`-over-`save` laws (`find_save_same`/`_extends`/`_prefix`/`_frame`) plus `find_append` — `Semantics` had only the first. The delete family is lazy at the node (`delNode` is the `delSt` leaf, `delAt` eager above it): a member is kept or reset by the node's kind (`selectOnDelNode`, `keepsOnDelete`), so the `Map`/`Fixed` rules are stated one selector down with the kind as a premise (`selectDelNodeMap`, `delFieldFixed`, …). `findDelAtFields` carries a read through the fields of a deleted node with no kinds in it (`kindFree`). Still a theory over free terms, as upstream's is: the pre-state leaf `Struct.cur` is a view like `copyMem`, and what it denotes is `Update.lean`'s lowering business. |
| `Theory/Copy.lean` | The copying write and the array writes: `copyTo` (solkey's non-collapsing `save`, a `copyAt` leaf), `stripVal`, `lenAt`, and `pushT`/`pushSlotT`/`fillSlot`/`popT`/`shrinkT`, the terms the calculus's `push`/`pop` denote. The `selectOnSaveEmpty*` rules are its `selectOnCopy*` laws, by the two nodes' kinds with no length invariant; the `find_copyTo_*`, `find_pushT_*`, `find_popT_*` read-backs. |
| `Theory/Observe.lean` | Congruence for `StValue.Equiv`: `Sim` (the closure of `Equiv` under `copyVal`, `delValue`, `storeAt`) and `Sim.equiv`, from one bisimulation step `Equiv.of_bisim`; every operation of the algebra respects `Equiv` (`Struct.Equiv.save`/`copyTo`/`delAt`/`pushT`/`popT`/…), so a law that holds only up to it is usable under any context. |
| `Theory/Abs.lean` | The interpreter's storage as a Theory term: `SVal.abs` (a node is a `storeSt` chain over its kinded leaf `mtK`; an array's live and past-the-end slots are one run of indices, its length outermost, fixed arrays too), `State.abs` (the roots as members of one struct node) and `rootPath`. The slot selection proved once (`select_slots`), the reads `select_abs_fields`/`_array`/`_map`, and the writes in the same layout (`storeAt_slots`, `storeAt_abs_fields`/`_entries`). Imports no `Update` and no calculus. |
| `Theory/Bridge/Find.lean` | The interpreter's read against `findSt` on `abs`, literally: `SVal.abs_find`, `State.abs_findStorage`, `abs_arrayLen`, `abs_lenAt_of_array`. |
| `Theory/Bridge/Save.lean` | The interpreter's save against the collapsing `save` on `abs`, literally (`SVal.abs_save`, `State.abs_saveStorage`): `setBy` and `storeAt` put a new binding at the same place. |
| `Theory/Bridge/CopyArray.lean` | The array-over-array arm of `SVal.overlay` against `copyAt`, up to `StValue.Equiv` (`abs_overlay_array`), given the element-wise copy and delete as premises so that `Theory/Bridge/Copy.lean` can feed it its induction. |
| `Theory/Bridge/Delete.lean` | `SVal.defaultOf` against the lazy `delValue` (`abs_defaultOf`), and `delete` against `delAt` (`State.abs_delete`), up to `StValue.Equiv`. |
| `Theory/Bridge/Copy.lean` | `SVal.strip`/`SVal.overlay` against `stripVal`/`copyVal` (`abs_strip`, `abs_overlay`), and an assignment's `writeStorage` against `copyTo` (`State.abs_writeStorage`), up to `StValue.Equiv`. |
| `Theory/Bridge/Push.lean` | `pushAt`/`pushPlaceAt`/`popAt` against `pushT`/`pushSlotT`/`shrinkT` literally, and a pop against `popT` up to `StValue.Equiv`; the interpreter's preconditions come from the `.ok` hypotheses. |
| `Theory/Bridge/Denote.lean` | The term bridge: `Term.denote_eval` and siblings (`Update.lean`'s `denote` agrees with `eval` where it returns), `Term.holdsEq_of_eval`, and `holds_eqD_iff` (`eqD` is the interpreter's equation). The one Theory module that imports `Update`. |
| `Theory/Memory.lean` | `memoryRules.key`'s taclets, over `Theory/Terms.lean`'s sorts, plus the `new` predicate. Every taclet a theorem, including the chain-walking family (`readREmpty`, `readRCons`, `idCCDef`, `defaultDefIdentity`) and `newFromAdd`/`readOnAddM` in KeY's branching form. `copySt`/`copyMem` are `Theory/CrossDomain.lean`. |
| `Theory/Terms.lean` | The sorts, because `structMemoryRules.key` ties the other two files together: `copyMem` is a `Struct` constructor and `copySt` a `Memory` one, as KeY declares them, so `Struct`/`StValue`/`Memory` are one mutual inductive. With them the readers that are mutual for the same reason — `selectSt`, `findSt` (the storage read that stops at a view), `find` (the one that crosses into `readR`), `readIn`/`readId`/`readR`/`readRId`, and the path-identity resolver. All structural: the cycle is cut by `readIn` reading its copied struct with `findSt`, so every equation stays `rfl` and a closed term reduces in the kernel, which is how half the taclets are checked. `Struct.inductionOn`/`Memory.inductionOn` are the one-sort recursors a mutual inductive does not give. `Struct.cur p` is the storage a derivation line started from, below `p`: the leaf a read is lowered onto. The kinded nodes (`mtK`, `NodeKind`) and the two lazy leaves `copyAt`/`delSt` are here, read one member at a time by `copyRead`/`keepsOnDelete`; `StValue.Equiv` is observational equality (`seen`/`readAt`). |
| `Theory/CrossDomain.lean` | `structMemoryRules.key`'s four taclets on those sorts: `findCopyMem`, `readCopySt`, `readCopyStIdentity`, `readCopyStOther`. `readCopyStIdentity` falls out of `defaultDefIdentity` because a copied struct member reads as `dflt`. Not modelled: a view nested in a view — `StValue.find_eq_findSt` is where that is stated, and no worked example nests one. |
| `Theory/Rewrite.lean` | The theory layer's answer to `Calculus/Rules.lean`: `TheoryRule`, one constructor per rewrite rule of the printed signature, under **its printed** name rather than KeY's, and `lemmaNames` saying which theorem each one is at each sort. `#theory_rules` prints the table. |

## Typing

| Module | What it is |
|---|---|
| `Typing/Storage.lean` | `Layout`, `SVal.hasTy`, read-typing lemmas, and the runtime sorts `SVal.keySort`/`MVal.keySort`. The write inversions (`opStore_ok_inv`, `bumpStore_ok_inv`, `State.writeStorage_ok_inv`, …), `Layout.tyAt_split`, and the `bind_inv` tactic. |
| `Typing/StoragePreservation.lean` | The write-side twin: `save` keeps a value's type. |
| `Typing/State.lean` | `StateWT`, the full-state invariant, and cross-domain copy typing. |
| `Typing/Soundness.lean` | Type soundness: `Stmt.run_wt`/`Prog.run_wt` keep `RunWT` over the locals context `Stmt.wt` threads. |
| `Typing/Reachability.lean` | Every reachable storage is canonical (`reachable_canon`), and three well-typed storages that are not. |
| `Typing/Constructibility.lean` | The converse: `SVal.tight`, the builder `Build.rootsProg` (`storage_tight`, `canon_reachable`, `no_hidden_invariant`), `Prog.run_tight`, and `reachable_iff` — reachable ⇔ canonical ∧ tight, for `Ty.okDeep` roots; canonical storages no program reaches. |

## Sort faithfulness (the solkey cross-check)

| Module | What it is |
|---|---|
| `SortCheck/Annotations.lean` | Proof-free table of the taclets' read-sort annotations, transcribed from the `.key` file. |
| `SortCheck/Parser.lean` | Token-level `.key` scanner plus the `conforms` cross-check. |
| `SortCheck/Faithfulness.lean` | Each taclet's read-sort annotation holds of what a well-typed run reads, storage and memory; `rows_covered`. |
| `SolkeyCheck.lean` (root) | `lake exe solkeycheck`. |

## Counterexamples

- `DeleteFamilyGenericOverlap.lean` — the first-order inconsistency of solkey's pre-`e67a0d7c48` delete fallthroughs.
- `StaticRuntimeSort.lean` — the static sort of an array/mapping type is not its value's runtime sort.
- `PreFixSortAnnotations.lean` — the pre-fix `find<[int]>` annotations refuted.
- `WellTypedNecessity.lean` — faithfulness needs well-typed storage.

## The EVM compiler

| Module | What it is |
|---|---|
| `Evm/Machine.lean` | A straight-line EVM: slots as terms, wrapping words and their two's complement reading, relative forward jumps, running code in pieces. |
| `Evm/Compile.lean` | The compiler from `Stmt C` for a stated fragment (`wtStmt`: `int`, static copies, `push`, fragile aliases), with solc's guards (`uTail`, `sTail`, `expCode`); a call compiled inlined. |
| `Evm/Repr.lean` | The storage layout: a typed path's slots (a fixed-size array inline, `ReprAt.fixed`), injectivity, writing a subtree is writing its slots, copies and `push`, lengths only grow (`live_mono`). |
| `Evm/Signed.lean` | The signed guard sequences (`checked_add_t_int256` and siblings) exact on two's complement words. |
| `Evm/Exp.lean` | `**`: solc's `checked_exp_unsigned`, its loop unrolled 255 times, exact. |
| `Evm/Correctness.lean` | `compile_correct`, `compile_storage`, `not_stuck`, under the `push` bound `L + pushesP P ≤ 2^64`. |
| `Evm/Examples.lean` | Compiled programs run by `decide`. |

## The tools

Commands for people, not the kernel: they run, print and search, and prove
nothing beyond the certificates they check.  `Examples/Tools.lean` and
`Examples/Verify.lean` pin each one's output.

| Module | What it is |
|---|---|
| `Tools/Show.lean` | Printers: a storage value read against its type, a state one root per line, the transaction (`fmtTx`), a clause as written. |
| `Tools/Common.lean` | What the commands share: resolving `C` / `C.f` (`resolveTarget`), evaluating a command's term, one report layout (`logReport`), reading a formula (`elabFormula`). |
| `Tools/Run.lean` | `#run C.f(args) [from σ] [with msg.sender := n, root := v, …]`: a call run by the interpreter from the contract's fresh state. |
| `Tools/Inspect.lean` | `#wp φ` (what symbolic execution leaves, and its update-free reading), `#step φ` (the rule that fires), `#taclet r` (a rule's shape, KeY origin, printed rule, soundness theorem; also by KeY name). |
| `Tools/DiffTest.lean` | `#difftest C` / `#difftest C.f`: the interpreter against the compiled EVM code from random well-typed storages, compared on what `compile_correct` claims; a mismatch prints the command that replays it. |
| `Tools/Counterexample.lean` | `Fml.eval3`, a three-valued evaluator sound both ways (`Fml.eval3_sound`); the witness search and shrinker; `#counterexample C.f` / `#counterexample φ`, certified by reflection when every premise evaluates. |
| `Tools/Verify.lean` | `#verify C` / `#verify C.f`: each spec'd function proved (`sol_spec`), refuted with a witness, or stuck with its goals; a proof is offered as a "Try this" theorem. |

## The solkey corpus

`SolidityCorpus` (its own target, `lake build SolidityCorpus`): each function
of solkey's `.sol` suites, generated by `scripts/solkey-port.mjs` into
`Solidity/Corpus/`, stated at the contract's initial store and decided by the
kernel. `./scripts/check-corpus.sh` checks the verdicts against
`tests/solkey/expected.tsv`; `docs/corpus-parity.md` is the scoreboard.

## Examples

Every example is a theorem `⊨ dl!{ … }` proved by `sol_symex; sol_close`, or
a derivation `⊢ φ` built one `apply` per taclet (`Calculus/Logic.lean`).
`docs/examples-port.md` says where each example of the removed untyped layer
went.

| Module | What it is |
|---|---|
| `Examples/Tour.lean` | The running example end to end. |
| `Examples/StorageSteps.lean` | One example per storage statement form, the worked derivations as `apply` walks. |
| `Examples/StorageSuite.lean` | solkey's taclet suite on storage, deduplicated. |
| `Examples/StorageDelete.lean`, `Examples/LedgerDelete.lean` | `delete`, and a struct holding a mapping deleted. |
| `Examples/Branch.lean`, `Examples/Revert.lean` | The two-goal split, a conditional of references; box and diamond on `revert`, `require`, `assert`, `transfer`. |
| `Examples/Values.lean` | Operators, short-circuits, checked arithmetic, `−−`, `++` inside an expression, negative literals. |
| `Examples/Operators.lean` | Bitwise `& \| ^ ~`, shifts, their compound assignments, `unchecked { … }`; the same on the machine. |
| `Examples/Calls.lean` | Internal calls: inlined bodies, captured arguments, nested calls, early returns (in a branch, in a callee), calls inside expressions, effects on storage; what cannot be written (recursion, a call under `&&`/`\|\|` or in a conditional's branch). |
| `Examples/Callback.lean` | The callback semantics: a checks-effects-interactions withdrawal proved with callbacks (`ProvesC`, `transferWithCallbackBox`), an interaction-first one proved without and refuted with, the diamond's funds. |
| `Examples/Memory.lean`, `Examples/CrossDomain.lean`, `Examples/Net.lean`, `Examples/Theory.lean` | Memory (memory `delete`, `new T[](n)`, `.length` included), copies between storage and memory, `transfer`, the theory's rewriting. |
| `Examples/Notation.lean` | What taclets, premises and sequents print, pinned. |
| `Examples/ApplySteps.lean` | The proof style: every `Proves` constructor once, and a refused rule. |
| `Examples/Chains.lean`, `Examples/UpdateRules.lean`, `Examples/Decide.lean` | Derivation chains, update simplification, `sol_decide`. |
| `Examples/ExampleNames.lean` | Chains in the examples' names for the fresh variables: the headline with `pv`/`acc`, the token example with `aliceTok`/`aliceAcc`, `acc` as a memory reference, `matrix[i++][i++]`; the tests of a table (a line is its default spelling's term, a capture numbered past a table name). |
| `Examples/Specs.lean` | Clauses as obligations (`spec!{f}`) beyond the benchmarks, proved by `sol_spec`: ERC20 over `msg.sender` (`approve`, `_mint`) and `Tally`. The benchmark contracts carry their own clauses and `spec!` theorems in `Examples/Benchmark/`. |
| `Examples/Benchmark/Syntax.lean` | What elaborates away, pinned by what it prints: units, `payable`/`address` casts, events and `emit`, errors and `require`/`revert` with a message or an error, enums, struct constructors, modifiers. |
| `Examples/Benchmark/Counter.lean`, `Examples/Benchmark/SimpleStorage.lean`, `Examples/Benchmark/Mapping.lean` | solkey's benchmark contracts `Counter`, `SimpleStorage`, `Mapping` and `NestedMapping` as published, with their `@custom:key` clauses as members, proved both as `dl!` formulas and as `spec!{f}` obligations. |
| `Examples/Benchmark/Purchase.lean` | solkey's benchmark `Purchase` with its enum, modifiers, errors and events as published (`msg.*` and `address(this).balance` as state variables), its clauses on `state` and `buyer` proved. |
| `Examples/Benchmark/Coin.lean` | solkey's benchmark `Coin`: `msg.sender` in `require` and as a mapping key; `mint` and `send` against their `@custom:key` clauses, the two `send` clauses `sol_close` does not close as runs. |
| `Examples/Benchmark/EtherWallet.lean` | solkey's benchmark `EtherWallet`: `withdraw` pays `msg.sender`; the owner kept, `address(this).balance` less by the amount, the ledger as a run. |
| `Examples/Benchmark/ERC20.lean` | solkey's benchmark ERC20 in its published `return true;` form, `mint`/`burn` calling `_mint`/`_burn`; every `@custom:key` postcondition proved. |
