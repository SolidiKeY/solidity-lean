# Module map

One line per module: what it defines. The module's own `/-!` docstring has
the detail; this file only says where to look.

**Start at `Theorems.lean`**: the main theorems on one page, in notation
(`⊢ φ → ⊨ φ`, `(P, σ) ⇓ σ'`, `⟦P⟧`), each proved by the original's name.

```
Solidity/  KeySort  AST  Syntax  Semantics  Update  SpecSyntax  Theorems
           Semantics/         the interpreter's satellites
           Calculus/          the taclets and everything proved about them
           Theory/            solkey's data-structure theories as free-term algebras
           Typing/            value typing, reachability
           SortCheck/         solkey's sort annotations, checked
           Counterexamples/   refutations that pin a design decision
           Evm/               the compiler and its simulation proof
           Tools/             the `#run`, `#wp`, `#verify`, … commands
           Corpus/            solkey's example suites (own target)
           Frontend/          solc's JSON AST read at elaboration time
           Solkey/            solkey's contracts imported from solc (own target)
           Examples/          the worked examples, in the default build
```

Layering: types and names (`AST`), the typed syntax (`Syntax`), the
interpreter (`Semantics`), terms and formulas (`Update`), the taclets
(`Calculus/Rules`), then what is proved about them. Imports are acyclic; a new
module goes in `Solidity.lean` (`scripts/check-orphans.mjs` fails on a module
nothing imports).

**Formulas read storage through the Theory.** Programs and updates run in the
interpreter, but `a ≐ b` (`Fml.eq`) compares `Tm.denote`s over `State.abs`,
the state as a Theory term, and is total as KeY's `=` is. A program comparison
`a == b` is `Fml.eqD`, `defined(a) ∧ defined(b) ∧ a ≐ b`. `Theory/Bridge/`
proves once that the interpreter's reads and writes are the Theory's on `abs`
(up to `StValue.Equiv`). A derivation rewrites terms by named term taclets
(`Calculus/TermTaclets.lean`, `Proves.rewrite`), each sound by its Theory
lemma (`TermTaclet.sound`).

## The language

| Module | What it defines |
|---|---|
| `KeySort.lean` | solkey's sort lattice as one type. Imports nothing. |
| `Eqns.lean` | `attribute [eqns l₁ … lₙ] f`: hand-named equation lemmas for a definition written with a recursor (irreducible, so `simp only [f]` rewrites constructor applications only; the kernel still reduces it). |
| `AST.lean` | Types (`PrimTy`/`Ty`/`RefTy`, `RefTy.fixed`), the struct table, operators, `Var`. |
| `Syntax.lean` | The typed syntax (`Val C p`, `SPath`, `Loc`, `MPath`, `Stmt C`), `Contract`/`FunDecl`, the elaborator behind `sol[C]{…}` and `contract!{…}` (a flat block's local renamed apart, `freshenBlocks`), and the quoter (`Prog.quote`). |
| `Scope.lean` | `Solidity.Core`'s contexts: `LTy`, `Ctx := List LTy`, positions `Idx`, suffixes `Ext` (scope ends), thinnings `Thin` (weakening), `Binders`. |
| `Syntax/Core.lean` | The typed syntax scoped (`Solidity.Core`, `docs/intrinsic.md`): `Stmt C Γ Γ'`/`Prog C Γ Γ'` over `Idx`, scoped branches and blocks, calls closed over their frame (`Args`, `CallRet`), the printers (names beside the context) and `Stmt.wk`.  Beside `Syntax.lean`'s until M4. |
| `Syntax/Resolve.lean` | Between the two: `erase` (positions to names, a block to its statements) and `resolve` (names to the newest position, branches, loop bodies and call bodies as scopes, a memory return moved into the call's frame), `resolve_erase`, `Prog.Fresh` (no binder reuses a name in scope; checked by `resolve` unless `strict := false`, `resolve_fresh`), and `Prog.resolveCheck`, the elaborator's locals check. |
| `Syntax/Splice.lean` | The elaborator's entry points, checked by `resolve` (`elabProg`, `elabProgAt`, `ctorProg`), `sol[C]{…}`/`sol{…}`, and their pins. |
| `Syntax/CoreQuote.lean` | The scoped syntax quoted (`Core.Prog.quote`, `Idx` as `here`/`there`, proofs `Eq.refl`), contexts shared and the term hash-conses (`quoteShared`); `Prog.defineCore` resolves, quotes and declares a block for the kernel to check. |
| `FreshNames.lean` | `FreshNames.ofTable`: the examples' names for the rules' fresh variables, one table per example; `FreshNames.clashes`. |
| `SpecSyntax.lean` | The specification language (`SolSpec.g4`: `SpecExpr`, `spec!(…)`) and a function's clauses (`FunSpec`). |
| `Semantics.lean` | The interpreter `Stmt.run`, following solc where KeY is more liberal (`docs/solc-alignment.md`); a loop's run as the least fixed point of its unwinding (`Loop.run`, `Loop.run_rel`); a deployment's `Contract.deployState` and `Contract.deploy`. |
| `Semantics/Properties.lean` | Read-after-write, frame and result-monad lemmas about the state operations, shared by every later layer. |
| `Semantics/Agree.lean` | `EnvAgreeExcept`: states agreeing off scratch names, and a frame lemma per evaluator. |
| `Semantics/WellFormed.lean` | `storageWtB`: well-formed storage (the shape `SVal.canon ∧ SVal.tight`, and words in range, `SVal.wordsB`) as a test the term `wt(storage)` runs; `SVal.isDfltB`, a default the kernel can recognise. |
| `Semantics/DecEq.lean` | `DecidableEq SVal`. |
| `Semantics/NoPanicSimp.lean` | The simp set `no_panic_simp` of the `*_noPanic` lemmas. |
| `Semantics/NoPanic.lean` | Only an `assert` panics: `NoPanic` of every operation, `Stmt.mayPanic`, `Prog.run_noPanic`; the `no_panic` tactic. |
| `Semantics/Callback.lean` | The callback reading of `transfer`, `send` and `try`: `ExecS`/`ExecP`, `holdsC`, `TransferSem`. |
| `Semantics/Mutability.lean` | A callee's mutability (`pure`, `view`, `nonpayable`) read off its inlined body (`Stmt.within`, `Prog.writes`), and its frame from `Stmt.run` (`Mutability.Frame`, `Prog.frame_of_within`, `Prog.pure_frame`, `Prog.view_frame`); a loop's frame, from the same `Stmt.within` (`Prog.loopFrame`, `Fml.loopAnon`, `Prog.loopFrame_run`: solkey's `#loopAnon`). |
| `Semantics/Core/Value.lean` | `PrimTy.Denote`: a typed primitive value (a `uint` an `Int` in range); its erasure `PrimTy.erase` and reading back `PrimTy.ofValue?`; `Core.toRes`, a revert as `none` (`docs/intrinsic.md`, M4a); `PrimTy.key`, a mapping key as the integer solc hashes (a `bool` as `0`/`1`). |
| `Semantics/Core/Ops.lean` | The operators on typed values (`BinOp.evalT`, `UnOp.evalT`; arithmetic on `Int`, the range check `PrimTy.ofInt?`), and their agreement with `evalBinop`/`applyUnOp` (`BinOp.evalT_erase`, `UnOp.evalT_erase`). |
| `Semantics/Core/Storage.lean` | Typed storage (`Solidity.Core`, M4b): `SVal T` mutual with `SFields` over `structDef` (exact members), `SList`/`SVec`/`SMap`; `Fold`, the recursor of the five families (`SVal.fold`, `match` twin `foldM`), and the functions on a whole value as folds with `eqns` equations (`erase`, `toList`, `SVec.set`, `defaultOf`, `strip`, `overlay`, `beq`), each recursor form with its `match` twin as `implemented_by` and a `_eq_…M` theorem; views computed from the index (`SVal.view`/`Shape`, `SFields.view`, `SVec.view`, `uncons`); `DecidableEq (SVal T)` and `(SFields fs)` by `beq`, reduced by `decide +kernel`; structural defaults `SVal.dflt` (fuel `rankBound`); typed paths `Path T U` (`append` by `Path.rec`, `index` by `casesOn`), `SRef C U` (`SRef.atKey`: a key as hashed, `PrimTy.key`), `Storage C := SFields C.vars`; find/save by `Path.rec` over `SVal.view`, with `match` twins `findM`/`findLiveM`/`saveM` (and `SFields.getM`/`setM`) as `implemented_by`, `checkIndex` (`inBounds` by `casesOn`), `len`, `push`, `pushPlace`, `pop` through the view, `delete`, `write`, revert as `none`. |
| `Semantics/Core/StorageErase.lean` | The typed storage operations erase to `Semantics.lean`'s, which are never stuck on erased inputs (`SVal.find_eq_findM` and the other twins, `SVal.find_erase`, `SVal.save_erase`, `SVal.dflt_erase`, `SVal.overlay_erase` under `TyNodup`, the `Storage` lemmas); `SVal.ofU`, an untyped value read back at its type. |
| `Semantics/Core/Heap.lean` | Typed heap (`Solidity.Core`, M4c): a heap typing `HTy := List RefTy` (identity = position), `HRef H R`, `MVal H T`/`MObj H R` computed from the typing (no mapping object), `Heap H`; `get`/`set`/`alloc` (grows to `H ++ [R]`, weakening along `<+:`), member and element reads and writes; `SVal.copyStToM` (`Grown`, a fold), `MVal.copyMToSt` by rank and type (no cycle arm); erasure `Heap.erase`, `Heap.into`. |
| `Semantics/Core/HeapErase.lean` | The typed heap operations erase to `Semantics.lean`'s on `σ.heap = hp.erase` (`getObj_erase`, `alloc_erase`, `SVal.copyStToM_erase`, `allocDefault_erase`, `MVal.copyMem_erase` via `RemOk`, `memWriteField_erase`, `memWriteIndex_erase`, `memArrayLen_erase`, `readField_erase`, `readIndex_erase`). |
| `Semantics/Core.lean` | The interpreter over the scoped syntax (`Solidity.Core`, `docs/intrinsic.md` M3): `LTy.Denote`, `Env C Γ` computed from the context (`get`/`set` on `Idx`, `drop` on `Ext`), `State C Γ` (`Semantics.State`'s global part, `glob`), one step per statement (`Run.*`), `Stmt.run`/`Prog.run` by the recursor with a compiled twin (`runC`, `Stmt.runR_eq`), scopes popped by `Prog.ext`; kernel-checked runs. |
| `Semantics/Core/TypedState.lean` | The typed state `Core.State` becomes at M4: `LTy.TDenote C H` (a value of its type, an `SRef`, an `HRef H R`), `TEnv C H Γ` (computed, weakened along a heap extension), `TState C Γ` (typed storage, heap typing `H` as a field, typed heap); `TState.erase` to `Core.State`, `adopt` (a `Grown` heap, locals weakened), `alloc`, `copyStToM`, `allocDefault`, `copyMToSt`, each with its `_erase` lemma. |
| `Semantics/Core/TypedRun.lean` | The typed run (M4 wiring): `SPath`/`Loc` to an `SRef`, `MLoc` to a heap address (`MAddr`: a struct member or an element of an `HRef`), `MPath` to the slot it holds (an `HRef` at a reference type), `Val.evalT` by `BinOp.evalT`/`UnOp.evalT`, `Stmt.trun`/`Prog.trun` on `TState` (the recursor, `match` twin `trunC`); halts only by `THalt` (`revert`, `panic`, `diverge`). |
| `Semantics/Core/TypedRunErase.lean` | The typed run erases to the scoped run (`Prog.trun_erase`, M4 wiring item 4): `TRes.Agrees` (the erased state, the same `revert`/`panic`; a typed `diverge` against anything), one lemma per `TRun.*` step against its `Run.*` (`StepAgrees`), the loop by its unwinding (`SumAgrees`); on `Prog.bridgeOk` programs (no `bool` mapping key, no storage copy at a type with a repeated member name), decided by evaluation. |
| `Semantics/Core/TypedRunWk.lean` | A weakened program runs as the program, typed (`Stmt.trun_wk`, `Prog.trun_wk`, W1): `τ.lift h d` (`TEnv.put`/`off`/`thin`), the background weakened along the heap a run grows (`TEnv.wk`, `offWk`), `TWkRel`; per-step lemmas (`TRun.*_wk`); frames run (`Frames.trun`); loops on `TLoop`: `run_map`, `run_unfold`, `run_induct`, `run_variant`. |
| `Semantics/Core/TypedRunFrame.lean` | A body within a mutability runs within its frame, typed (`Stmt.trun_frame`, `Prog.trun_frame`, W1): the heap and its typing kept (`TGFrame`, heaps compared by `HEq`), the locals below kept but where `writesAt d` lists them (`TLocAgree`); `TState.anon`, `TState.havoc`, and a state in a loop body's frame is one `{anon(xs)}`/`{havoc}` covers (`TState.eq_anonHavoc`, `Prog.trun_frame_anon`). |
| `Semantics/Core/TypedToSem.lean` | A typed state as `Semantics.lean`'s (`TState.toSem ns`, W1): bindings `LTy.TDenote.bind`, locals `TEnv.toSem`; a local found under its name (`lookup_toSem`), and how it moves with `push`/`setLocal` (`setBy`)/`drop`/`withStorage`/`havoc`/`adopt`; the bridge `toSem_eq` (= `σ.erase.erase ns`) and `agree_toSem` (`Agree`). |
| `Semantics/RunErase.lean` | The bridge (`docs/intrinsic.md` M3): `Prog.run_erase`/`Stmt.run_erase`, a fresh scoped block's run against `Semantics.lean`'s run of its erasure, up to the popped locals (`ResultsAgree`); `Agree`, `RunRel`, `Stmt.binders`, and each global operation natural in the locals (`*_nat`). |
| `TermSimp.lean` | The simp sets `tm_eval` and `tm_denote` of the generic term functions. |
| `Update.lean` | Terms as one signature (`Srt`, `Op0`…`Op3`, `Tm`; `Term`, `STerm`, … are its sorts, the old constructors abbreviations), their reading (`Tm.eval`, `Tm.denote`) and frame lemmas, parallel updates (`UpdElem`; a deployment's `.netMt` for `net := storeSt(mtSt, at(r), a)`, `.setBalance` for `selfBalance := a`, `.saveNetMt`), formulas with both modalities (`Fml`, `holds`, `Valid`), lowering of program expressions to terms. |
| `Theorems.lean` | The headline theorems in notation. |

## The calculus

| Module | What it defines |
|---|---|
| `Calculus/RuleSyntax.lean` | The `dl{ … }` notation: schemas (taclets, sequents `..Γ ⟹[R] ⟨[ s; ..ω ]⟩ φ`, update schemas `{u ‖ {u}u2}`), `tm{ … }` for terms, and the printers for taclets, premises, goals, terms (`pp.sol.key`: KeY's long forms). |
| `Calculus/Rules.lean` | `Taclet` (solkey's rules), `LeanTaclet` (rules solkey lacks), `Rule`, `CallbackTaclet`. |
| `Calculus/Core/Fml.lean` | Scoped terms, updates and formulas (`Solidity.Core`, M6a of `docs/intrinsic.md`): `Tm C Γ s`, `Upd C Γ Δ` (assign, declare, pop), `Frames` (`seq`, `pop .block`/`.capture`, `drop` by a `Thin`), `Fml C Γ` with `modal m P κ φ` and the hidden binder `bind`, `Premise C Γ Γ'` (no cover goal; `branches`, `cases`, `inv`, `inline`) and `Premise.fml`, `Frames.exit`, and `Fml.erase` to `Update.lean`'s. |
| `Calculus/Core/Lower.lean` | Scoped program expressions lowered to `Core.Tm` (`Val.lower`, …), and `lower_erase`: the old lowering of the erasure. |
| `Calculus/Core/Print.lean` | `Core.Fml.show`: a scoped formula printed as `RuleSyntax.lean` prints its erasure (`}` at a block's end, pops and hidden binders unprinted), pinned against it. |
| `Calculus/Core/Shift.lean` | A rule's schema variables shifted under its fresh locals (`Val.up` and its kin, `*.up_eq`: `wk up` without a `Thin`), and a call's body read under its caller (`Thin.atop`, `Idx.under`). |
| `Calculus/Core/Arms.lean` | The rule of each statement on scoped syntax (`Completeness.lean`'s arms): holes (`SHole`, `MHole`, `VHole`), reads, writes, copies, deletes, the conditional, `&&`/`||`, compound assignments, `++`, push/pop, payments, memory, `if`/`require`/`assert`; each arm names its taclet. |
| `Calculus/Core/Blocks.lean` | The rules of calls (inlined, the frame dropped under exported returns by `Premise.inline`), `try` (`Premise.branches`) and loops (`whileUnwind`, `loopExit`, the invariant rules, `Premise.inv`), and the loop frame (`Stmt.within`, `Prog.frame`). |
| `Calculus/Core/Step.lean` | The strategy on scoped formulas: `Stmt.step` (one `casesOn`, every statement a rule), `Fml.maxIdx`/`fresh`, `Fml.stepR` by `Fml.rec` with its compiled twin `Fml.stepAt` (`stepR_eq`), `symex`. |
| `Calculus/Core/Logic.lean` | What a scoped formula means over M3's `State C Γ`: `Tm.eval`/`denote` (locals by position, symbols on `State.glob`), `Upd.apply`, `Frames.run`, `holds` (the diamond, as an update or a modality, read from and into states whose `bool` locals hold `bool`s: `State.BoolOK`, `Modality.afterT`/`afterRunT`); `holds_exit`/`holds_modalK`; the premise shapes (`Premise.sound_update`, `_unfold`, `_inline`, `_bind`, `_capture`, `_split`, `_check`, `_done`); `Val.eval_up` (a shifted part reads as before); soundness of thirteen arms against `Core.Stmt.run`. |
| `Calculus/Core/SoundKit.lean` | The statement every arm's soundness proves (M6a): `Premise.Sound` (a premise in front of any rest gives `⟨ s; ω κ ⟩ φ`), `Stmt.StepSound` (in every state); a scoped term and an update never panic (`Tm.eval_noPanic`, `Upd.apply_noPanic`); the premise shapes as `Premise.Sound.*`. |
| `Calculus/Core/RunWk.lean` | A weakened program runs as the program (`Stmt.run_wk`, `Prog.run_wk`): the state of the wider context `τ.lift h d`, the locals the thinning drops kept (`WkRel`); a scope's end on both sides (`Thin.Over`); a loop every turn of which is lifted (`Loop.run_map`). |
| `Calculus/Core/RunFrame.lean` | A body within a mutability runs within its frame (`Stmt.run_frame`, `Prog.run_frame`, `Mutability.lean`'s `frame_of_within` on scoped syntax): the global part kept but storage and ledger (`GFrame`), the locals of the context `d` below kept but where `writesAt d` lists them (`LocAgree`); a state in a loop body's frame is one `{anon(xs)}` (`{havoc}`) covers (`holds_anonHavoc`, `Prog.frame_some`). |
| `Calculus/Core/SoundBlocks.lean` | Soundness of `Calculus/Core/Blocks.lean`'s arms against `Core.Stmt.run`: `whileUnwind` (`Loop.run_unfold`), `loopExit`, the rules that close to `false`, `try` under the box (each clause for every value its outcome decodes to). |
| `Calculus/Core/SoundCalls.lean` | Soundness of the call rule against `Run.call` (`Stmt.stepSound_call`): `expand_function_body` for each kind of result (`Premise.Sound.callNone`, `callVal`, `callRets`, `callMem`: the parameters declared, the body weakened by `Thin.atop` run in its frame by `Prog.run_wk`, the frame popped or dropped from under the returns) and `functionCallArgCapture` (`Args.eval_capture`). |
| `Calculus/Core/SoundLoops.lean` | Soundness of the loop invariant rules and the loop arm (`Stmt.stepSound_loop`): `whileInvariantBox` (the invariant at every head by `Loop.run_induct`, each head in the body's frame, `holds_anonHavoc`), `whileInvariantDiamond` (the body read under the variant's local keeps it, `Prog.run_wk`; the variant bounds the iterations, `Loop.run_variant`), the condition's update read into a state whose `bool` locals hold `bool`s (`State.BoolOK`). |
| `Calculus/Core/SoundArms.lean` | Soundness of the arms (M6a), part one: a statement read with a local pushed runs as before (`Run.*_push`, `OpLoc.Agree`, `MLoc.Agree`); the update arms of locals, storage writes, deletes, compound assignment and `++`/`--` (`sound_setLocal` … `sound_assignIncDec`), each `Premise.Sound.update`. |
| `Calculus/Core/SoundUpdates.lean` | The other update arms: push, pop, an alias bound to a pushed slot, transfer, send (`Premise.Sound.cases`), fresh memory objects and memory `delete`; `Premise.Sound.updateSim` (an update alike up to the halt). |
| `Calculus/Core/SoundCapture.lean` | A capture sound up to the halt (`Premise.Sound.captureSim`, `captureSPSim`, `captureMVSim`; `Res.Sim.err_bind` where the statement reads another part first); each statement's run by name (`Stmt.run_assign` …); the holes read once (`SHole.cont`, `MHole.cont`, `VHole.cont`, `fill_run`, `fill_push`), so a read unfolded into a hole (`SHole.readStep_sound`, `MHole.readStep_sound`), a value (`VHole.step_sound`, `lower_sound`) and a conditional (`ternaryStep_sound`) are sound for every hole. |
| `Calculus/Core/SoundLocal.lean` | The arms on locals: `localStep_sound` (with `&&`/`||`, `shortStep_sound`), `rebindStep_sound`, `opStep_sound`, `incStep_sound` (`OpLoc.unfoldRecv_sound`); `Premise.Sound.splitStuck` (a split on a condition that reads as no `bool`: stuck, so the box holds and the diamond does not read from the state, `Simple.eval_bool`); `Premise.Sound.split` (a split given its two branch runs and the stuck case; `iteStep`'s and `requireStep`'s simple conditions). |
| `Calculus/Core/SoundControl.lean` | `transferStep_sound`, `sendStep_sound`, `iteStep_sound` (a captured condition under `WkRuns`, the run of `Prog.wk up`), `requireStep_sound`, `assertStep_sound`; declarations with an initializer (`sound_declStorageInit`, `sound_declMemInit`). |
| `Calculus/Core/SoundStore.lean` | The storage arms: `assignStep_sound`, `copyStep_sound`, `assignFromMemStep_sound`, `deleteStep_sound`, `pushStep_sound`, `popStep_sound`; a block of captures run one push at a time (`Prog.run_declLocal_cons` and kin, `pushed2_drop`, `pushed3_drop`). |
| `Calculus/Core/SoundMem.lean` | The memory arms: `rebindMemStep_sound`, `memRefStep_sound`, `assignMemStep_sound`, `deleteMemStep_sound`, `sound_assignNew`. |
| `Calculus/Core/SoundStep.lean` | `Stmt.stepSound`: every arm of `Stmt.step` is sound (`Stmt.StepSound`), the block arms by `SoundCalls`/`SoundBlocks`/`SoundLoops`; `WkRuns.of_run_wk` (a block weakened under one local runs as before). |
| `Calculus/Core/HoldsErase.lean` | `holds_erase`: a scoped formula holds where its erasure does (`Update.lean`'s `holds`), in every agreeing untyped state, for `Fml.Plain` formulas; `Tm.eval_erase` (up to the locals a storage carries, `Srt.wl`), `Tm.denote_erase`, `Upd.apply_erase`, `Frames.run_erase`, `Agree.thin`/`dropNames`; one way each for a hidden binder (`holds_erase_bind`, scoped to erased) and `{anon(…)}` (`holds_of_erase_anon`, erased to scoped). |
| `Calculus/Core/Quote.lean` | Scoped formulas, terms, updates, frames and premises quoted back into `Expr` (`Core.Fml.quote`, `Tm.quote`, `Upd.quote`, `Frames.quote`, `Premise.quote`), hash-consed; a block alone is `Syntax/CoreQuote.lean`'s. |
| `Calculus/Core/Rules.lean` | The rule table on scoped statements (W1): `Rules.lean`'s `Taclet` and `LeanTaclet` lines copied verbatim (binders aside) by `scripts/core-rules.mjs` (`scripts/check-rule-text.sh` diffs the copies), read under `open scoped Solidity.Core.Schema` into scoped taclets (`RuleSyntax.schemaTacletCore`); the term symbols the lines write (`Tms`), the side conditions (`Loc.isTarget`, the holes' `isTarget`, …), `Prog.up`, a call's inlining `Premise.expandCall` and argument capture `Premise.argCapture` (`functionCallArgCapture`, stated by hand); `Rule`. |
| `Calculus/Core/Taclet.lean` | Each scoped taclet is the rule `Stmt.step` fires (`Taclet.toStep`, alias `step_eq`; `LeanTaclet.toStep`, `Rule.toStep`, `Rule.premise_unique`): one lemma per constructor (`Taclet.<rule>.toStep`), most written by `#derive_toStep` (`to_step_tac`), the rest by hand; `Premise.erase`, today's premise. |
| `Calculus/Core/RuleShapes.lean` | The scoped table's origins: today's rows by name (`RuleShapes.tacletOrigins`), and what scoping claims besides: `blockEmpty` (`Core.Taclet.blockEmpty`), `functionFrameEmpty` (with the call expansions); `taclets_partitioned` (308 claimed, 15 excused). |
| `Calculus/Core/PrintedRules.lean` | The scoped table's printed rules: today's rows by name, `blockEmpty` a solkey taclet not printed; `printed_rules_partitioned` as today's. |
| `Calculus/Core/Completeness.lean` | The rule a scoped statement fires, by name (`ruleOf?`, `#rule_of m s`): the constructor whose line matches (a hole's statement by the hole and part read off it, `holeCandidates`) and whose side conditions evaluate to true, its premise checked to be `Stmt.step`'s; for `#step`, `sol_derive?` and the proof tree. |
| `Calculus/Core/DelabLean.lean` | The printer of `Core.LeanTaclet`: `dl[LeanTaclet C k]{ … }` as `Rules.lean`'s, through `Calculus/Core/Delab.lean`'s translation (a loop's invariant rule with solkey's labels). |
| `Calculus/Core/RuleText.lean` | Every scoped rule prints as its twin in `Rules.lean`: `#check_rule_text` compares the printed lines (`Calculus/Core/Delab.lean` against `Rules.lean`'s delaborator) and lists the rules that differ, pinned; `#rule_text r` shows both. |
| `Calculus/Core/Delab.lean` | Scoped taclets, premises and formulas printed from their `Expr`, schema variables and all: each translated to its erasure's `Expr` (schema variables as twins of the erased type, positions as the names the term declared) and printed by `RuleSyntax.lean`'s printers; `}` at a block's end (`core_item`, printing only); the delaborators for `Core.Taclet`, `Core.Premise`, `Core.Fml` (calls and `try` as the statements they come from; a frame end by `Thin` as nothing) and `Core.Proves` (today's sequent). |
| `Calculus/Core/Proves.lean` | The scoped sequent: `Hyps C Γ₀ Γ` (a telescope: updates, `∀` and the hidden binder extend the scope), `Hyps.wrap`/`fresh`/`boxOnly`/`anonHavoc`, and `Proves` with one rule per premise kind (`update`, `unfold`, `bind`, `split` with KeY's two goals, `check`, `done`, `branches`, `cases`, `inv`, `inline`), each firing `Stmt.step`'s rule, and `intro`, `allIntro`, `updIntro`, `bindIntro`, `empty`, `closeTrue`. |
| `Calculus/Core/ProvesSound.lean` | Soundness of the scoped sequent, unconditional: `Proves.sound`, `Proves.valid` (axioms: Lean's three), from `Stmt.sound` (every rule's premise sound in every state, `Calculus/Core/SoundKit.lean`'s `Premise.Sound`, collected from `Stmt.stepSound` by `Stmt.Sound.of_stepSound`); `Hyps.wrap_and`/`wrap_conj`/`wrap_valid`. |
| `Calculus/Core/NotationResolve.lean` | `Update.lean`'s terms, updates and formulas read scoped over a named context (`Tm.resolveN`, `Upd.resolveN`: a target in scope at its type assigned, any other declared; `Fml.resolveN`), `Fml.closeN` (locals bound outermost), and `Core.Post C Γ`, a postcondition at the context it stands in. |
| `Calculus/Core/Notation.lean` | `cdl!{ φ }`/`cdl[C, m]{ φ }`: `dl!{}`'s text read into `Core.Fml C []` (`elabFmlC`): parameters bound outermost (a `uint` by `∀`, an alias by a hidden binder), only when read before bound; a Lean formula elaborated at the context of its place. |
| `Calculus/Core/Spec.lean` | Obligations scoped: `Problem.fml`/`ctorFml` over the parameters' context (`paramsN`, bound by `∀`), `Problem.resolve`/`ofLegacy`/`ctor`; `specObligation` (`cspec!{f}`): today's read in the parameters' context, `old`/`oldNet` declared at `LTy.old`/`.oldNet`, parameters by hidden binders, erasing to today's; `cproblem!{constructor}`. |
| `Calculus/Core/ProofTree.lean` | The proof tree of a scoped goal `H ⊢ φ` (`Core.ProofTree.build`, `ofFormula`), as `Calculus/ProofTree.lean`'s `Tree`: each rule the one `ruleOf?` names, applied as `apply update (Taclet.toStep .r)`; scope ends and hidden binders folded into the node before them; leaves closed by `closeTrue` and `Config.closers`; `Proves.impRight`/`allRight`/`emptyModality`. |
| `Calculus/Core/Callback.lean` | The callback taclets on scoped statements (`Core.CallbackTaclet`: `transferWithCallbackBox`, `sendWithCallbackBox`, `tryCallWithCallbackBox`, `Rules.lean`'s lines read under `Core.Schema`), each its no-callback twin (`toTaclet`) and so `Stmt.step`'s (`toStep`); `ProvesC` (sequents `dl{ ..H ⟹ᶜ[I] φ }`, the invariant a closed formula read past a dropping update, `Fml.closedAt`); their printers. |
| `Calculus/Core/Surface.lean` | The flip switch, `open scoped Solidity.Core.Surface`: `dl!{}`/`dl[C]{}` read as `cdl…`, `spec!`/`problem!` as `cspec…`/`cproblem…`, `⊨` by the formula's type (`valid%`), `⊢` the scoped sequent; `surfaceOn` for the commands. |
| `Semantics/Core/Callback.lean` | The callback semantics over the typed run (W1): `COut C H Γ` (over `Out`, the heap's growth carried), an invariant read on the global part (`StateInv`, `StateInv.at`), `ExecS`/`ExecP`/`ExecF` (no stuck arms, no failed entries; `TState.havoc` over typed storage; a call's locals given back by `TRun.callLeave`); the deterministic run is a callback run (`Prog.exec_run`, `Frames.exec_run`), the only one with no payment (`ExecP.eq_run`, `ExecP.forall_iff`). `holdsC` waits for `holds` on typed states (W2). |
| `Calculus/KeyTaclets.lean` | The 323 taclets of `solidityProgramRules.key` as one type, with `KeyOrigin`. |
| `Calculus/RuleShapes.lean` | Which solkey taclets each constructor transcribes, checked (`taclets_partitioned`); KeY's taclet of an operator family at an operator (`keyTacletAt`). |
| `Calculus/PrintedRules.lean` | The printed rules and the constructor for each. |
| `Calculus/Completeness.lean` | `Stmt.step`, the rule for every statement, and `Stmt.complete`. |
| `Calculus/Uniqueness.lean` | One rule per statement: every derivation's premise is `Stmt.step`'s. |
| `Calculus/Progress.lean` | A formula with a modality always steps. |
| `Calculus/Termination.lean` | Weights, `Fml.measure`, `symex_normalizes`. |
| `Calculus/NoPanic.lean` | A term never panics: `Tm.eval_noPanic`, `Upd.apply_ne_panic`. |
| `Calculus/SoundKit.lean` | `SameOk`, `Premise.Correct` and the tactics the soundness proofs use. |
| `Calculus/SoundUpdate.lean` | Every taclet with an update premise has the statement's effect. |
| `Calculus/SoundUnfold.lean` | Every unfolding taclet runs like its statement off the fresh names. |
| `Calculus/SoundLoop.lean` | The loop invariant rules sound: `Stmt.loop_inv_box`, `Stmt.loop_inv_diamond`, `Loop.run_variant`. |
| `Calculus/RuleSoundness.lean` | `Taclet.sound`, `LeanTaclet.sound`, `Rule.sound`. |
| `Calculus/Logic.lean` | The sequent calculus `Proves` (`⊢` all rules, `⊢ₖ` solkey's), its rules written as sequents `dl{ ..Γ, c ⟹[R] φ }`, solkey's names for them (`impRight`, `allRight`, …) and `Proves.sound`; the update, rewrite and close rules (`close`, `closeFalse`). |
| `Calculus/Callback.lean` | `CallbackTaclet.sound`, `CallbackTaclet.sound_send`, `ProvesC` (sequents `dl{ ..Γ ⟹ᶜ[I] φ }`) and `ProvesC.sound`. |
| `Calculus/SolkeyFragment.lean` | `Stmt.inSolkey m`, where solkey's rules alone are the calculus under a modality; and where they fall short. |
| `Calculus/Symex.lean` | `Fml.step`, `symex`, `symex_sound`; `sol_step`, `sol_symex`, `sol_derive`; `Proves.closeTrue` and `Proves.splitBox`, a box split with KeY's two goals. |
| `Calculus/Close.lean` | `sol_close`: first-order goals by weakest preconditions, and `sol_close_mt` from a deployment's empty storage. Its docstring lists what it does not close. |
| `Calculus/CloseTests.lean` | What `sol_close` closes, pinned. |
| `Calculus/ReadWrite.lean` | Reads after writes: the four-way path comparison; the simp sets `close_rw`, `decide_eval`. |
| `Calculus/MemNames.lean` | The interpreter facts the memory closer rests on: a copy into memory is a tree of the counters it used (`copyStToM_interval`, `copyStToM_resolve_inj`), names fixed at their birth (`Births`), copies read as their sources both ways, when a copy halts. |
| `Calculus/DecideLang.lean` | `sol_decide`'s target language: terms, paths, storages and memories (`LTerm`, `LStor`, `LMem`, `LId`) read in the initial state, and the formulas over them; constants folded where a term is built (`LTerm.mkBin`/`mkUn`), literal powers up to the exponent 256 (`powBig`). |
| `Calculus/KeyNotation.lean` | The closer's notation in solkey's spelling: `key{ save(st, P, w) }` (names are Lean or pattern variables) and `key!{ find(storage, alice.age) }` (names are literals), macros to the `L*` constructors; `ppKey` and the delaborators print them back (no `whnf`, cut off at `keyCutoff` nodes, off with `pp.sol.dl false`). |
| `Calculus/MemRead.lean` | The memory clauses, as solkey's memory taclets: reads walked over the writes to a name's birth (`readT`, `readI`), the guards of names and writes, each exact against the interpreter. Each arm is written in `key{}` at its taclet's schema variables (`key{ write(mem, id1, a1, v) }, id2, a2` for `readOnWrite`), the taclet named above it. |
| `Calculus/MemTheory.lean` | The memory readers against `Theory/Memory.lean`: a memory as a Theory term (`LMem.toTheory`), and `readT`/`readI` answering what `Memory.readIn`/`readId` read, each arm by its taclet's lemma or by definition (`LMem.readT_agree`, `LMem.readI_agree`), a default under `DeclAlong`, the member table along the read's path. |
| `Calculus/SlotLemmas.lean` | The slots past an array's end, read live: a slot-level write (through a stale alias) read at, apart from, below and above its path; the first slot past the end that a `push()` recycles; what a `delete`, a copy and a push leave there. |
| `Calculus/Decide.lean` | `sol_decide`: reads of writes as case trees on key equalities, over the live storage; pushes, pops and storage copies (`LStor.arr`, `LStor.copy`); the updates' memory as an `LMem`, an allocation's pair kept whole (`pairL`), a copy from storage as that pair (`pairMem`), a copy of memory into storage as a view (`LStor.view`, `memL`). The memory clauses (`LMem.readU`/`objU`/`okU` and their `F` twins), the storage clauses (`LStor.readU`/`hasU`/`lenU`/`mapU`/`slot*`/`okE`/`cpokU`, `LTerm.elim` and their `F` twins, each arm commented with its taclet), the leaf builders and the `Op*.toL` table match in `key{}`: the patterns are written in it, the bodies, which call Lean functions, mostly raw. |
| `Calculus/DecideSyn.lean` | `LFml.syn`: a reduction closed by its terms, KeY's syntactic closing; `sol_decide`'s first try. `core`/`strict`/`arith` match in `key{}`. |
| `Calculus/DecideComplete.lean` | The starting storage's reads are realizable; `Fml.valid_iff_cons`. |
| `Calculus/Closer.lean` | `LFml.close`: the closer, KeY's first-order and arithmetic taclets as clauses of one `Bool` (ground evaluation, `applyEq`, `bool` case splits, intervals by constants and bounds below, reads typed by `wt`'s layout, the slot a `push()` recycles typed by its element type, a copy into memory of a type with no mapping, `Facts.cpokInit`), `LFml.close_holds`; `LFml.fits`, the size count; literal powers folded (`foldBin`). The folds, `simpE` and the `Facts` arms on terms match in `key{}`. |
| `Calculus/Derive.lean` | The strategy as one kernel evaluation: `Derive.residue` (per-goal fresh names, any number of branches, a box split's two goals as `Proves.splitBox`'s, a step budget over the whole derivation, leaves closed by `LFml.close` with `wt` read as a layout, parallel updates split, a push's returned alias read after the push, `Derive.fitsClose` bounding a leaf and its reduction, a split on a ground condition pruned by `Proves.closeFalse`, `Derive.splitRes`, the invariant rule's goals (`Premise.inv`: the invariant, then a split's goals past `Hyp.loopAnon`)), `Proves.of_residue`, `Proves.close_dropWt`; `sol_prove`, `sol_prove?`. |
| `Calculus/Problem.lean` | solkey's obligation forms (`Problem.fml`: `∀x̄. wt(storage) → [f] true` or `⟨f⟩ true`), the constructor's `Problem.ctorFml` from `Problem.deployUpd` (`problem!{constructor}`, `Problem.deploy_of_valid`), `Fml.wt`, `shape_iff_reachable`, `wt_iff_reachable`, `initStorage_wt`, `ReachableU` (the untyped run of a resolved block), `ReachableU.reachableS` and `ReachableU.reachable` (words, keys and slots in range); `Problem.text` in solkey's syntax. |
| `Calculus/Spec.lean` | Specifications compiled to dynamic logic as solkey's `SpecCompiler` does; `spec[C]{f}`, `spec!{constructor}` (a deployment's), `sol_spec`. |
| `Calculus/Contracts.lean` | Function contracts: `FunContract` and its obligation, `useContract` (goals "pre" and "post", `{havoc}` for a `nonpayable` callee only) and `FunContract.sound`. |
| `Calculus/Notation.lean` | `dl[C]{ … }` and `dl!{ … }`: concrete formulas read against a contract; `dl![m]{ … }`, `⟨[ ]⟩` at a modality `m`; a Lean formula where a formula stands; `Γ ⟹ φ` lines; `st!{ … }`, `pt!{ … }` for a storage term and a path. |
| `Calculus/Quote.lean` | Quoters from formulas back to terms, so the kernel re-checks a computed goal. |
| `Calculus/Chains.lean` | Derivations as values: `~>`, `~*>`, chain terms `A ~[r]~> B ~*> C …` (`Fml.Via`), `sol_chain`, `#derivation`; lines at a modality `m` over a postcondition `φ : Post C`; rewrite links (`~[sequentialToParallel]~>`, `~[findOnSave]~>`), proved over `m` by `cases m` where a merge compares modalities. |
| `Calculus/Sequents.lean` | `sequent!{ Γ ⟹ φ }`: the goals of a `⊢` walk (`Proves`) read back, for checked `show` lines; a chain under a context (`Fml.Steps.valid_in`). |
| `Calculus/ProofTree.lean` | solkey's proof tree of a goal `Γ ⊢ φ` (`ProofTree.build`, `Tree.rows`, `Tree.toJson`), with KeY's rule names and branch labels (`branchLabels`); `sol_derive?`, the walk it is, and `sol_chain?`, a derivation as its `calc`. |
| `Calculus/UpdateRules.lean` | KeY's update simplification as `UpdRule`s (`dl_schema{ {u}{u2}φ }`), and the semantics of the update constructors. |
| `Calculus/StateParts.lean` | Readings compared where a write looks (`Srt.AgreePart`: a storage by its storage, a memory by its heap): `{memory := M}` and `{L ‖ storage := s}` substituted into an update's right-hand sides, memory reads included (`Tm.withMem`, `Tm.substSt`: an index check or push slot becomes `p[i]@s`, `p[p.length]@s`), and the two merges' soundness. |
| `Calculus/LastLine.lean` | `#last_line chain`: the chain ends at a last line — no program left, one parallel update in front of each goal, no rewrite a chain takes still applies (every one `~=>` tries but `simplifyUpdate`, under either modality); silent when it does, else one error with what is left and the rewrite that goes on. |
| `Calculus/ChainGen.lean` | A whole chain written out: `#chain φ` and `#chain_rest c` (the strategy's links grouped as the worked examples print them, then one rewrite a link until the line is last, as one chain term to paste — in segments composed by `Fml.Leads.via` past ten links — and a `FreshNames` table to fill), `sol_chain?` on `φ ~~> ψ`, and `sol_rws [r₁, …]` / `sol_rws?`, a `~~>` by several rewrites (for tests and proofs; a worked chain writes each rewrite as its own link). |
| `Calculus/ChainRewrites.lean` | The lines after a chain's program as rewrites of the line with their soundness (`LineRw`): update merges (a storage write shadowed by one over it dropped; a memory write, or locals beside a storage or memory write, substituted into the update after), update rules, Theory laws — in an update's right-hand side under any modality where the update holds the write the law reads back (`Upd.covers`), or where the law reads a write member-wise, as solkey does (`Term.base?`, `Term.base_eval`) — and the laws of memory reads (`EvalLaw`: `readOnWrite`, `findCopyMem`, `readCopySt`), refinements of the interpreter applied where the update holds the write read back (`Upd.coversEval`). |
| `Calculus/ChainBranches.lean` | Rewrites under a branch, each along a skeleton of the line the elaborator reads off it (`Skel`, so that a postcondition variable is never cased on): `applyOnRigid` pushed through `∧`, `→`, `¬` (`Fml.push`, an equivalence for an update that cannot halt; `Fml.pushBox` under the box, one direction, antecedents and negated parts kept whole), KeY's `applyOnPV` under an update that cannot be applied whole (a local it binds last to a literal read as that literal in the equations below, the update kept), KeY's `concrete` folds (`Fml.concrete`: `true ∧ A`, `false → A`, `¬false`, two literals compared, a literal defined), and a rewrite at the first node of the skeleton where it fits (`Fml.inSkeleton`, `LineRw.mergeIn`: a merge under a branch). |
| `Calculus/Literals.lean` | KeY's `*_literals` taclets as `LitLaw` (`add_literals`, `sub_literals`, `div_literals` in `uint` range, `leq_literals`, `less_literals`, `greater_literals`, `geq_literals`), exact laws (`LitLaw.exact`: the left side returns the literal in every state), rewritten in an update's right-hand sides, memory terms included, under any modality with no premise (`LineRw.lit`) and in the equations and `defined(…)`s of a line's skeleton (`LineRw.litEq`). |
| `Calculus/TermRules.lean` | Theory equations as rewrite rules: `Term.Theq`, `Fml.rwEq` and its soundness. |
| `Calculus/TermTaclets.lean` | `TermTaclet`: the Theory's read-back rules on terms (in `tm{ … }`), their side conditions, and `TermTaclet.sound`. |
| `Calculus/TheoryRewrite.lean` | A Theory lemma as a rewrite rule (`theoryRewrite`, `sol_rw`). |
| `Calculus/Rewrite.lean` | The steps after the program: `rw [h]`, `eqDSplit`, `andSplit`, `sol_apply_upd`, `sol_upd`, `sol_merge`. |

## The data-structure theories

solkey's `find`/`save`/`read`/`write` are uninterpreted symbols whose meaning is
a taclet set. These modules are that theory as terms, each taclet a theorem.
The map from taclet to theorem is `docs/lean-key-rule-map.md`.

| Module | What it defines |
|---|---|
| `Theory/Terms.lean` | The mutual sorts `Struct`/`StValue`/`Memory`, the readers, `StValue.Equiv`. |
| `Theory/Storage.lean` | `structRules.key`'s taclets: `save`, `storeAt`, the delete family, `diverges`. |
| `Theory/Copy.lean` | The copying write `copyTo` and the array writes (`pushT`, `popT`, …). |
| `Theory/Memory.lean` | `memoryRules.key`'s taclets and `new`. |
| `Theory/CrossDomain.lean` | `structMemoryRules.key`'s four taclets. |
| `Theory/Observe.lean` | Congruence for `StValue.Equiv`: every operation respects it. |
| `Theory/Abs.lean` | The interpreter's storage as a Theory term (`SVal.abs`, `State.abs`). |
| `Theory/Bridge/Find.lean`, `Save.lean` | The interpreter's read and save against `findSt` and `save` on `abs`. |
| `Theory/Bridge/Delete.lean` | `defaultOf` and `delete` against `delValue` and `delAt`. |
| `Theory/Bridge/Copy.lean`, `CopyArray.lean` | `overlay`, `strip` and assignment against `copyVal`, `stripVal`, `copyTo`. |
| `Theory/Bridge/Push.lean` | `push`/`pop` against `pushT`/`shrinkT`/`popT`. |
| `Theory/Bridge/Denote.lean` | `Term.denote_eval`, `holds_eqD_iff`. The one Theory module that imports `Update`. |
| `Theory/Rewrite.lean` | `TheoryRule`: a constructor per printed rewrite rule, and the lemma behind each. |

## Typing and sort faithfulness

| Module | What it defines |
|---|---|
| `Typing/Storage.lean` | `Layout`, `SVal.hasTy`, read typing, write inversions, runtime sorts. |
| `Typing/StoragePreservation.lean` | `save` keeps a value's type. |
| `Typing/State.lean` | `StateWT`, the invariant of a state's global part (storage, heap, allocation counter); copy typing. |
| `Typing/Soundness.lean` | Type soundness of the scoped run: `Core.Stmt.run_wt`, `Core.Prog.run_wt` (`RunWT`: `StateWT` and every local of its type); `RunInv`, the scope cases every run invariant shares. |
| `Typing/TypedWT.lean` | `RunWT` by construction: a typed state erases to a well-typed one (`Core.TState.erase_wt`, under `HTy.toHeapTy`), for state variables and heap types that reach no struct with a repeated member name (`Ty.nodupDeep`). |
| `Typing/StraightRun.lean` | Straight programs (`Core.Prog.straight`: simple values assigned, aliases bound, defaults pushed, `pop`, `delete`, blocks; no loop, length or call): on the bridge, their typed run never diverges (`Prog.trun_noDiv`), so it ends where the scoped run does (`Prog.trun_of_run`). |
| `Typing/Reachability.lean` | Every reachable storage is canonical (`Core.Prog.run_canon`); `Reachable` is a bridged scoped program's typed run (`Core.Prog.trun`) from the initial state, `ReachableS` the scoped run's (`Reachable.reachableS`). |
| `Typing/Constructibility.lean` | The converse: reachable ⇔ canonical ∧ tight; the builder `Core.Build.rootsProg` is a straight scoped program (`rootsProg_straight`), so the typed run reaches what it builds; `Core.Prog.run_tight`; `ReachableS.reachable`. |
| `Typing/CanonTest.lean` | The tests `wt(storage)` runs decide `canon` and `tight` (`SVal.canonB_iff`, `SVal.tightB_iff`); a default is canonical (`defaultForTy_canonB`). |
| `SortCheck/Annotations.lean` | The taclets' read-sort annotations, transcribed from the `.key` file. |
| `SortCheck/Parser.lean` | Token-level `.key` scanner and the `conforms` cross-check. |
| `SortCheck/Faithfulness.lean` | Each annotation holds of what a well-typed run reads. |
| `SolkeyCheck.lean` (root) | `lake exe solkeycheck`. |
| `Counterexamples/*.lean` | Four refutations pinning a design decision: `DeleteFamilyGenericOverlap`, `StaticRuntimeSort`, `PreFixSortAnnotations`, `WellTypedNecessity`. |

## The EVM compiler

`docs/compiler-verification.md` has the theorem, the fragment and what is out.

| Module | What it defines |
|---|---|
| `Evm/Machine.lean` | A straight-line EVM: slots as terms, wrapping words, relative forward jumps, the accounts' balances. |
| `Evm/Compile.lean` | The compiler for the fragment `wtStmt`, with solc's guards. |
| `Evm/Repr.lean` | The storage layout and the representation relation. |
| `Evm/Signed.lean` | The signed guard sequences, exact on two's complement. |
| `Evm/Exp.lean` | `**`: solc's `checked_exp_unsigned`, unrolled. |
| `Evm/Correctness.lean` | `compile_correct`, `compile_box`, `compile_net`, `compile_exact`, `compile_storage`, `not_stuck`. |
| `Evm/Examples.lean` | Compiled programs run by `decide`. |
| `Evm/CoreCompile.lean` | The compiler over the scoped syntax (M5, `docs/intrinsic.md`): a local at its level (`cell`, `lvl`), a call's body in its own frame, the fragment `inFrag` over `Frag Γ` (alias flags only), `compileStmt_erase` (the same code as `Evm/Compile.lean`'s up to the memory cells) and `pushes_erase`.  Beside it until M4. |
| `Evm/CoreExamples.lean` | `Evm/Examples.lean`'s programs resolved and compiled by `Evm/CoreCompile.lean`, run by `decide +kernel`. |
| `Evm/CoreSim.lean` | `Sim` over the scoped syntax (M5, W1): the locals by position, typed (`Look C Γ`, `Seen`: a value, an alias's `SRef`), declarations as `Look.cons` (`Sim.consVal`/`consAlias`/`consFragile`/`consDead`), a scope's end as `Sim.drop`, the fragment's flags (`Sim.flags`, `meet`, `storeDrop`), a call's frame (`Sim.enter`, `Sim.return`); compiled code at base `b` stores to no level below `b` (`storesFrom_compileStmt`, `storesFrom_callFrame`, `exec_mem`). |
| `Evm/CoreExpr.lean` | The expression lemmas over the typed run (W1): `TState.sem`, `Look.ofTEnv` (`TEnv.get` as `Look`), `ValOutT`/`LocOutT`, `simple_sim`, `spath_sim`, `loc_sim`, `val_sim`. |
| `Evm/CoreStmt.lean` | One lemma per statement of the fragment over the typed run (W1), a storage write read back typed (`into_ok`): `StmtOut` (with `Keeps`: cells below the frame, array lengths), `Stmt.asserts`, `assign_sim` … `transfer_sim`. |
| `Evm/CoreCorrect.lean` | `stmt_sim`/`prog_sim` over `Core` and `Prog.trun` (within `maxHeartbeats 10000`) (one lemma per family, `ite_sim`, `block_sim`, `callNone_sim`/`callVal_sim`), then `compile_correct`, `compile_exact`, `compile_box`, `compile_net`, `compile_storage`; no `not_stuck` (no stuck outcome). |
| `Evm/CoreInterpreter.lean` | `Evm/Examples.lean`'s interpreter theorems over `Core.Prog.trun` (`setAge_interpreter`, `overflow_interpreter`, `payOwner_interpreter`, `callTwice_interpreter`), from `Evm/CoreExamples.lean`'s machine runs. |

## Tools

Commands for people; they prove nothing beyond the certificates they check.
`Examples/Tools.lean` and `Examples/Verify.lean` pin their output.

| Module | What it defines |
|---|---|
| `Tools/Show.lean` | Printers for storage values, states, transactions, clauses. |
| `Tools/Common.lean` | Shared plumbing: resolving `C` / `C.f`, evaluating terms, report layout. |
| `Tools/Run.lean` | `#run C.f(args) [from σ] [with msg.sender := n, …]`: the typed run from a fresh state; `#deploy C(args) [with …]`, a deployment (`Contract.deploy`). |
| `Tools/Inspect.lean` | `#wp φ`, `#step φ`, `#taclet r`. |
| `Tools/CoreInspect.lean` | `#wp φ`, `#step φ`, `#proof_tree φ`, `#proof_node n φ`, `#proof_tree_json φ` on a scoped formula (`Core.Fml C Γ`): the scoped strategy compiled, its result quoted and printed by `Core.Delab`; the tree by `Core.ProofTree.ofFormula`. |
| `Tools/DiffTest.lean` | `#difftest C[.f]`: the typed run against `Evm/CoreCompile.lean`'s code on random storages. |
| `Tools/Counterexample.lean` | `Fml.eval3`, witness search and shrinking, `#counterexample`. |
| `Tools/Verify.lean` | `#verify C[.f]`: each spec'd function proved, refuted or stuck. |
| `Tools/ProofTree.lean` | `#proof_tree φ`, `#proof_node n φ`, `#proof_tree_json φ`: solkey's view of the tree of `⊢ φ`. |

## The solkey corpus

`SolidityCorpus` (`lake build SolidityCorpus`): each function of solkey's `.sol`
suites, generated by `scripts/solkey-port.mjs` into `Solidity/Corpus/`, stated
at the contract's initial store and decided by the kernel; `TestSuite`'s rows
are read off `TestSuite/Report.lean` and its derived obligations restated as
corollaries.  `./scripts/check-corpus.sh` checks the verdicts against
`tests/solkey/expected.tsv`, `./scripts/check-testsuite.sh` audits the
TestSuite rows without Lean; `docs/corpus-parity.md` is the scoreboard.

| Module | What it defines |
|---|---|
| `Corpus/Basic.lean` | The corpus's obligation `Diamond σ P`, `corpus_decide` (resolved, run typed: `trunOk`), the stores as typed starts. |
| `Corpus/Imported.lean` | `testSuite_agrees` (the hand-written `TestSuite`'s roots are the imported one's), `Box`, `diamond_of_proved`, `box_of_proved`. |
| `Corpus/TestSuite.lean` | Generated: each derived `TestSuite` obligation with no parameters at `Solkey.TestSuite.initState`. |

## The solc front end

`SolkeyTestSuite` (`lake build SolkeyTestSuite`): solkey's `TestSuite.sol` from
the AST the pinned soljson writes (`scripts/solc-ast.mjs` makes
`tests/solc/TestSuite.ast.json`; `./scripts/check-solc-ast.sh` re-derives and
diffs it).  `docs/testsuite-proofs.md` has the counts and timings.

| Module | What it defines |
|---|---|
| `Frontend/SolcJson.lean` | solc's JSON AST (`Lean.Json`) printed as `sol` text per function: `readContract`, `Gap`, `Tag`; the struct table checked member by member; the functions called by name as `contract!` members, callees first; the constructor (`ctor`, a root of the calls) and the state variables' initializers (`initMembers`, `initGap`). |
| `Frontend/Import.lean` | `solc_import "f.json" hash 0x… as N renaming A => B`: `N : Contract`, `N.f : Prog N` per function, `N.constructor : Prog N` (a deployment, `constructor(x̄);`), `N.report : List ImportRow`; one `evalExpr`.  `solc_scoped N`, the scoped syntax's lint: `N.f.core : Core.Prog N Γ Γ'` per program, checked by the kernel. |
| `Solkey/TestSuite.lean` | `Solkey.TestSuite`, its 449 programs and the report, pinned. |
| `Solkey/TestSuiteScoped.lean` | `solc_scoped Solkey.TestSuite`: the 449 programs scoped, in a module of their own (the kernel's check is a third of the import's). |
| `Solkey/Constructors.lean` | solkey's `Counter.sol` and `EtherWallet.sol` imported (`tests/solc/Counter.ast.json`, `tests/solc/EtherWallet.ast.json`): their constructors and initializers, and `EtherWallet`'s constructor obligation derived; `tests/solc/CtorGap.sol` and `tests/solc/InitGap.sol` pin what the import leaves out. |
| `Frontend/Problems.lean` | `solc_problems N` (`N.f.problem : Fml N` per program; the constructor's `Problem.ctorFml`), `solc_scoped_problems N` (`N.f.problem.core : Core.Fml N []`, kernel-checked), `#solkey_problem`, `#solkey_scan`, `#solkey_derive?` (the replays to paste, when they fit `maxHeartbeats`), `#solkey_obligations` (derived, checked against `⊢ N.f.problem` and Lean's three axioms / pending). |
| `TestSuite/Problems.lean` | The 437 statements of `Solkey.TestSuite`, two pinned in solkey's syntax, `initState_wt`. |
| `TestSuite/Derived1.lean` … `TestSuite/Derived12.lean` | `Solkey.TestSuite.f.proved : ⊢ Solkey.TestSuite.f.problem`, 40, 40, 40, 40, 40, 37, 40, 23, 40, 40, 11 and 20 (411 in all), by `sol_prove` and explicit leaf tactics; 7 and 8 are what pushes, pops and storage copies added, 9 to 11 what memory added, 12 what copies between memory and storage added. |
| `TestSuite/Derived13.lean` | The obligations that write or push through an alias a `pop` made dangle (`LStor.stale`), by `sol_prove`: four of the five; `testArrayCopyClearsOldElements` stays pending (415 in all). |
| `TestSuite/Derived14.lean` | solkey `1b4341a303`'s twenty new obligations (`send`, internal calls, `return`, tuples), each by a bare `sol_prove` (435 in all); `returnEarly` and `tupleReturnDiscardsComponents` fit `Derive.replayFits` since ground splits are pruned (`Derive.splitRes`). |
| `TestSuite/Report.lean` | The pinned count: derived, pending (named), and the fifteen with no statement (excluded, skipped, and the twelve internal helpers). |
| `TestSuite/Suggestions.lean` | `#solkey_derive?` suggestions pinned by name, off the `Derived` modules' import path; `returnEarly` and `tupleReturnDiscardsComponents` pinned as derived since ground splits are pruned. |

## Examples

Two directories, by proof style (`.claude/rules/derivations.md`).

`Examples/Chains/` — the calculus's worked examples, one file per section in
its order, each example a chain in its printed lines and fresh names:

| Module | Its examples |
|---|---|
| `Examples/Chains/Storage.lean` | Storage writes and reads, roots, rebinding, index, `push`/`pop`, nonsimple paths, side effects in receiver and index. |
| `Examples/Chains/StorageArrays.lean`, `StorageDelete.lean` | The further storage array cases; storage `delete`. |
| `Examples/Chains/StorageCoverage.lean` | One chain per storage rule, from a concrete state. |
| `Examples/Chains/Arithmetic.lean` | The compound storage update. |
| `Examples/Chains/Memory.lean`, `MemoryDelete.lean`, `MemoryArrays.lean` | Memory aliasing, writes and reads; memory `delete`; memory arrays. |
| `Examples/Chains/MemoryCoverage.lean` | One chain per memory rule, from a concrete state. |
| `Examples/Chains/StorageToMemory.lean`, `MemoryToStorage.lean` | The copies between the two, with lazy reads. |
| `Examples/Chains/Payment.lean` | `transfer` under the box: a literal amount, a nonsimple amount, a storage receiver. |
| `Examples/Chains/CheckedArithmetic.lean`, `EvaluationOrder.lean` | Overflow reverts; the evaluation order of an indexed write. |

`Examples/Tactics/` — theorems `⊨ dl!{ … }` proved by `sol_symex; sol_close`
or `sol_decide`, derivations `⊢ φ` built one `apply` per taclet, and runs:

| Module | What it shows |
|---|---|
| `Examples/Tactics/Tour.lean` | The running example end to end. |
| `Examples/Tactics/StorageSteps.lean` | One storage statement form at a time, as `apply` walks. |
| `Examples/Tactics/StorageSuite.lean`, `StorageDelete.lean`, `LedgerDelete.lean` | solkey's taclet suite on storage; `delete`; a struct holding a mapping deleted. |
| `Examples/Tactics/Branch.lean`, `Revert.lean` | Two-goal splits; box and diamond on `revert`, `require`, `assert` (a check: `[ assert(false); ] true` is not valid). |
| `Examples/Tactics/Payment.lean`, `Net.lean` | `transfer` and `send` as `⊢` walks with checked sequents; the frame, the ledger's postconditions and the runs, a refused send's included. |
| `Examples/Tactics/Values.lean`, `Operators.lean`, `Checked.lean` | Operators, checked arithmetic, `−−`, bitwise, shifts, `unchecked`, `uint8` … `int248`, casts. |
| `Examples/Tactics/Calls.lean`, `CallOperands.lean`, `Callback.lean`, `TryCatch.lean`, `Contracts.lean` | Internal calls, call-valued operands, callbacks (`ProvesC`), `try`/`catch`, calls by contract (`useContract`). |
| `Examples/Tactics/Constructors.lean` | A deployment: `constructor(args);` with initializers, `Contract.deploy`, `#deploy`, and solkey's `{storage := mtSt ‖ …}` start closed by `sol_close_mt`; the obligations `problem!{constructor}` and `spec!{constructor}` (solkey's `Counter.sol`, `\old(net(a))` of `oldNet := mtSt`), the refusals, the initializer/modifier order, and what `sol_close_mt` leaves open. |
| `Examples/Tactics/Memory.lean`, `CrossDomain.lean`, `Theory.lean` | Memory, storage↔memory copies, the theory's rewriting. |
| `Examples/Tactics/SelectOnSaveConsr.lean` | Reading a write back through a `consr` path, by hand and in solkey's order. |
| `Examples/Tactics/Dangling.lean` | Writes and pushes through a stale alias (one a `pop` left dangling), made live by a `push()`, past a `delete` and a copy, by `sol_prove?`; rounds of them refused past `elimSize` in milliseconds. |
| `Examples/Tactics/ApplySteps.lean`, `UpdateRules.lean`, `Decide.lean`, `TermTaclets.lean` | The proof style, update simplification, `sol_decide`, term taclets. |
| `Examples/Tactics/Specs.lean` | Clauses as obligations (`spec!{f}`, `sol_spec`) beyond the benchmarks. |
| `Examples/Tactics/Loops.lean` | `while`, `for`, `do … while`, `break`, `continue`, `return` in a loop: the lowering's shapes pinned, `#run` of loops, a concrete loop decided (`Prog.run_loop_of_iterN`); loops proved by unwinding (`whileUnwind`, `loopExit`), solkey's two solc loop ports among them; by an invariant (`whileInvariantBox`, `whileInvariantDiamond`): a counting loop, a sum with a closed form, a loop with `break`, a walk and its proof tree. |
| `Examples/Tactics/LoopsImport.lean` | Loops from solc's AST (`tests/solc/Loops.sol`): the `/// @custom:key` clauses `scripts/solc-ast.mjs` reads from the source by the loop's `src` offset, printed above the loop by the front end (a clause over several `///` lines joined, as solkey's `KeyNatspec`); a `return` inside a loop lowered on import; five of its seven obligations proved, the two not proved named with why. |
| `Examples/Tactics/CoreSymex.lean` | `Core.symex` on three programs, checked by the kernel (`Eq.refl`) and against today's `symex` on the erasure. |
| `Examples/Tactics/CoreStep.lean` | The arms of `Core.Stmt.step` against today's, by rule family (storage, memory structs and arrays, arrays of mapping-holding structs, operators, payments, loops, calls, `try`): each program's `Core.symex` erases to today's `symex` (covers dropped) and is kernel-checked (`Eq.refl`). |
| `Examples/Tactics/CoreRules.lean` | `#rule_of` pinned: the scoped rule a statement fires (an update, a hole's unfolding, a write, a branch, `revert`, a block, a loop's unwinding and exit). |
| `Examples/Tactics/CorePrint.lean` | The scoped taclets printed as their rule lines, a block's `}`, and the strategy's formulas printed from their `Expr` as `Core.Fml.show` prints them (calls, `try`, `send`, a loop invariant); the `branches`/`cases`/`inv`/`inline` premises; `Core.Proves` goals as sequents. |
| `Examples/Tactics/CoreNotation.lean` | `cdl!{}` pinned: parameters, updates' targets, branch scopes, errors; `#wp`/`#step` on scoped formulas. |
| `Examples/Tactics/CoreProofTree.lean` | The proof tree of a scoped goal pinned: `#proof_tree`, `#proof_node`, `#proof_tree_json` on `cdl!{}`. |
| `Examples/Tactics/CoreSurface.lean` | The flip switch pinned: the same text read today's and scoped; the callback taclets printed. |
| `Examples/Tactics/CoreSpec.lean` | `cspec!{f}` and `cproblem!{constructor}` pinned on a contract with snapshots and a result; each erases to today's. |
| `Examples/Tactics/CoreCallback.lean` | The typed callback reading used: the deterministic run of a program that pays is a callback run (`Prog.exec_run`), and every callback run of one that does not is its deterministic run, decided by the kernel (`ExecP.forall_iff`).; a send's three goals under `ProvesC`. |

At the root, the notation's own tests:

| Module | What it shows |
|---|---|
| `Examples/ChainNotation.lean`, `ChainRewrites.lean`, `ExampleNames.lean` | How a chain is written and checked, its rewrite links, the printed names of fresh variables. |
| `Examples/Notation.lean` | What taclets, premises and sequents print, pinned. |
| `Examples/Verify.lean`, `Tools.lean` | `#verify`, `#counterexample` and the other commands, pinned. |
| `Examples/ProofTree.lean` | The proof tree's commands, `sol_derive?`, `sol_chain?` and `sol_prove?`, pinned. |
| `Examples/Benchmark/*.lean` | solkey's benchmark contracts with their `@custom:key` clauses proved (`Counter`, `SimpleStorage`, `Mapping`, `Purchase`, `Coin`, `EtherWallet`, `ERC20`), and `Syntax`, which pins what elaborates away (units, casts, events, errors, enums, struct constructors, modifiers). |
