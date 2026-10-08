import Solidity.Calculus.Core.TSoundKit

/-!
# Soundness over the typed state, part one: the update arms

`Calculus/Core/SoundArms.lean`'s and `SoundUpdates.lean`'s update arms
read over the typed state (`Premise.TSound`, `Calculus/Core/TProvesSound.lean`).
An update is a term of `Update.lean`, read on the erasure, so each arm is
M3's equation between the update and the scoped run (`*_run`, the proof of
M3's arm, stated over any untyped state), carried to the typed run by the
bridge (`Premise.tsound_update_run`, `Calculus/Core/TSoundKit.lean`).

The bridge asks of the typed run that it does not diverge under the
diamond: an expression, a location and every write but a push neither
diverge nor are exhausted (`Val.evalT_ends` and its kin,
`Typing/StraightRun.lean`), and a push onto `2^256 - 1` elements is
exhausted (`TRun.push_nd`, decision 15), which both modalities accept.  Every
statement is on the bridge: no struct repeats a member name (decision 16).
-/

namespace Solidity.Core

open Solidity (Modality Srt Op0 Op1 Op2 Op3 NoPanic)
open Semantics (Value SVal MVal Seg Halt Res)

variable {C : Contract}


/-! ## M3's equations, over any untyped state

The proofs of M3's update arms (`Calculus/Core/SoundArms.lean`,
`SoundUpdates.lean`), stated as the equation `Premise.Sound.update` asks. -/

section Runs

variable {Γ : Ctx} (σ : State C Γ)

theorem setLocal_run {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) :
    (Upd.nil.snoc (.local i (.val v.lower))).apply σ = Stmt.run σ (.assignLocal i v) := by
  show (do pure (σ.setLocal i (← v.lower.eval σ))) = Run.assignLocal i v σ
  rw [Val.eval_lower]; rfl

theorem save_run {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    (Upd.nil.snoc (.storage (.app3 .save .storage l.lower r.lower))).apply σ =
      Stmt.run σ (.assign l r) := by
  show (do
    let st ← Op3.eval σ.glob .save (pure σ.glob) (l.lower.eval σ) (r.lower.eval σ)
    pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.assign l r σ
  simp only [Op3.eval, Loc.eval_lower, Src.eval_lower, Run.assign, bind_assoc, pure_bind]
  congr 1; funext sv; congr 1; funext q
  exact storage_glob σ _ (Solidity.State.writeStorage_with _ _ _ _)

theorem saveMem_run {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
    (Upd.nil.snoc (.storage (.app3 .save .storage l.lower
      (.app2 .copyMem .memory p.lower)))).apply σ = Stmt.run σ (.assignFromMem l p) := by
  show (do
    let st ← Op3.eval σ.glob .save (pure σ.glob) (l.lower.eval σ)
      (Op2.eval σ.glob .copyMem (pure σ.glob) (p.lower.eval σ))
    pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.assignFromMem l p σ
  simp only [Op3.eval, Op2.eval, Loc.eval_lower, MPath.eval_lower, Run.assignFromMem, bind_assoc,
    pure_bind]
  congr 1; funext mv; congr 1; funext id; congr 1; funext sv; congr 1; funext q
  exact storage_glob σ _ (Solidity.State.writeStorage_with _ _ _ _)

theorem delAt_run {T : Ty} (l : Loc C Γ T) :
    (Upd.nil.snoc (.storage (.app2 .delAt .storage l.lower))).apply σ =
      Stmt.run σ (.delete l) := by
  show (do
    let st ← Op2.eval σ.glob .delAt (pure σ.glob) (l.lower.eval σ)
    pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.delete l σ
  simp only [Op2.eval, Loc.eval_lower, Run.delete, bind_assoc, pure_bind]
  congr 1; funext q; congr 1; funext cur
  exact storage_glob σ _ (Solidity.State.saveStorage_with _ _ _ _)

theorem writeMem_run {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) :
    (Upd.nil.snoc (.memory (.app3 .write .memory l.lower r.lower))).apply σ =
      Stmt.run σ (.assignMem l r) := by
  show (do
    let μ ← Op3.eval σ.glob .write (pure σ.glob) (l.lower.eval σ) (r.lower.eval σ)
    pure (σ.withGlob { σ.glob with heap := μ.heap, nextId := μ.nextId })) = Run.assignMem l r σ
  simp only [Op3.eval, MLoc.eval_lower_addr, MSrc.eval_lower, Run.assignMem, MLoc.write_eq,
    bind_assoc, pure_bind]
  congr 1; funext mv; congr 1; funext a
  exact memory_glob σ _ (Solidity.writeAddr_with _ _ _)

theorem rebindPath_run {R : RefTy} (i : Idx Γ (.alias R)) (p : SPath C Γ (.ref R)) :
    (Upd.nil.snoc (.local i (.path p.lower))).apply σ = Stmt.run σ (.rebind i (.path p)) := by
  show (do pure (σ.setLocal i (← do pure (some (← p.lower.eval σ))))) = Run.rebind i (.path p) σ
  simp only [SPath.eval_lower, Run.rebind, ARhs.eval, bind_assoc, pure_bind]

theorem rebindMemAlias_run {R : RefTy} (i : Idx Γ (.mem R)) (p : MPath C Γ (.ref R)) :
    (Upd.nil.snoc (.local i (.mref p.lower))).apply σ = Stmt.run σ (.rebindMem i (.alias p)) := by
  show (do pure (σ.setLocal i (← do pure (some (← p.lower.eval σ))))) =
    Run.rebindMem i (.alias p) σ
  simp only [MPath.eval_lower, Run.rebindMem, MRhs.eval, bind_assoc, pure_bind]

theorem opAssign_run {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (se : Simple C Γ p) :
    (Upd.nil.snoc (l.set (l.op op se.lower))).apply σ =
      Stmt.run σ (.opAssign op hop hp l (.simple se)) := by
  obtain ⟨v, hv⟩ := Simple.eval_ok σ se
  rw [upd1_apply]
  show _ = Run.opAssign op l (.simple se) σ
  cases l with
  | «local» i =>
    simp only [OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Rhs.eval, Tm.eval, Op2.eval,
      Simple.eval_lower, hv, evalBinop_compound hop, Run.opAssign, Val.eval, OpLoc.store, opLocal,
      bind_assoc, pure_bind]
  | root r h =>
    have hv' : se.eval σ = pure v := hv
    simp only [OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, Loc.lower, Simple.eval_lower, hv', evalBinop_compound hop,
      Run.opAssign, Val.eval, OpLoc.store, opStore, bind_assoc, pure_bind, writeStorage_toSVal,
      saveStorage_glob, map_bind]
  | field b f h =>
    have hv' : se.eval σ = pure v := hv
    simp only [OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, Loc.eval_lower, Simple.eval_lower, hv', evalBinop_compound hop,
      Run.opAssign, Val.eval, OpLoc.store, opStore, bind_assoc, pure_bind, writeStorage_toSVal,
      saveStorage_glob, map_bind]
    cases Loc.resolve σ (Loc.field b f h) <;> rfl
  | index it b ie =>
    have hv' : se.eval σ = pure v := hv
    simp only [OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, Loc.eval_lower, Simple.eval_lower, hv', evalBinop_compound hop,
      Run.opAssign, Val.eval, OpLoc.store, opStore, bind_assoc, pure_bind, writeStorage_toSVal,
      saveStorage_glob, map_bind]
    cases Loc.resolve σ (Loc.index it b (.simple ie)) <;> rfl
  | mfield b f h =>
    have hv' : se.eval σ = pure v := hv
    simp only [OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, MLoc.lower, MPath.eval_lower, Simple.eval_lower, hv',
      evalBinop_compound hop, Run.opAssign, Val.eval, OpLoc.store, opMem, bind_assoc, pure_bind,
      writeAddr_glob, map_bind, Solidity.readLoc_eq, Solidity.writeLoc_eq]
    cases MPath.mval σ b with
    | error => rfl
    | ok mv => cases hr : mv.asRef <;> simp only [Res.bind_ok, hr] <;> rfl
  | mindex a b ie =>
    have hv' : se.eval σ = pure v := hv
    obtain ⟨iv, hi⟩ := Simple.eval_ok σ ie
    have hi' : ie.eval σ = pure iv := hi
    simp only [OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, MLoc.lower, MPath.eval_lower, Simple.eval_lower, hv', hi',
      evalBinop_compound hop, Run.opAssign, Val.eval, OpLoc.store, opMem, bind_assoc, pure_bind,
      writeAddr_glob, map_bind, Solidity.readLoc_eq, Solidity.writeLoc_eq]
    cases MPath.mval σ b with
    | error => rfl
    | ok mv =>
      cases hr : mv.asRef <;> cases hn : iv.asInt <;> simp only [Res.bind_ok, hr] <;> rfl

theorem incDec_run {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    (Upd.nil.snoc (l.set (l.op op.binOp .one))).apply σ = Stmt.run σ (.incDec op hp l) := by
  rw [upd1_apply]; exact incDec_write σ op l

theorem assignIncDec_run {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (hs : l.recvSimple = true) :
    ((Upd.nil.snoc (l.set (l.op op.binOp .one))).snoc
      (.local i (.val (Tm.bumped op p l.cur)))).apply σ =
      Stmt.run σ (.assignIncDec i op hp l hs) := by
  rw [upd2_apply, incDec_write]
  show _ = Run.assignIncDec i op l σ
  simp only [Run.incDec, Run.assignIncDec, bind_assoc, pure_bind]
  cases hb : l.bump σ op with
  | error => rfl
  | ok x =>
    obtain ⟨σ', v⟩ := x
    show (do pure (σ'.setLocal i (← (Tm.bumped op p l.cur).eval σ))) = _
    rw [bump_bumped σ op l hb]; rfl

end Runs

/-! ## The update arms of `SoundArms.lean`, over the typed state -/

section Arms

variable {Γ : Ctx} {m : Modality} (σ : TState C Γ)

/-- `localValueAssign`, the reads, `binopAssignment`, `unopAssignment`, the
length reads: `{v := e}` for `v = e;`. -/
theorem tsound_setLocal {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) :
    Premise.TSound m (.assignLocal i v) (.setLocal i v) σ :=
  Premise.tsound_update_run σ (setLocal_run σ.erase i v) fun _ =>
    ((Val.evalT_ends σ v).bind fun _ => TRes.Ends.ok _).1

/-- `storageRootWriteStore`, `storageFieldWriteSave`, `storageIndexWrite*Save`,
`…CopySource`: `{storage := save(storage, l, src)}`. -/
theorem tsound_save {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    Premise.TSound m (.assign l r) (.save l r) σ :=
  Premise.tsound_update_run (s := .assign l r) σ (save_run σ.erase l r) fun _ =>
    ((Src.valueT_ends σ r).bind fun _ => (Loc.resolveT_ends σ l).bind fun _ =>
      (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _).1

/-- `memoryToStorage*CopyRoot`: `{storage := save(storage, l, copyMem(memory, p))}`. -/
theorem tsound_saveMem {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
    Premise.TSound m (.assignFromMem l p) (.saveMem l p) σ :=
  Premise.tsound_update_run (s := .assignFromMem l p) σ (saveMem_run σ.erase l p) fun _ =>
    ((MPath.mvalT_ends σ p).bind fun _ => (Loc.resolveT_ends σ l).bind fun _ =>
      (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _).1

/-- `storageRootDelete`, `storageFieldDelete`, `storageIndexDelete`,
`storageIndexArrayDelete`: `{storage := delAt(storage, l)}`. -/
theorem tsound_delAt {T : Ty} (l : Loc C Γ T) : Premise.TSound m (.delete l) (.delAt l) σ :=
  Premise.tsound_update_run σ (delAt_run σ.erase l) fun _ =>
    ((Loc.resolveT_ends σ l).bind fun _ => (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _).1

/-- `memoryFieldWrite`, `memoryIndexWriteArray`, `memoryFieldWriteCopy`,
`memoryIndexWriteCopy`: `{memory := write(memory, l, src)}`. -/
theorem tsound_writeMem {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) :
    Premise.TSound m (.assignMem l r) (.writeMem l r) σ :=
  Premise.tsound_update_run σ (writeMem_run σ.erase l r) fun _ =>
    ((MSrc.mvalT_ends σ r).bind fun _ => (MLoc.addrT_ends σ l).bind fun _ =>
      (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _).1

/-- `storageLocalRootRebind`, `…BindLocalRoot`: `{lsv := p}`. -/
theorem tsound_rebindPath {R : RefTy} (i : Idx Γ (.alias R)) (p : SPath C Γ (.ref R)) :
    Premise.TSound m (.rebind i (.path p)) (.upd1 (.local i (.path p.lower))) σ :=
  Premise.tsound_update_run σ (rebindPath_run σ.erase i p) fun _ =>
    (((SPath.resolveT_ends σ p).bind fun _ => TRes.Ends.ok _).bind fun _ => TRes.Ends.ok _).1

/-- `memoryRootRebind`, `memoryFieldReadAliasRoot`, `memoryIndexReadArrayMemory`:
`{mv := p}`. -/
theorem tsound_rebindMemAlias {R : RefTy} (i : Idx Γ (.mem R)) (p : MPath C Γ (.ref R)) :
    Premise.TSound m (.rebindMem i (.alias p)) (.upd1 (.local i (.mref p.lower))) σ :=
  Premise.tsound_update_run σ (rebindMemAlias_run σ.erase i p) fun _ =>
    ((MRhs.evalT_ends σ (.alias p)).bind fun _ => TRes.Ends.ok _).1

/-- `localOpAssign`, `storage*OpAssign`, `memory*OpAssign`: `{l := l ⊕ se}`. -/
theorem tsound_opAssign {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (se : Simple C Γ p) :
    Premise.TSound m (.opAssign op hop hp l (.simple se)) (.upd1 (l.set (l.op op se.lower))) σ :=
  Premise.tsound_update_run σ (opAssign_run σ.erase op hop hp l se) fun _ =>
    (TRes.Ends.bind (TRes.Ends.ok _) fun _ => OpLoc.storeT_ends σ op l _).1

/-- `localIncrement`, `storage*Increment`, `memory*Increment`: `{l := l ± 1}`. -/
theorem tsound_incDec {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    Premise.TSound m (.incDec op hp l) (.upd1 (l.set (l.op op.binOp .one))) σ :=
  Premise.tsound_update_run σ (incDec_run σ.erase op hp l) fun _ =>
    ((OpLoc.bumpT_ends σ op l).bind fun _ => TRes.Ends.ok _).1

/-- `localAssignIncrement`, `…IncrementAssignment`:
`{l := l ± 1 ‖ v := bumped(l)}`. -/
theorem tsound_assignIncDec {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (hs : l.recvSimple = true) :
    Premise.TSound m (.assignIncDec i op hp l hs) (.update ((Upd.nil.snoc
      (l.set (l.op op.binOp .one))).snoc (.local i (.val (Tm.bumped op p l.cur))))) σ :=
  Premise.tsound_update_run σ (assignIncDec_run σ.erase i op hp l hs) fun _ =>
    ((OpLoc.bumpT_ends σ op l).bind fun _ => TRes.Ends.ok _).1

end Arms

/-! ## The update arms of `SoundUpdates.lean` and `Step.lean`: M3's equations -/

section Runs2

variable {Γ : Ctx} (σ : State C Γ)

theorem pushSlot_run {E : Ty} (b : SPath C Γ (.array E)) (hd : (none.isSome || E.defaultOkS) = true) :
    (Upd.nil.snoc (.storage (.app2 (.pushSlot E) .storage b.lower))).apply σ =
      Stmt.run σ (.push b none hd) := by
  rw [upd1_apply]
  show (do
    let st ← Op2.eval σ.glob (.pushSlot E) (pure σ.glob) (b.lower.eval σ)
    pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.push b none σ
  simp only [Op2.eval, SPath.eval_lower, Run.push, bind_assoc, pure_bind]
  congr 1; funext q
  exact storage_glob σ _ (Solidity.pushAt_with _ _ _ _ _)

theorem extend_run {E : Ty} (b : SPath C Γ (.array E)) (hd : (none.isSome || E.defaultOkS) = true) :
    (Upd.nil.snoc (.storage (.app2 (.extend E) .storage b.lower))).apply σ =
      Stmt.run σ (.push b none hd) := by
  rw [upd1_apply]
  show (do
    let st ← Op2.eval σ.glob (.extend E) (pure σ.glob) (b.lower.eval σ)
    pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.push b none σ
  simp only [Op2.eval, SPath.eval_lower, Run.push, pushPlaceAt, pushAt, Src.pushVal,
    SemanticsProperties.State.saveStorage_eq, bind_assoc, pure_bind]
  simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  cases b.resolve σ with
  | error => rfl
  | ok q =>
    simp only
    cases σ.glob.findStorage q.1 q.2 with
    | error => rfl
    | ok v =>
      cases v with
      | array elems shadow fx =>
        simp only
        cases σ.glob.storeRes q.1 q.2 _ <;> rfl
      | _ => rfl

theorem pushSome_run {E : Ty} (b : SPath C Γ (.array E)) (r : Src C Γ E)
    (hd : ((some r).isSome || E.defaultOkS) = true) :
    (Upd.nil.snoc (.storage (.app3 .push .storage b.lower r.lower))).apply σ =
      Stmt.run σ (.push b (some r) hd) := by
  rw [upd1_apply]
  show (do
    let st ← Op3.eval σ.glob .push (pure σ.glob) (b.lower.eval σ) (r.lower.eval σ)
    pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.push b (some r) σ
  simp only [Op3.eval, SPath.eval_lower, Src.eval_lower, Run.push, bind_assoc, pure_bind]
  congr 1; funext q
  rw [show Src.pushVal σ (some r) = fun _ => (do pure (← r.value σ).strip) from rfl,
    Solidity.pushAt_const σ.glob E .uint]
  exact storage_glob σ _ (Solidity.pushAt_with _ _ _ _ _)

theorem pop_run {E : Ty} (b : SPath C Γ (.array E)) :
    (Upd.nil.snoc (.storage (.app2 (if E.isMapping then .shrink else .pop)
      .storage b.lower))).apply σ = Stmt.run σ (.pop b) := by
  rw [upd1_apply]
  cases hE : E.isMapping with
  | false =>
    show (do
      let st ← Op2.eval σ.glob .pop (pure σ.glob) (b.lower.eval σ)
      pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.pop b σ
    simp only [Op2.eval, SPath.eval_lower, Run.pop, hE, bind_assoc, pure_bind]
    congr 1; funext q
    exact storage_glob σ _ (Solidity.popAt_with _ _ _ _)
  | true =>
    show (do
      let st ← Op2.eval σ.glob .shrink (pure σ.glob) (b.lower.eval σ)
      pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.pop b σ
    simp only [Op2.eval, SPath.eval_lower, Run.pop, hE, bind_assoc, pure_bind]
    congr 1; funext q
    exact storage_glob σ _ (Solidity.popAt_with _ _ _ _)

theorem rebindPush_run {R : RefTy} (i : Idx Γ (.alias R)) (b : SPath C Γ (.array (.ref R)))
    (hd : (Ty.ref R).defaultOkS = true) :
    ((Upd.nil.snoc (.storage (.app2 (.extend (.ref R)) .storage b.lower))).snoc
      (.local i (.path (.app1 .next rfl b.lower)))).apply σ = Stmt.run σ (.rebind i (.push b hd)) := by
  rw [upd2_apply]
  show _ = Run.rebind i (.push b hd) σ
  simp only [UpdElem.write, Rhs.eval, Tm.eval, Op2.eval, Op1.eval, Op0.eval, SPath.eval_lower,
    Run.rebind, ARhs.eval, pushPlaceAt, SemanticsProperties.State.saveStorage_eq, bind_assoc,
    pure_bind]
  simp only [bind, Except.bind, pure, Except.pure]
  cases b.resolve σ with
  | error => rfl
  | ok q =>
    simp only
    cases σ.glob.findStorage q.1 q.2 with
    | error => rfl
    | ok v =>
      cases v with
      | array elems shadow fx =>
        simp only
        cases σ.glob.storeRes q.1 q.2 _ <;> rfl
      | _ => rfl

theorem transferBox_run (sadr se : Simple C Γ .uint) :
    (Upd.nil.snoc (.payTo sadr se)).apply σ = Stmt.run σ (.transfer (.simple sadr) (.simple se)) := by
  rw [upd1_apply]
  obtain ⟨a, ha⟩ := Simple.eval_ok σ sadr
  obtain ⟨v, hv⟩ := Simple.eval_ok σ se
  show _ = Run.transfer (.simple sadr) (.simple se) σ
  simp only [UpdElem.write, Simple.eval_lower, ha, hv, Run.transfer, Val.eval, transferAt,
    Semantics.State.pay, Res.bind_ok]
  cases a.asInt with
  | error => rfl
  | ok n =>
    cases v.asInt with
    | error => rfl
    | ok k =>
      simp only [Res.bind_ok]
      by_cases hk : k < 0 <;> simp only [hk, ↓reduceIte] <;> rfl

theorem send_run (pv : Idx Γ (.val .bool)) (sadr se : Simple C Γ .uint) :
    ∃ U ∈ [(Upd.nil.snoc (.payTo sadr se)).snoc (.local pv (.val (Tm.lit (.bool true)))),
        Upd.nil.snoc (.local pv (.val (Tm.lit (.bool false))))],
      Res.Sim (U.apply σ) (Stmt.run σ (.send pv (.simple sadr) (.simple se))) := by
  obtain ⟨a, ha⟩ := Simple.eval_ok σ sadr
  obtain ⟨v, hv⟩ := Simple.eval_ok σ se
  have e₁ : ((Upd.nil.snoc (.payTo sadr se)).snoc
      (.local pv (.val (Tm.lit (.bool true))))).apply σ = (do
        let addr ← a.asInt
        let amt ← v.asInt
        if amt < 0 then .error .revert
        else pure ((σ.withGlob (σ.glob.pay addr amt)).setLocal pv (.bool true))) := by
    rw [upd2_apply]
    simp only [UpdElem.write, Rhs.eval, Tm.eval, Op0.eval, Simple.eval_lower, ha, hv, Res.bind_ok,
      bind_assoc]
    cases a.asInt with
    | error => rfl
    | ok n =>
      cases v.asInt with
      | error => rfl
      | ok k => by_cases hk : k < 0 <;> simp only [Res.bind_ok, hk, ↓reduceIte] <;> rfl
  have e₂ : (Upd.nil.snoc (.local pv (.val (Tm.lit (C := C) (Γ := Γ) (.bool false))))).apply σ =
      .ok (σ.setLocal pv (.bool false)) := rfl
  have hr : Stmt.run σ (.send pv (.simple sadr) (.simple se)) = (do
      let addr ← a.asInt
      let amt ← v.asInt
      sendAt σ pv addr amt) := by
    show Run.send pv _ _ σ = _
    simp only [Run.send, Val.eval, ha, hv, Res.bind_ok]
  rw [hr]
  cases ha' : a.asInt with
  | error e => exact ⟨_, List.mem_cons_self .., by rw [e₁, ha']; exact Res.Sim.refl _⟩
  | ok n =>
    cases hv' : v.asInt with
    | error e => exact ⟨_, List.mem_cons_self .., by rw [e₁, ha', hv']; exact Res.Sim.refl _⟩
    | ok k =>
      rw [ha', hv'] at e₁
      simp only [Res.bind_ok, sendAt] at e₁ ⊢
      by_cases hk : k < 0
      · exact ⟨_, List.mem_cons_self .., by rw [e₁]; simp only [hk, ↓reduceIte]; exact Res.Sim.refl _⟩
      · simp only [hk, ↓reduceIte] at e₁ ⊢
        cases hl : Semantics.lookupBy (sendKey n k) σ.tx.ext with
        | none => exact ⟨_, List.mem_cons_self .., by rw [e₁]; exact Res.Sim.refl _⟩
        | some r =>
          cases r with
          | ok => exact ⟨_, List.mem_cons_self .., by rw [e₁]; exact Res.Sim.refl _⟩
          | _ =>
            exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by rw [e₂]; exact Res.Sim.refl _⟩

theorem declMemFresh_run (R : RefTy) (x : Var) (hd : (none.isSome || (Ty.ref R).defaultOkS) = true)
    (hm : (Ty.ref R).mapFree = true) :
    ((Upd.nil.decl x (.mref (.app1 (.alloc R) rfl .memory))).snoc
      (.memory (.app1 (.addM R) rfl .memory))).apply σ = Stmt.run σ (.declMem R x none hd hm) := by
  show (do
    let τ ← (Upd.nil.decl x (.mref (.app1 (.alloc R) rfl .memory))).apply σ
    UpdElem.write σ (.memory (.app1 (.addM R) rfl .memory)) τ) = Run.declMem R none σ
  simp only [Upd.apply, UpdElem.write, Rhs.eval, Tm.eval, Op1.eval, Op0.eval, Run.declMem,
    Solidity.allocDefault_eq, bind_assoc, pure_bind]
  simp only [bind, Except.bind, pure, Except.pure]
  cases Solidity.allocHN σ.glob R <;> rfl

theorem deleteMemVar_run {R : RefTy} (i : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    (hd : (Ty.ref R).defaultOkS = true) :
    ((Upd.nil.snoc (.local i (.mref (.app1 (.alloc R) rfl .memory)))).snoc
      (.memory (.app1 (.addM R) rfl .memory))).apply σ = Stmt.run σ (.deleteMem (.var i hm) hd) := by
  rw [upd2_apply]
  show _ = Run.deleteMem (.var i hm) σ
  simp only [UpdElem.write, Rhs.eval, Tm.eval, Op1.eval, Op0.eval, Run.deleteMem,
    Solidity.allocDefault_eq, bind_assoc, pure_bind]
  simp only [bind, Except.bind, pure, Except.pure]
  cases Solidity.allocHN σ.glob R <;> rfl

theorem allocCopy_run {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) (v : Tm C Γ .sv)
    (hr : r.eval σ = (do
      let (τ, mv) ← Semantics.copyStToM σ.glob (← v.eval σ)
      pure (σ.withGlob τ, ← mv.asRef))) :
    ((Upd.nil.snoc (.local i (.mref (.app2 .copy .memory v)))).snoc
      (.memory (.app2 .copySt .memory v))).apply σ = Stmt.run σ (.rebindMem i r) := by
  rw [upd2_apply]
  show _ = Run.rebindMem i r σ
  simp only [Run.rebindMem, hr, UpdElem.write, Rhs.eval, Tm.eval, Op2.eval, Op0.eval,
    Solidity.copyStToM_eq, bind_assoc, pure_bind]
  simp only [bind, Except.bind, pure, Except.pure]
  cases v.eval σ with
  | error => rfl
  | ok sv =>
    simp only
    cases Solidity.copyHN σ.glob sv with
    | error => rfl
    | ok q =>
      simp only
      cases q.2.2.asRef <;> rfl

theorem clearMem_run {T : Ty} (l : MLoc C Γ T) (hd : T.defaultOkS = true) :
    ∃ U, Premise.clearMem l.lower T = .update U ∧
      Res.Sim (U.apply σ) (Stmt.run σ (.deleteMem (.loc l) hd)) := by
  cases T with
  | prim p =>
    refine ⟨_, rfl, Res.Sim.of_eq ?_⟩
    rw [upd1_apply]
    show _ = Run.deleteMem (.loc l) σ
    simp only [UpdElem.write, Tm.eval, Op3.eval, Op1.eval, Op0.eval, MLoc.eval_lower_addr,
      Run.deleteMem, memClear, bind_assoc, pure_bind, writeAddr_glob]
  | ref R =>
    refine ⟨_, rfl, ?_⟩
    rw [upd1_apply]
    show Res.Sim _ (Run.deleteMem (.loc l) σ)
    simp only [UpdElem.write, Tm.eval, Op3.eval, Op1.eval, Op0.eval, MLoc.eval_lower_addr,
      Run.deleteMem, memClear, Solidity.allocDefault_eq, bind_assoc, pure_bind]
    simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
    have ha : NoPanic (l.addr σ) := by
      have h := Tm.eval_noPanic σ l.lower
      rw [MLoc.eval_lower_addr] at h
      exact h
    have hal : NoPanic (Solidity.allocHN σ.glob R) := Solidity.allocHN_noPanic σ.glob R
    revert ha hal
    cases l.addr σ with
    | error e =>
      cases Solidity.allocHN σ.glob R with
      | error e' => exact fun ha hal => ⟨fun h => absurd (congrArg Except.error h) hal,
          fun h => absurd (congrArg Except.error h) ha⟩
      | ok q => intro _ _; exact Res.Sim.refl _
    | ok a =>
      cases Solidity.allocHN σ.glob R with
      | error e' => intro _ _; exact Res.Sim.refl _
      | ok q =>
        intro _ _
        simp only
        cases hw : writeAddr _ _ a with
        | error => exact Res.Sim.refl _
        | ok μ =>
          simp only [writeAddr_ok_with hw]
          exact Res.Sim.refl _

end Runs2

/-! ## The update arms of `SoundUpdates.lean` and `Step.lean`, over the typed state -/

section Arms2

variable {Γ : Ctx} {m : Modality} (σ : TState C Γ)

/-- `storagePushLengthSave`: `{storage := pushSlot(storage, b)}`. -/
theorem tsound_pushSlot {E : Ty} (b : SPath C Γ (.array E))
    (hd : (none.isSome || E.defaultOkS) = true) :
    Premise.TSound m (.push b none hd) (.upd1 (.storage (.app2 (.pushSlot E) .storage b.lower))) σ :=
  Premise.tsound_update_run σ (pushSlot_run σ.erase b hd) fun _ => TRun.push_nd σ b none

/-- `storagePushLengthSaveReferenceElement`: `{storage := extend(storage, b)}`. -/
theorem tsound_extend {E : Ty} (b : SPath C Γ (.array E))
    (hd : (none.isSome || E.defaultOkS) = true) :
    Premise.TSound m (.push b none hd) (.upd1 (.storage (.app2 (.extend E) .storage b.lower))) σ :=
  Premise.tsound_update_run σ (extend_run σ.erase b hd) fun _ => TRun.push_nd σ b none

/-- `storagePushValueSave`, `storagePushValueCopySource`:
`{storage := push(storage, b, src)}`. -/
theorem tsound_pushSome {E : Ty} (b : SPath C Γ (.array E)) (r : Src C Γ E)
    (hd : ((some r).isSome || E.defaultOkS) = true) :
    Premise.TSound m (.push b (some r) hd)
      (.upd1 (.storage (.app3 .push .storage b.lower r.lower))) σ :=
  Premise.tsound_update_run σ (pushSome_run σ.erase b r hd) fun _ => TRun.push_nd σ b (some r)

/-- `storagePopSave`, `storagePopSaveMappingElement`. -/
theorem tsound_pop {E : Ty} (b : SPath C Γ (.array E)) :
    Premise.TSound m (.pop b) (.upd1 (.storage (.app2 (if E.isMapping then .shrink else .pop)
      .storage b.lower))) σ :=
  Premise.tsound_update_run σ (pop_run σ.erase b) fun _ =>
    ((SPath.resolveT_ends σ b).bind fun _ => (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _).1

/-- `storageLocalRootPushBind`, `storageLocalRootPushBindMappingElement`:
`{storage := extend(storage, b) ‖ lsv := next(b)}`. -/
theorem tsound_rebindPush {R : RefTy} (i : Idx Γ (.alias R)) (b : SPath C Γ (.array (.ref R)))
    (hd : (Ty.ref R).defaultOkS = true) :
    Premise.TSound m (.rebind i (.push b hd)) (.update ((Upd.nil.snoc
      (.storage (.app2 (.extend (.ref R)) .storage b.lower))).snoc
      (.local i (.path (.app1 .next rfl b.lower))))) σ :=
  Premise.tsound_update_run σ (rebindPush_run σ.erase i b hd) fun _ =>
    TRes.NoDiv.bind (ARhs.evalT_nd σ (.push b hd)) fun _ => TRes.NoDiv.ok _

/-- `transferNoCallbackBox`: `{net := …}`. -/
theorem tsound_transferBox (sadr se : Simple C Γ .uint) :
    Premise.TSound m (.transfer (.simple sadr) (.simple se)) (.upd1 (.payTo sadr se)) σ :=
  Premise.tsound_update_run σ (transferBox_run σ.erase sadr se) fun _ => TRes.NoDiv.ok _

/-- `transferDiamond` (Lean): the goal fails. -/
theorem tsound_done_false {Γ' : Ctx} (s : Stmt C Γ Γ') : Premise.TSound m s (.done false) σ :=
  Premise.tsound_done σ false fun h => nomatch h

/-- `sendNoCallbackBox`, `sendNoCallbackDiamond`: the payment with `pv` true,
or `pv` false. -/
theorem tsound_send (pv : Idx Γ (.val .bool)) (sadr se : Simple C Γ .uint) (fs : List (Fml C Γ)) :
    Premise.TSound m (.send pv (.simple sadr) (.simple se)) (.cases fs
      [(Upd.nil.snoc (.payTo sadr se)).snoc (.local pv (.val (Tm.lit (.bool true)))),
        Upd.nil.snoc (.local pv (.val (Tm.lit (.bool false))))]) σ :=
  Premise.tsound_cases_run σ (fun _ => send_run σ.erase pv sadr se) fun _ => TRes.NoDiv.ok _

/-- `memoryReferenceDeclFreshAlloc`. -/
theorem tsound_declMemFresh (R : RefTy) (x : Var)
    (hd : (none.isSome || (Ty.ref R).defaultOkS) = true) (hm : (Ty.ref R).mapFree = true) :
    Premise.TSound m (.declMem R x none hd hm) (.update ((Upd.nil.decl x
      (.mref (.app1 (.alloc R) rfl .memory))).snoc (.memory (.app1 (.addM R) rfl .memory)))) σ :=
  Premise.tsound_update_run σ (declMemFresh_run σ.erase R x hd hm) fun _ => TRes.NoDiv.ok _

/-- `memoryRootDeleteFreshRebind`. -/
theorem tsound_deleteMemVar {R : RefTy} (i : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    (hd : (Ty.ref R).defaultOkS = true) :
    Premise.TSound m (.deleteMem (.var i hm) hd) (.update ((Upd.nil.snoc
      (.local i (.mref (.app1 (.alloc R) rfl .memory)))).snoc
      (.memory (.app1 (.addM R) rfl .memory)))) σ :=
  Premise.tsound_update_run σ (deleteMemVar_run σ.erase i hm hd) fun _ => TRes.NoDiv.ok _

/-- `memoryStorageCopy`, `memoryArrayFreshAlloc`, given M3's reading of the
right-hand side on the erasure. -/
theorem tsound_allocCopy {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) (v : Tm C Γ .sv)
    (hr : r.eval σ.erase = (do
      let (τ, mv) ← Semantics.copyStToM σ.erase.glob (← v.eval σ.erase)
      pure (σ.erase.withGlob τ, ← mv.asRef))) :
    Premise.TSound m (.rebindMem i r) (.allocCopy i v) σ :=
  Premise.tsound_update_run σ (allocCopy_run σ.erase i r v hr) fun _ =>
    ((MRhs.evalT_ends σ r).bind fun _ => TRes.Ends.ok _).1

theorem clearT_ends : {T : Ty} → (a : MAddr σ.H T) → (hm : T.mapFree = true) →
    (TRun.clearT σ a hm).Ends
  | .prim _, _, _ => (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _
  | .ref R, a, hm => by
    simp only [TRun.clearT]
    split <;> exact ⟨(fun h => nomatch h), fun h => nomatch h⟩

/-- `memoryFieldDelete*`, `memoryIndexDelete*`: a slot reset to its default,
or written a fresh default object. -/
theorem tsound_clearMem {T : Ty} (l : MLoc C Γ T) (hd : T.defaultOkS = true) :
    Premise.TSound m (.deleteMem (.loc l) hd) (.clearMem l.lower T) σ := by
  obtain ⟨U, hU, hs⟩ := clearMem_run σ.erase l hd
  rw [hU]
  exact Premise.tsound_updateSim_run σ hs fun _ =>
    ((MLoc.addrT_ends σ l).bind fun a => clearT_ends σ a _).1

/-- `valueDeclSkip`: `{v := defVal(T)}`. -/
theorem tsound_valueDeclSkip (p : PrimTy) (x : Var) :
    Premise.TSound m (.declLocal p x none)
      (.update (Upd.nil.decl x (.val (p := p) (.app0 (.lit p.default))))) σ :=
  Premise.tsound_update_run (s := .declLocal p x none) σ rfl fun _ => TRes.NoDiv.ok _

/-- `storageLocalDeclSkip`: `{lsv := unset}`. -/
theorem tsound_storageLocalDeclSkip (R : RefTy) (x : Var) :
    Premise.TSound m (.declStorage R x none) (.update (Upd.nil.decl (t := .alias R) x .unset)) σ :=
  Premise.tsound_update_run (s := .declStorage R x none) σ rfl fun _ => TRes.NoDiv.ok _

/-- `revertBox`, `revertDiamond`. -/
theorem tsound_revert :
    Premise.TSound m (.revert : Stmt C Γ Γ) (.done (m == .box)) σ :=
  Premise.tsound_done σ _ fun h =>
    ⟨by cases m <;> first | rfl | exact absurd h (by decide), .revert, rfl, by decide⟩

end Arms2

end Solidity.Core
