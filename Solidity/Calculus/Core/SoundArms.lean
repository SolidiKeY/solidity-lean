import Solidity.Calculus.Core.SoundKit
import Solidity.Theory.StateWrites

/-!
# Soundness of the update arms

The rules of `Calculus/Core/Arms.lean` and `Step.lean` whose premise is an
update (`Premise.Sound`, `Calculus/Core/ProvesSound.lean`).  An update is a
term of `Update.lean`, read on the erasure, so each arm is an equation
between the update and what the statement's typed step erases to (`*_run`,
stated over any erased state against `StepAgrees.erased` of the step's
`TRun.*_erase`, `Semantics/Core/TypedStepErase.lean`), which the typed run
agrees with (`Premise.sound_update_erased`, `Calculus/Core/SoundKit.lean`).
Before them, the global operations' frame lemmas
(`Theory/StateWrites.lean`'s, on `σ.glob`).

The arms ask of the typed run that it does not diverge under the diamond:
an expression, a location and every write but a push neither diverge nor
are exhausted (`Val.evalT_ends` and its kin,
`Semantics/Core/TypedEnds.lean`), and a push onto `2^256 - 1` elements is
exhausted (`TRun.push_nd`, decision 15), which both modalities accept.  Every
statement is on it: no struct repeats a member name (decision 16).
-/

namespace Solidity.Core
open Solidity (Modality Srt Op0 Op1 Op2 Op3 NoPanic)
open Semantics (Value SVal MVal Seg Halt Res)
open Solidity (readAddr)

variable {C : Contract}


/-! ## Updates: the update ends as the statement does

Step 3 of every family.  The update reads its right-hand sides in the state
it is applied in, the statement left to right; both reach the same writes
through the same reads, and a write of the storage (the heap) changes
nothing else (`Theory/StateWrites.lean`'s `*_with`). -/

section Updates

variable {Γ : Ctx} {m : Modality} (σ : State C Γ)

theorem Src.eval_lower {T : Ty} (r : Src C Γ T) : r.lower.eval σ = r.value σ := by
  cases r with
  | val v => simp only [Src.lower, Tm.eval, Op1.eval, Src.value, Val.eval_lower]
  | copy p hm => simp only [Src.lower, Tm.eval, Op2.eval, Op0.eval, Src.value, SPath.eval_lower,
      pure_bind]

theorem MSrc.eval_lower {T : Ty} (r : MSrc C Γ T) : r.lower.eval σ = r.mval σ := by
  cases r with
  | val v => simp only [MSrc.lower, Tm.eval, Op1.eval, MSrc.mval, Val.eval_lower]
  | ref p => simp only [MSrc.lower, Tm.eval, Op1.eval, MSrc.mval, MPath.eval_lower, bind_assoc]

theorem MLoc.eval_lower_addr {T : Ty} (l : MLoc C Γ T) : l.lower.eval σ = l.addr σ := by
  cases l with
  | field b f h => simp only [MLoc.lower, Tm.eval, Op1.eval, MLoc.addr, MPath.eval_lower, bind_assoc]
  | index a b i => simp only [MLoc.lower, Tm.eval, Op2.eval, MLoc.addr, MPath.eval_lower,
      Val.eval_lower, bind_assoc]

/-- A storage write through the term: the global part with the storage it
leaves. -/
theorem storage_glob (x : Res Semantics.State)
    (hx : (x >>= fun τ => pure { σ.glob with storage := τ.storage }) = x) :
    (x >>= fun st => pure (σ.withGlob { σ.glob with storage := st.storage })) = σ.withGlob <$> x := by
  conv => rhs; rw [← hx]
  cases x <;> rfl

/-- A heap write through the term. -/
theorem memory_glob (x : Res Semantics.State)
    (hx : (x >>= fun μ => pure { σ.glob with heap := μ.heap, nextId := μ.nextId }) = x) :
    (x >>= fun μ => pure (σ.withGlob { σ.glob with heap := μ.heap, nextId := μ.nextId })) =
      σ.withGlob <$> x := by
  conv => rhs; rw [← hx]
  cases x <;> rfl

theorem upd1_apply (e : UpdElem C Γ Γ) : (Upd.nil.snoc e).apply σ = e.write σ σ := rfl

theorem Simple.eval_ok {p : PrimTy} (s : Simple C Γ p) : ∃ v, s.eval σ = .ok v := by
  cases s <;> exact ⟨_, rfl⟩

theorem Res.bind_ok {α β : Type} (a : α) (f : α → Res β) : ((Except.ok a : Res α) >>= f) = f a :=
  rfl

theorem writeStorage_toSVal (s : Semantics.State) (r : Name) (segs : List Seg) (v : Value) :
    s.writeStorage r segs v.toSVal = s.saveStorage r segs v.toSVal := by
  cases v <;> rfl

/-- A storage save through the term, as the statement's write. -/
theorem saveStorage_glob (r : Name) (segs : List Seg) (v : Semantics.SVal) :
    (σ.glob.saveStorage r segs v >>= fun d =>
      pure (σ.withGlob { σ.glob with storage := d.storage })) =
      σ.withGlob <$> σ.glob.saveStorage r segs v :=
  storage_glob σ _ (Solidity.State.saveStorage_with _ _ _ _)

/-- A heap write through the term, as the statement's write. -/
theorem writeAddr_glob (mv : Semantics.MVal) (a : Semantics.Addr) :
    (writeAddr σ.glob mv a >>= fun μ =>
      pure (σ.withGlob { σ.glob with heap := μ.heap, nextId := μ.nextId })) =
      σ.withGlob <$> writeAddr σ.glob mv a :=
  memory_glob σ _ (Solidity.writeAddr_with _ _ _)

/-- A global step's state and value, with the locals (`Semantics/Core.lean`'s
private `withGlob₂`). -/
def glob₂ (x : Semantics.State × Value) : State C Γ × Value := (σ.withGlob x.1, x.2)

@[simp] theorem glob₂_fst (x : Semantics.State × Value) : (glob₂ σ x).1 = σ.withGlob x.1 := rfl
@[simp] theorem glob₂_snd (x : Semantics.State × Value) : (glob₂ σ x).2 = x.2 := rfl

theorem bind_withGlob (x : Res Semantics.State) :
    (x >>= fun τ => pure (σ.withGlob τ)) = σ.withGlob <$> x := by
  cases x <;> rfl

theorem OpLoc.bump_root {p : PrimTy} (op : IncDec) (r : Name) (h : C.rootType r = some (.prim p)) :
    (OpLoc.root (Γ := Γ) r h).bump σ op = glob₂ σ <$> bumpStore σ.glob op p r [] := rfl

theorem OpLoc.bump_field {p : PrimTy} (op : IncDec) {s : Name} (b : SPath C Γ (.struct s)) (f : Name)
    (h : C.fieldType s f = some (.prim p)) :
    (OpLoc.field b f h).bump σ op = (do
      let (rt, segs) ← (Loc.field b f h).resolve σ
      glob₂ σ <$> bumpStore σ.glob op p rt segs) := rfl

theorem OpLoc.bump_index {p : PrimTy} (op : IncDec) {R : RefTy} {k : PrimTy}
    (it : IndexTy R k (.prim p)) (b : SPath C Γ (.ref R)) (i : Simple C Γ k) :
    (OpLoc.index it b i).bump σ op = (do
      let (rt, segs) ← (Loc.index it b (.simple i)).resolve σ
      glob₂ σ <$> bumpStore σ.glob op p rt segs) := rfl

theorem OpLoc.bump_mfield {p : PrimTy} (op : IncDec) {s : Name} (b : MPath C Γ (.struct s)) (f : Name)
    (h : C.fieldType s f = some (.prim p)) :
    (OpLoc.mfield b f h).bump σ op = (do
      let id ← (← b.mval σ).asRef
      glob₂ σ <$> bumpMem σ.glob op p (.memoryField id f)) := rfl

theorem OpLoc.bump_mindex {p : PrimTy} (op : IncDec) {R : RefTy} (a : ArrTy R (.prim p))
    (b : MPath C Γ (.ref R)) (i : Simple C Γ .uint) :
    (OpLoc.mindex a b i).bump σ op = (do
      let id ← (← b.mval σ).asRef
      let iv ← (← i.eval σ).asInt
      glob₂ σ <$> bumpMem σ.glob op p (.memoryIndex id iv)) := rfl

/-- `localIncrement`, `storageRootIncrement`, `storageFieldIncrement`,
`storageIndexIncrement`, `memoryFieldIncrement`, `memoryIndexArrayIncrement`:
`{l := l ± 1}`. -/
theorem incDec_write {p : PrimTy} (op : IncDec) (l : OpLoc C Γ p) :
    (l.set (l.op op.binOp .one)).write σ σ = (do pure (← l.bump σ op).1) := by
  cases l with
  | «local» i =>
    simp only [Rhs.eval, OpLoc.bump, bumpLocal, OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write,
      Tm.eval, Op2.eval, Op0.eval, evalBinop_bump, Solidity.applyBinOp_bump,
      bind_assoc, pure_bind]
  | root r h =>
    simp only [Loc.lower, OpLoc.bump_root, bumpStore, writeStorage_toSVal, saveStorage_glob,
      OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, evalBinop_bump, Solidity.applyBinOp_bump,
      bind_assoc, pure_bind, map_bind, map_pure, glob₂_fst, bind_withGlob]
  | field b f h =>
    simp only [Loc.eval_lower, OpLoc.bump_field, bumpStore, writeStorage_toSVal,
      saveStorage_glob, OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, evalBinop_bump, Solidity.applyBinOp_bump,
      bind_assoc, pure_bind, map_bind, map_pure, glob₂_fst, bind_withGlob]
    cases Loc.resolve σ (Loc.field b f h) <;> rfl
  | index it b ie =>
    simp only [Loc.eval_lower, OpLoc.bump_index, bumpStore, writeStorage_toSVal,
      saveStorage_glob, OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, evalBinop_bump, Solidity.applyBinOp_bump,
      bind_assoc, pure_bind, map_bind, map_pure, glob₂_fst, bind_withGlob]
    cases Loc.resolve σ (Loc.index it b (.simple ie)) <;> rfl
  | mfield b f h =>
    simp only [MLoc.lower, MPath.eval_lower, OpLoc.bump_mfield, bumpMem, writeAddr_glob,
      Solidity.readLoc_eq, Solidity.writeLoc_eq, OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, evalBinop_bump, Solidity.applyBinOp_bump,
      bind_assoc, pure_bind, map_bind, map_pure, glob₂_fst, bind_withGlob]
    cases MPath.mval σ b with
    | error => rfl
    | ok mv => cases hr : mv.asRef <;> simp only [Res.bind_ok, hr] <;> rfl
  | mindex a b ie =>
    obtain ⟨iv, hi⟩ := Simple.eval_ok σ ie
    have hi' : ie.eval σ = pure iv := hi
    simp only [MLoc.lower, MPath.eval_lower, Simple.eval_lower, hi', OpLoc.bump_mindex, bumpMem,
      writeAddr_glob, Solidity.readLoc_eq, Solidity.writeLoc_eq, OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, evalBinop_bump, Solidity.applyBinOp_bump,
      bind_assoc, pure_bind, map_bind, map_pure, glob₂_fst, bind_withGlob]
    cases MPath.mval σ b with
    | error => rfl
    | ok mv =>
      cases hr : mv.asRef <;> cases hn : iv.asInt <;> simp only [Res.bind_ok, hr] <;> rfl

theorem writeAddr_ok_with {s x : Semantics.State} {mv : Semantics.MVal} {a : Semantics.Addr}
    (h : writeAddr s mv a = .ok x) : { s with heap := x.heap, nextId := x.nextId } = x := by
  have e := Solidity.writeAddr_with s mv a
  rw [h] at e
  exact Except.ok.inj e

theorem upd2_apply (e₁ e₂ : UpdElem C Γ Γ) :
    ((Upd.nil.snoc e₁).snoc e₂).apply σ = (do e₂.write σ (← e₁.write σ σ)) := rfl

theorem Res.bind_eq_ok {α β : Type} {x : Res α} {f : α → Res β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact ⟨fun h => (nomatch h), fun ⟨_, h, _⟩ => (nomatch h)⟩
  | ok a => exact ⟨fun h => ⟨a, rfl, h⟩, fun ⟨_, h, h'⟩ => by cases h; exact h'⟩

theorem Res.map_eq_ok {α β : Type} {x : Res α} {f : α → β} {b : β} :
    (f <$> x) = .ok b ↔ ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => exact ⟨fun h => (nomatch h), fun ⟨_, h, _⟩ => (nomatch h)⟩
  | ok a => exact ⟨fun h => ⟨a, rfl, Except.ok.inj h⟩, fun ⟨_, h, h'⟩ => by cases h; rw [← h']; rfl⟩

/-- The value `l++` gives is what the term `bumped(l)` reads in the state before. -/
theorem bump_bumped {p : PrimTy} (op : IncDec) (l : OpLoc C Γ p) {σ' : State C Γ} {v : Value}
    (hb : l.bump σ op = .ok (σ', v)) : (Tm.bumped op p l.cur).eval σ = .ok v := by
  unfold Tm.bumped
  cases l with
  | «local» j =>
    simp only [OpLoc.bump, bumpLocal, Res.bind_eq_ok] at hb
    obtain ⟨n, hn, new, hnew, he⟩ := hb
    cases Except.ok.inj he
    split <;> simp only [OpLoc.cur, Tm.eval, Op2.eval, Op0.eval, evalBinop_bump,
      Solidity.applyBinOp_bump, Res.bind_ok, pure_bind, *]
    all_goals rfl
  | root r h =>
    simp only [OpLoc.bump_root, bumpStore, Res.map_eq_ok, Res.bind_eq_ok] at hb
    obtain ⟨⟨τ, w⟩, ⟨sv, hsv, old, hold, n, hn, new, hnew, τ', hτ', he⟩, hg⟩ := hb
    cases Except.ok.inj he; cases hg
    split <;> simp only [Loc.lower, OpLoc.cur, Tm.eval, Op2.eval, Op0.eval, Val.lower, evalBinop_bump, Solidity.applyBinOp_bump, Res.bind_ok, pure_bind, bind_assoc, hsv, hold, hn, hnew] <;> rfl
  | field b f h =>
    simp only [OpLoc.bump_field, bumpStore, Res.map_eq_ok, Res.bind_eq_ok] at hb
    obtain ⟨⟨rt, segs⟩, hr, ⟨τ, w⟩, ⟨sv, hsv, old, hold, n, hn, new, hnew, τ', hτ', he⟩, hg⟩ := hb
    cases Except.ok.inj he; cases hg
    split <;> simp only [Loc.eval_lower, OpLoc.cur, Tm.eval, Op2.eval, Op0.eval, Val.lower, evalBinop_bump, Solidity.applyBinOp_bump, Res.bind_ok, pure_bind, bind_assoc, hr, hsv, hold, hn, hnew] <;> rfl
  | index it b ie =>
    simp only [OpLoc.bump_index, bumpStore, Res.map_eq_ok, Res.bind_eq_ok] at hb
    obtain ⟨⟨rt, segs⟩, hr, ⟨τ, w⟩, ⟨sv, hsv, old, hold, n, hn, new, hnew, τ', hτ', he⟩, hg⟩ := hb
    cases Except.ok.inj he; cases hg
    split <;> simp only [Loc.eval_lower, OpLoc.cur, Tm.eval, Op2.eval, Op0.eval, Val.lower, evalBinop_bump, Solidity.applyBinOp_bump, Res.bind_ok, pure_bind, bind_assoc, hr, hsv, hold, hn, hnew] <;> rfl
  | mfield b f h =>
    simp only [OpLoc.bump_mfield, bumpMem, Res.map_eq_ok, Res.bind_eq_ok] at hb
    obtain ⟨mv, hmv, id, hid, ⟨τ, w⟩, ⟨old, hold, n, hn, new, hnew, τ', hτ', he⟩, hg⟩ := hb
    cases Except.ok.inj he; cases hg
    simp only [Solidity.readLoc_eq, Res.bind_eq_ok] at hold
    obtain ⟨r, hr, hro⟩ := hold
    split <;> simp only [MLoc.lower, MPath.eval_lower, OpLoc.cur, Tm.eval, Op2.eval, Op1.eval, Op0.eval, Val.lower, evalBinop_bump, Solidity.applyBinOp_bump, Res.bind_ok, pure_bind, bind_assoc, hmv, hid, hr, hro, hn, hnew] <;> rfl
  | mindex a b ie =>
    simp only [OpLoc.bump_mindex, bumpMem, Res.map_eq_ok, Res.bind_eq_ok] at hb
    obtain ⟨mv, hmv, id, hid, iv, hiv, k, hk, ⟨τ, w⟩, ⟨old, hold, n, hn, new, hnew, τ', hτ', he⟩, hg⟩ := hb
    cases Except.ok.inj he; cases hg
    simp only [Solidity.readLoc_eq, Res.bind_eq_ok] at hold
    obtain ⟨r, hr, hro⟩ := hold
    split <;> simp only [MLoc.lower, MPath.eval_lower, Simple.eval_lower, OpLoc.cur, Tm.eval, Op2.eval, Op0.eval, Val.lower, evalBinop_bump, Solidity.applyBinOp_bump, Res.bind_ok, pure_bind, bind_assoc, hmv, hid, hiv, hk,
      hr, hro, hn, hnew] <;> rfl

end Updates

open Solidity (Modality Srt Op0 Op1 Op2 Op3 NoPanic)
open Semantics (Value SVal MVal Seg Halt Res)

/-! ## The equations, over the erased state

Each update arm's equation between its update and what the statement's
typed step erases to, over any erased state, as
`Premise.sound_update_erased` asks. -/

section Runs

variable {Γ : Ctx} (σ : State C Γ)

theorem setLocal_run {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) :
    (Upd.nil.snoc (.local i (.val v.lower))).apply σ = (TRun.assignLocal_erase i v).erased σ := by
  show (do pure (σ.setLocal i (← v.lower.eval σ))) = _
  rw [Val.eval_lower]

theorem save_run {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    (Upd.nil.snoc (.storage (.app3 .save .storage l.lower r.lower))).apply σ =
      (TRun.assign_erase l r).erased σ := by
  show (do
    let st ← Op3.eval σ.glob .save (pure σ.glob) (l.lower.eval σ) (r.lower.eval σ)
    pure (σ.withGlob { σ.glob with storage := st.storage })) = _
  simp only [Op3.eval, Loc.eval_lower, Src.eval_lower, StepAgrees.erased, bind_assoc, pure_bind]
  congr 1; funext sv; congr 1; funext q
  exact storage_glob σ _ (Solidity.State.writeStorage_with _ _ _ _)

theorem saveMem_run {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
    (Upd.nil.snoc (.storage (.app3 .save .storage l.lower
      (.app2 .copyMem .memory p.lower)))).apply σ = (TRun.assignFromMem_erase l p).erased σ := by
  show (do
    let st ← Op3.eval σ.glob .save (pure σ.glob) (l.lower.eval σ)
      (Op2.eval σ.glob .copyMem (pure σ.glob) (p.lower.eval σ))
    pure (σ.withGlob { σ.glob with storage := st.storage })) = _
  simp only [Op3.eval, Op2.eval, Loc.eval_lower, MPath.eval_lower, StepAgrees.erased, bind_assoc,
    pure_bind]
  congr 1; funext mv; congr 1; funext id; congr 1; funext sv; congr 1; funext q
  exact storage_glob σ _ (Solidity.State.writeStorage_with _ _ _ _)

theorem delAt_run {T : Ty} (l : Loc C Γ T) :
    (Upd.nil.snoc (.storage (.app2 .delAt .storage l.lower))).apply σ =
      (TRun.delete_erase l).erased σ := by
  show (do
    let st ← Op2.eval σ.glob .delAt (pure σ.glob) (l.lower.eval σ)
    pure (σ.withGlob { σ.glob with storage := st.storage })) = _
  simp only [Op2.eval, Loc.eval_lower, StepAgrees.erased, bind_assoc, pure_bind]
  congr 1; funext q; congr 1; funext cur
  exact storage_glob σ _ (Solidity.State.saveStorage_with _ _ _ _)

theorem writeMem_run {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) :
    (Upd.nil.snoc (.memory (.app3 .write .memory l.lower r.lower))).apply σ =
      (TRun.assignMem_erase l r).erased σ := by
  show (do
    let μ ← Op3.eval σ.glob .write (pure σ.glob) (l.lower.eval σ) (r.lower.eval σ)
    pure (σ.withGlob { σ.glob with heap := μ.heap, nextId := μ.nextId })) = _
  simp only [Op3.eval, MLoc.eval_lower_addr, MSrc.eval_lower, StepAgrees.erased, MLoc.write_eq,
    bind_assoc, pure_bind]
  congr 1; funext mv; congr 1; funext a
  exact memory_glob σ _ (Solidity.writeAddr_with _ _ _)

theorem rebindPath_run {R : RefTy} (i : Idx Γ (.alias R)) (p : SPath C Γ (.ref R)) :
    (Upd.nil.snoc (.local i (.path p.lower))).apply σ =
      (TRun.rebind_erase i (.path p)).erased σ := by
  show (do pure (σ.setLocal i (← do pure (some (← p.lower.eval σ))))) = _
  simp only [SPath.eval_lower, StepAgrees.erased, ARhs.eval, bind_assoc, pure_bind]

theorem rebindMemAlias_run {R : RefTy} (i : Idx Γ (.mem R)) (p : MPath C Γ (.ref R)) :
    (Upd.nil.snoc (.local i (.mref p.lower))).apply σ =
      (TRun.rebindMem_erase i (.alias p)).erased σ := by
  show (do pure (σ.setLocal i (← do pure (some (← p.lower.eval σ))))) =
    _
  simp only [MPath.eval_lower, StepAgrees.erased, MRhs.eval, bind_assoc, pure_bind]

theorem opAssign_run {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (se : Simple C Γ p) :
    (Upd.nil.snoc (l.set (l.op op se.lower))).apply σ =
      (TRun.opAssign_erase op hop hp l (.simple se)).erased σ := by
  obtain ⟨v, hv⟩ := Simple.eval_ok σ se
  rw [upd1_apply]
  show _ = _
  cases l with
  | «local» i =>
    simp only [OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Rhs.eval, Tm.eval, Op2.eval,
      Simple.eval_lower, hv, evalBinop_compound hop, StepAgrees.erased, Val.eval, OpLoc.store,
      opLocal,
      bind_assoc, pure_bind]
  | root r h =>
    have hv' : se.eval σ = pure v := hv
    simp only [OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, Loc.lower, Simple.eval_lower, hv', evalBinop_compound hop,
      StepAgrees.erased, Val.eval, OpLoc.store, opStore, bind_assoc, pure_bind, writeStorage_toSVal,
      saveStorage_glob, map_bind]
  | field b f h =>
    have hv' : se.eval σ = pure v := hv
    simp only [OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, Loc.eval_lower, Simple.eval_lower, hv', evalBinop_compound hop,
      StepAgrees.erased, Val.eval, OpLoc.store, opStore, bind_assoc, pure_bind, writeStorage_toSVal,
      saveStorage_glob, map_bind]
    cases Loc.resolve σ (Loc.field b f h) <;> rfl
  | index it b ie =>
    have hv' : se.eval σ = pure v := hv
    simp only [OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, Loc.eval_lower, Simple.eval_lower, hv', evalBinop_compound hop,
      StepAgrees.erased, Val.eval, OpLoc.store, opStore, bind_assoc, pure_bind, writeStorage_toSVal,
      saveStorage_glob, map_bind]
    cases Loc.resolve σ (Loc.index it b (.simple ie)) <;> rfl
  | mfield b f h =>
    have hv' : se.eval σ = pure v := hv
    simp only [OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, MLoc.lower, MPath.eval_lower, Simple.eval_lower, hv',
      evalBinop_compound hop, StepAgrees.erased, Val.eval, OpLoc.store, opMem, bind_assoc,
      pure_bind,
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
      evalBinop_compound hop, StepAgrees.erased, Val.eval, OpLoc.store, opMem, bind_assoc,
      pure_bind,
      writeAddr_glob, map_bind, Solidity.readLoc_eq, Solidity.writeLoc_eq]
    cases MPath.mval σ b with
    | error => rfl
    | ok mv =>
      cases hr : mv.asRef <;> cases hn : iv.asInt <;> simp only [Res.bind_ok, hr] <;> rfl

theorem incDec_run {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    (Upd.nil.snoc (l.set (l.op op.binOp .one))).apply σ = (TRun.incDec_erase op hp l).erased σ := by
  rw [upd1_apply]; exact incDec_write σ op l

theorem assignIncDec_run {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    ((Upd.nil.snoc (l.set (l.op op.binOp .one))).snoc
      (.local i (.val (Tm.bumped op p l.cur)))).apply σ =
      (TRun.assignIncDec_erase i op hp l).erased σ := by
  rw [upd2_apply, incDec_write]
  show _ = _
  simp only [StepAgrees.erased, StepAgrees.erased, bind_assoc, pure_bind]
  cases hb : l.bump σ op with
  | error => rfl
  | ok x =>
    obtain ⟨σ', v⟩ := x
    show (do pure (σ'.setLocal i (← (Tm.bumped op p l.cur).eval σ))) = _
    rw [bump_bumped σ op l hb]; rfl

end Runs

/-! ## The update arms -/

section Arms

variable {Γ : Ctx} {m : Modality} (σ : TState C Γ)

/-- `localValueAssign`, the reads, `binopAssignment`, `unopAssignment`, the
length reads: `{v := e}` for `v = e;`. -/
theorem sound_setLocal {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) :
    Premise.Runs m (.assignLocal i v) (.setLocal i v) σ :=
  Premise.sound_update_erased (TRun.assignLocal_erase i v) σ (setLocal_run σ.erase i v) fun _ =>
    ((Val.evalT_ends σ v).bind fun _ => TRes.Ends.ok _).1

/-- `storageRootWriteStore`, `storageFieldWriteSave`, `storageIndexWrite*Save`,
`…CopySource`: `{storage := save(storage, l, src)}`. -/
theorem sound_save {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    Premise.Runs m (.assign l r) (.save l r) σ :=
  Premise.sound_update_erased (s := .assign l r) (TRun.assign_erase l r)
    σ (save_run σ.erase l r) fun _ =>
    ((Src.valueT_ends σ r).bind fun _ => (Loc.resolveT_ends σ l).bind fun _ =>
      (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _).1

/-- `memoryToStorage*CopyRoot`: `{storage := save(storage, l, copyMem(memory, p))}`. -/
theorem sound_saveMem {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
    Premise.Runs m (.assignFromMem l p) (.saveMem l p) σ :=
  Premise.sound_update_erased (s := .assignFromMem l p) (TRun.assignFromMem_erase l p)
    σ (saveMem_run σ.erase l p) fun _ =>
    ((MPath.mvalT_ends σ p).bind fun _ => (Loc.resolveT_ends σ l).bind fun _ =>
      (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _).1

/-- `storageRootDelete`, `storageFieldDelete`, `storageIndexDelete`,
`storageIndexArrayDelete`: `{storage := delAt(storage, l)}`. -/
theorem sound_delAt {T : Ty} (l : Loc C Γ T) : Premise.Runs m (.delete l) (.delAt l) σ :=
  Premise.sound_update_erased (TRun.delete_erase l) σ (delAt_run σ.erase l) fun _ =>
    ((Loc.resolveT_ends σ l).bind fun _ => (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _).1

/-- `memoryFieldWrite`, `memoryIndexWriteArray`, `memoryFieldWriteCopy`,
`memoryIndexWriteCopy`: `{memory := write(memory, l, src)}`. -/
theorem sound_writeMem {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) :
    Premise.Runs m (.assignMem l r) (.writeMem l r) σ :=
  Premise.sound_update_erased (TRun.assignMem_erase l r) σ (writeMem_run σ.erase l r) fun _ =>
    ((MSrc.mvalT_ends σ r).bind fun _ => (MLoc.addrT_ends σ l).bind fun _ =>
      (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _).1

/-- `storageLocalRootRebind`, `…BindLocalRoot`: `{lsv := p}`. -/
theorem sound_rebindPath {R : RefTy} (i : Idx Γ (.alias R)) (p : SPath C Γ (.ref R)) :
    Premise.Runs m (.rebind i (.path p)) (.upd1 (.local i (.path p.lower))) σ :=
  Premise.sound_update_erased (TRun.rebind_erase i (.path p))
    σ (rebindPath_run σ.erase i p) fun _ =>
    (((SPath.resolveT_ends σ p).bind fun _ => TRes.Ends.ok _).bind fun _ => TRes.Ends.ok _).1

/-- `memoryRootRebind`, `memoryFieldReadAliasRoot`, `memoryIndexReadArrayMemory`:
`{mv := p}`. -/
theorem sound_rebindMemAlias {R : RefTy} (i : Idx Γ (.mem R)) (p : MPath C Γ (.ref R)) :
    Premise.Runs m (.rebindMem i (.alias p)) (.upd1 (.local i (.mref p.lower))) σ :=
  Premise.sound_update_erased (TRun.rebindMem_erase i (.alias p))
    σ (rebindMemAlias_run σ.erase i p) fun _ =>
    ((MRhs.evalT_ends σ (.alias p)).bind fun _ => TRes.Ends.ok _).1

/-- `localOpAssign`, `storage*OpAssign`, `memory*OpAssign`: `{l := l ⊕ se}`. -/
theorem sound_opAssign {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (se : Simple C Γ p) :
    Premise.Runs m (.opAssign op hop hp l (.simple se)) (.upd1 (l.set (l.op op se.lower))) σ :=
  Premise.sound_update_erased (TRun.opAssign_erase op hop hp l (.simple se))
    σ (opAssign_run σ.erase op hop hp l se) fun _ =>
    (TRes.Ends.bind (TRes.Ends.ok _) fun _ => OpLoc.storeT_ends σ op l _).1

/-- `localIncrement`, `storage*Increment`, `memory*Increment`: `{l := l ± 1}`. -/
theorem sound_incDec {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    Premise.Runs m (.incDec op hp l) (.upd1 (l.set (l.op op.binOp .one))) σ :=
  Premise.sound_update_erased (TRun.incDec_erase op hp l) σ (incDec_run σ.erase op hp l) fun _ =>
    ((OpLoc.bumpT_ends σ op l).bind fun _ => TRes.Ends.ok _).1

/-- `localAssignIncrement`, `…IncrementAssignment`:
`{l := l ± 1 ‖ v := bumped(l)}`. -/
theorem sound_assignIncDec {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (hs : l.recvSimple = true) :
    Premise.Runs m (.assignIncDec i op hp l hs) (.update ((Upd.nil.snoc
      (l.set (l.op op.binOp .one))).snoc (.local i (.val (Tm.bumped op p l.cur))))) σ :=
  Premise.sound_update_erased (TRun.assignIncDec_erase i op hp l)
    σ (assignIncDec_run σ.erase i op hp l) fun _ =>
    ((OpLoc.bumpT_ends σ op l).bind fun _ => TRes.Ends.ok _).1

end Arms

/-! ## The other update arms (`Step.lean`): the equations -/

section Runs2

variable {Γ : Ctx} (σ : State C Γ)

theorem pushSlot_run {E : Ty} (b : SPath C Γ (.array E)) :
    (Upd.nil.snoc (.storage (.app2 (.pushSlot E) .storage b.lower))).apply σ =
      (TRun.push_erase b none).erased σ := by
  rw [upd1_apply]
  show (do
    let st ← Op2.eval σ.glob (.pushSlot E) (pure σ.glob) (b.lower.eval σ)
    pure (σ.withGlob { σ.glob with storage := st.storage })) = _
  simp only [Op2.eval, SPath.eval_lower, StepAgrees.erased, bind_assoc, pure_bind]
  congr 1; funext q
  exact storage_glob σ _ (Solidity.pushAt_with _ _ _ _ _)

theorem extend_run {E : Ty} (b : SPath C Γ (.array E)) :
    (Upd.nil.snoc (.storage (.app2 (.extend E) .storage b.lower))).apply σ =
      (TRun.push_erase b none).erased σ := by
  rw [upd1_apply]
  show (do
    let st ← Op2.eval σ.glob (.extend E) (pure σ.glob) (b.lower.eval σ)
    pure (σ.withGlob { σ.glob with storage := st.storage })) = _
  simp only [Op2.eval, SPath.eval_lower, StepAgrees.erased, pushPlaceAt, pushAt, Src.pushVal,
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

theorem pushSome_run {E : Ty} (b : SPath C Γ (.array E)) (r : Src C Γ E) :
    (Upd.nil.snoc (.storage (.app3 .push .storage b.lower r.lower))).apply σ =
      (TRun.push_erase b (some r)).erased σ := by
  rw [upd1_apply]
  show (do
    let st ← Op3.eval σ.glob .push (pure σ.glob) (b.lower.eval σ) (r.lower.eval σ)
    pure (σ.withGlob { σ.glob with storage := st.storage })) = _
  simp only [Op3.eval, SPath.eval_lower, Src.eval_lower, StepAgrees.erased, bind_assoc, pure_bind]
  congr 1; funext q
  rw [show Src.pushVal σ (some r) = fun _ => (do pure (← r.value σ).strip) from rfl,
    Solidity.pushAt_const σ.glob E .uint]
  exact storage_glob σ _ (Solidity.pushAt_with _ _ _ _ _)

theorem pop_run {E : Ty} (b : SPath C Γ (.array E)) :
    (Upd.nil.snoc (.storage (.app2 (if E.isMapping then .shrink else .pop)
      .storage b.lower))).apply σ = (TRun.pop_erase b).erased σ := by
  rw [upd1_apply]
  by_cases hE : E.isMapping = true
  · rw [if_pos hE]
    show (do
      let st ← Op2.eval σ.glob .shrink (pure σ.glob) (b.lower.eval σ)
      pure (σ.withGlob { σ.glob with storage := st.storage })) = _
    simp only [Op2.eval, SPath.eval_lower, StepAgrees.erased, hE, bind_assoc, pure_bind]
    congr 1; funext q
    exact storage_glob σ _ (Solidity.popAt_with _ _ _ _)
  · have hE' : E.isMapping = false := by simpa only [Bool.not_eq_true] using hE
    rw [if_neg hE]
    show (do
      let st ← Op2.eval σ.glob .pop (pure σ.glob) (b.lower.eval σ)
      pure (σ.withGlob { σ.glob with storage := st.storage })) = _
    simp only [Op2.eval, SPath.eval_lower, StepAgrees.erased, hE', bind_assoc, pure_bind]
    congr 1; funext q
    exact storage_glob σ _ (Solidity.popAt_with _ _ _ _)

theorem rebindPush_run {R : RefTy} (i : Idx Γ (.alias R)) (b : SPath C Γ (.array (.ref R)))
    (hd : (Ty.ref R).defaultOkS = true) :
    ((Upd.nil.snoc (.storage (.app2 (.extend (.ref R)) .storage b.lower))).snoc
      (.local i (.path (.app1 .next rfl b.lower)))).apply σ =
        (TRun.rebind_erase i (.push b hd)).erased σ := by
  rw [upd2_apply]
  show _ = _
  simp only [UpdElem.write, Rhs.eval, Tm.eval, Op2.eval, Op1.eval, Op0.eval, SPath.eval_lower,
    StepAgrees.erased, ARhs.eval, pushPlaceAt, SemanticsProperties.State.saveStorage_eq, bind_assoc,
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
    (Upd.nil.snoc (.payTo sadr se)).apply σ =
      (TRun.transfer_erase (.simple sadr) (.simple se)).erased σ := by
  rw [upd1_apply]
  obtain ⟨a, ha⟩ := Simple.eval_ok σ sadr
  obtain ⟨v, hv⟩ := Simple.eval_ok σ se
  show _ = _
  simp only [UpdElem.write, Simple.eval_lower, ha, hv, StepAgrees.erased, Val.eval, transferAt,
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
      Res.Sim (U.apply σ) ((TRun.send_erase pv (.simple sadr) (.simple se)).erased σ) := by
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
  have hr : (TRun.send_erase pv (.simple sadr) (.simple se)).erased σ = (do
      let addr ← a.asInt
      let amt ← v.asInt
      sendAt σ pv addr amt) := by
    show (TRun.send_erase pv (.simple sadr) (.simple se)).erased σ = _
    simp only [StepAgrees.erased, Val.eval, ha, hv, Res.bind_ok]
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

theorem declMemFresh_run (R : RefTy) (x : Var) (hm : (Ty.ref R).mapFree = true) :
    ((Upd.nil.decl x (.mref (.app1 (.alloc R) rfl .memory))).snoc
      (.memory (.app1 (.addM R) rfl .memory))).apply σ =
        (TRun.declMem_erase R none hm).erased σ := by
  show (do
    let τ ← (Upd.nil.decl x (.mref (.app1 (.alloc R) rfl .memory))).apply σ
    UpdElem.write σ (.memory (.app1 (.addM R) rfl .memory)) τ) = _
  simp only [Upd.apply, UpdElem.write, Rhs.eval, Tm.eval, Op1.eval, Op0.eval, StepAgrees.erased,
    Solidity.allocDefault_eq, bind_assoc, pure_bind]
  simp only [bind, Except.bind, pure, Except.pure]
  cases Solidity.allocHN σ.glob R <;> rfl

theorem deleteMemVar_run {R : RefTy} (i : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true) :
    ((Upd.nil.snoc (.local i (.mref (.app1 (.alloc R) rfl .memory)))).snoc
      (.memory (.app1 (.addM R) rfl .memory))).apply σ =
        (TRun.deleteMem_erase (.var i hm)).erased σ := by
  rw [upd2_apply]
  show _ = _
  simp only [UpdElem.write, Rhs.eval, Tm.eval, Op1.eval, Op0.eval, StepAgrees.erased,
    Solidity.allocDefault_eq, bind_assoc, pure_bind]
  simp only [bind, Except.bind, pure, Except.pure]
  cases Solidity.allocHN σ.glob R <;> rfl

theorem allocCopy_run {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) (v : Tm C Γ .sv)
    (hr : r.eval σ = (do
      let (τ, mv) ← Semantics.copyStToM σ.glob (← v.eval σ)
      pure (σ.withGlob τ, ← mv.asRef))) :
    ((Upd.nil.snoc (.local i (.mref (.app2 .copy .memory v)))).snoc
      (.memory (.app2 .copySt .memory v))).apply σ = (TRun.rebindMem_erase i r).erased σ := by
  rw [upd2_apply]
  show _ = _
  simp only [StepAgrees.erased, hr, UpdElem.write, Rhs.eval, Tm.eval, Op2.eval, Op0.eval,
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
      Res.Sim (U.apply σ) ((TRun.deleteMem_erase (.loc l)).erased σ) := by
  cases T with
  | prim p =>
    refine ⟨_, rfl, Res.Sim.of_eq ?_⟩
    rw [upd1_apply]
    show _ = _
    simp only [UpdElem.write, Tm.eval, Op3.eval, Op1.eval, Op0.eval, MLoc.eval_lower_addr,
      StepAgrees.erased, memClear, bind_assoc, pure_bind, writeAddr_glob]
  | ref R =>
    refine ⟨_, rfl, ?_⟩
    rw [upd1_apply]
    show Res.Sim _ ((TRun.deleteMem_erase (.loc l)).erased σ)
    simp only [UpdElem.write, Tm.eval, Op3.eval, Op1.eval, Op0.eval, MLoc.eval_lower_addr,
      StepAgrees.erased, memClear, Solidity.allocDefault_eq, bind_assoc, pure_bind]
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

/-! ## The other update arms (`Step.lean`) -/

section Arms2

variable {Γ : Ctx} {m : Modality} (σ : TState C Γ)

/-- `storagePushLengthSave`: `{storage := pushSlot(storage, b)}`. -/
theorem sound_pushSlot {E : Ty} (b : SPath C Γ (.array E))
    (hd : (none.isSome || E.defaultOkS) = true) :
    Premise.Runs m (.push b none hd) (.upd1 (.storage (.app2 (.pushSlot E) .storage b.lower))) σ :=
  Premise.sound_update_erased (TRun.push_erase b none)
    σ (pushSlot_run σ.erase b) fun _ => TRun.push_nd σ b none

/-- `storagePushLengthSaveReferenceElement`: `{storage := extend(storage, b)}`. -/
theorem sound_extend {E : Ty} (b : SPath C Γ (.array E))
    (hd : (none.isSome || E.defaultOkS) = true) :
    Premise.Runs m (.push b none hd) (.upd1 (.storage (.app2 (.extend E) .storage b.lower))) σ :=
  Premise.sound_update_erased (TRun.push_erase b none)
    σ (extend_run σ.erase b) fun _ => TRun.push_nd σ b none

/-- `storagePushValueSave`, `storagePushValueCopySource`:
`{storage := push(storage, b, src)}`. -/
theorem sound_pushSome {E : Ty} (b : SPath C Γ (.array E)) (r : Src C Γ E)
    (hd : ((some r).isSome || E.defaultOkS) = true) :
    Premise.Runs m (.push b (some r) hd)
      (.upd1 (.storage (.app3 .push .storage b.lower r.lower))) σ :=
  Premise.sound_update_erased (TRun.push_erase b (some r))
    σ (pushSome_run σ.erase b r) fun _ => TRun.push_nd σ b (some r)

/-- `storagePopSave`, `storagePopSaveMappingElement`. -/
theorem sound_pop {E : Ty} (b : SPath C Γ (.array E)) :
    Premise.Runs m (.pop b) (.upd1 (.storage (.app2 (if E.isMapping then .shrink else .pop)
      .storage b.lower))) σ :=
  Premise.sound_update_erased (TRun.pop_erase b) σ (pop_run σ.erase b) fun _ =>
    ((SPath.resolveT_ends σ b).bind fun _ => (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _).1

/-- `storageLocalRootPushBind`, `storageLocalRootPushBindMappingElement`:
`{storage := extend(storage, b) ‖ lsv := next(b)}`. -/
theorem sound_rebindPush {R : RefTy} (i : Idx Γ (.alias R)) (b : SPath C Γ (.array (.ref R)))
    (hd : (Ty.ref R).defaultOkS = true) :
    Premise.Runs m (.rebind i (.push b hd)) (.update ((Upd.nil.snoc
      (.storage (.app2 (.extend (.ref R)) .storage b.lower))).snoc
      (.local i (.path (.app1 .next rfl b.lower))))) σ :=
  Premise.sound_update_erased (TRun.rebind_erase i (.push b hd))
    σ (rebindPush_run σ.erase i b hd) fun _ =>
    TRes.NoDiv.bind (ARhs.evalT_nd σ (.push b hd)) fun _ => TRes.NoDiv.ok _

/-- `transferNoCallbackBox`: `{net := …}`. -/
theorem sound_transferBox (sadr se : Simple C Γ .uint) :
    Premise.Runs m (.transfer (.simple sadr) (.simple se)) (.upd1 (.payTo sadr se)) σ :=
  Premise.sound_update_erased (TRun.transfer_erase (.simple sadr) (.simple se))
    σ (transferBox_run σ.erase sadr se) fun _ => TRes.NoDiv.ok _

/-- `transferDiamond` (Lean): the goal fails. -/
theorem sound_done_false {Γ' : Ctx} (s : Stmt C Γ Γ') : Premise.Sound m s (.done false) σ :=
  Premise.sound_done σ false fun h => nomatch h

/-- `sendNoCallbackBox`, `sendNoCallbackDiamond`: the payment with `pv` true,
or `pv` false. -/
theorem sound_send (pv : Idx Γ (.val .bool)) (sadr se : Simple C Γ .uint) (fs : List (Fml C Γ)) :
    Premise.Sound m (.send pv (.simple sadr) (.simple se)) (.cases fs
      [(Upd.nil.snoc (.payTo sadr se)).snoc (.local pv (.val (Tm.lit (.bool true)))),
        Upd.nil.snoc (.local pv (.val (Tm.lit (.bool false))))]) σ :=
  Premise.sound_cases_erased (s := .send pv (.simple sadr) (.simple se))
    (TRun.send_erase pv (.simple sadr) (.simple se)) σ
    (fun _ => send_run σ.erase pv sadr se) fun _ => TRes.NoDiv.ok _

/-- `memoryReferenceDeclFreshAlloc`. -/
theorem sound_declMemFresh (R : RefTy) (x : Var)
    (hd : (none.isSome || (Ty.ref R).defaultOkS) = true) (hm : (Ty.ref R).mapFree = true) :
    Premise.Runs m (.declMem R x none hd hm) (.update ((Upd.nil.decl x
      (.mref (.app1 (.alloc R) rfl .memory))).snoc (.memory (.app1 (.addM R) rfl .memory)))) σ :=
  Premise.sound_update_erased (TRun.declMem_erase R none hm)
    σ (declMemFresh_run σ.erase R x hm) fun _ => TRes.NoDiv.ok _

/-- `memoryRootDeleteFreshRebind`. -/
theorem sound_deleteMemVar {R : RefTy} (i : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    (hd : (Ty.ref R).defaultOkS = true) :
    Premise.Runs m (.deleteMem (.var i hm) hd) (.update ((Upd.nil.snoc
      (.local i (.mref (.app1 (.alloc R) rfl .memory)))).snoc
      (.memory (.app1 (.addM R) rfl .memory)))) σ :=
  Premise.sound_update_erased (TRun.deleteMem_erase (.var i hm))
    σ (deleteMemVar_run σ.erase i hm) fun _ => TRes.NoDiv.ok _

/-- `memoryStorageCopy`, `memoryArrayFreshAlloc`, given the reading of the
right-hand side on the erasure. -/
theorem sound_allocCopy {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) (v : Tm C Γ .sv)
    (hr : r.eval σ.erase = (do
      let (τ, mv) ← Semantics.copyStToM σ.erase.glob (← v.eval σ.erase)
      pure (σ.erase.withGlob τ, ← mv.asRef))) :
    Premise.Runs m (.rebindMem i r) (.allocCopy i v) σ :=
  Premise.sound_update_erased (TRun.rebindMem_erase i r) σ (allocCopy_run σ.erase i r v hr) fun _ =>
    ((MRhs.evalT_ends σ r).bind fun _ => TRes.Ends.ok _).1

theorem clearT_ends : {T : Ty} → (a : MAddr σ.H T) → (hm : T.mapFree = true) →
    (TRun.clearT σ a hm).Ends
  | .prim _, _, _ => (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _
  | .ref R, a, hm => by
    simp only [TRun.clearT]
    split <;> exact ⟨(fun h => nomatch h), fun h => nomatch h⟩

/-- `memoryFieldDelete*`, `memoryIndexDelete*`: a slot reset to its default,
or written a fresh default object. -/
theorem sound_clearMem {T : Ty} (l : MLoc C Γ T) (hd : T.defaultOkS = true) :
    Premise.Runs m (.deleteMem (.loc l) hd) (.clearMem l.lower T) σ := by
  obtain ⟨U, hU, hs⟩ := clearMem_run σ.erase l hd
  rw [hU]
  exact Premise.sound_updateSim_erased (TRun.deleteMem_erase (.loc l)) σ hs fun _ =>
    ((MLoc.addrT_ends σ l).bind fun a => clearT_ends σ a _).1

/-- `valueDeclSkip`: `{v := defVal(T)}`. -/
theorem sound_valueDeclSkip (p : PrimTy) (x : Var) :
    Premise.Runs m (.declLocal p x none)
      (.update (Upd.nil.decl x (.val (p := p) (.app0 (.lit p.default))))) σ :=
  Premise.sound_update_erased (s := .declLocal p x none) (TRun.declLocal_erase p none)
    σ rfl fun _ => TRes.NoDiv.ok _

/-- `storageLocalDeclSkip`: `{lsv := unset}`. -/
theorem sound_storageLocalDeclSkip (R : RefTy) (x : Var) :
    Premise.Runs m (.declStorage R x none) (.update (Upd.nil.decl (t := .alias R) x .unset)) σ :=
  Premise.sound_update_erased (s := .declStorage R x none) (TRun.declStorage_erase R none)
    σ rfl fun _ => TRes.NoDiv.ok _

/-- `revertBox`, `revertDiamond`. -/
theorem sound_revert :
    Premise.Sound m (.revert : Stmt C Γ Γ) (.done (m == .box)) σ :=
  Premise.sound_done σ _ fun h =>
    ⟨by cases m <;> first | rfl | exact absurd h (by decide), .revert, rfl, by decide⟩

end Arms2

end Solidity.Core
