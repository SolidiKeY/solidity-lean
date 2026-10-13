import Solidity.Calculus.SoundKit

/-!
# Soundness of the update arms

The rules of `Calculus/Arms.lean` and `Step.lean` whose premise is an
update (`Premise.Sound`, `Calculus/PremiseSound.lean`).  An update is
computed on the typed state as a typed global part and the locals' values
(`Upd.applyP`), so each arm states that the statement's typed step
(`TRun.*`, `Semantics/Run.lean`) agrees with what the update computes in the
state it starts in (`*_agrees`, `TRes.AgreesO` of the state it ends in, read
as `(State.glob, State.locV)`), and closes with `Premise.sound_update_typed`
(`Calculus/SoundKit.lean`).  Nothing is erased (W9.8.3): an update's terms
read the typed operations the run does (`Calculus/LowerRun.lean` for the
lowered expressions), so an agreement follows the run's binds
(`TRes.AgreesO.cases`) and computes the term on what they returned.

The arms ask of the typed run that it does not diverge under the diamond:
an expression, a location and every write but a push neither diverge nor
are exhausted (`Val.evalT_ends` and its kin,
`Semantics/Ends.lean`), and a push onto `2^256 - 1` elements is
exhausted (`TRun.push_nd`, decision 15), which both modalities accept.
-/

namespace Solidity
open Solidity (Modality Srt)
open Semantics (lookupBy setBy)

variable {C : Contract}

/-! ## Following the run's binds -/

/-- **The run's bind, against a reading**: where the run returns `a`, its
part read `some (f a)`; where it reverts, read `none`, the reading `X` is
`none`. -/
theorem TRes.AgreesO.cases {α β γ δ : Type} {f : α → β} {t : TRes α} {u : Option β}
    (h : TRes.AgreesO f t u) {g : γ → δ} {k : α → TRes γ} {X : Option δ}
    (hok : ∀ a, u = some (f a) → TRes.AgreesO g (k a) X) (hnone : u = none → X = none) :
    TRes.AgreesO g (t >>= k) X := by
  match t, h with
  | .ok a, h => exact hok a h
  | .error .revert, h => exact hnone h
  | .error .diverge, _ => trivial
  | .error .exhausted, _ => trivial

/-- A step that only returns, against its reading. -/
theorem TRes.AgreesO.ret {γ δ : Type} {g : γ → δ} {c : γ} {X : Option δ} (h : X = some (g c)) :
    TRes.AgreesO g (Except.ok c : TRes γ) X := h

theorem Option.bind_swap {α β γ : Type} (x : Option α) (y : Option β) (f : α → β → Option γ) :
    (x.bind fun a => y.bind fun b => f a b) = y.bind fun b => x.bind fun a => f a b := by
  cases x <;> cases y <;> rfl

/-! ## Updates computed -/

section Updates

variable {Γ : Ctx} (σ : State C Γ)

theorem applyP_snoc {Δ : Ctx} (U : Upd C Γ Δ) (e : UpdElem C Γ Δ) :
    (U.snoc e).applyP σ = (U.applyV σ).bind fun p => (e.applyV σ p.1 p.2).map fun q => (q.1.1, q.2) := by
  show ((U.applyV σ).bind fun p => e.applyV σ p.1 p.2).map _ = _
  cases U.applyV σ <;> rfl

theorem applyV_nil : (Upd.nil : Upd C Γ Γ).applyV σ = some (σ.globG, σ.locV) := rfl

/-- A `storage :=` element. -/
theorem UpdElem.applyV_storage {Δ : Ctx} (t : Tm C Γ .st) (g : GlobT C σ.H) (ℓ : LocsV C Δ) :
    (UpdElem.storage t : UpdElem C Γ Δ).applyV σ g ℓ =
      (t.eval σ).map fun st => (g.withStorage st, ℓ) := by
  rw [UpdElem.applyV_eq_applyVM]
  show ((UpdElem.storage t : UpdElem C Γ Δ).globT σ g).bind _ = _
  rw [UpdElem.globT_eq_globTM]
  show ((t.eval σ).bind fun st => some (g.withStorage st)).bind _ = _
  cases t.eval σ <;> rfl

/-- A `memory :=` element. -/
theorem UpdElem.applyV_memory {Δ : Ctx} (t : Tm C Γ .mem) (g : GlobT C σ.H) (ℓ : LocsV C Δ) :
    (UpdElem.memory t : UpdElem C Γ Δ).applyV σ g ℓ =
      (t.eval σ).map fun μ => (g.withMem μ, ℓ) := by
  rw [UpdElem.applyV_eq_applyVM]
  show ((UpdElem.memory t : UpdElem C Γ Δ).globT σ g).bind _ = _
  rw [UpdElem.globT_eq_globTM]
  show ((t.eval σ).bind fun μ => some (g.withMem μ)).bind _ = _
  cases t.eval σ <;> rfl

/-- A local's element. -/
theorem UpdElem.applyV_local {Δ : Ctx} {t : LTy} (i : Idx Δ t) (r : Rhs C Γ t) (g : GlobT C σ.H)
    (ℓ : LocsV C Δ) :
    (UpdElem.local i r : UpdElem C Γ Δ).applyV σ g ℓ = (r.eval σ).map fun v => (g, ℓ.set i v) := by
  rw [UpdElem.applyV_eq_applyVM]
  show (r.eval σ).bind _ = _
  cases r.eval σ <;> rfl

/-- One storage element on its own. -/
theorem applyP_storage1 (t : Tm C Γ .st) :
    (Upd.nil.snoc (UpdElem.storage t)).applyP σ =
      (t.eval σ).map fun st => ((σ.withStorage st).glob, σ.locV) := by
  rw [applyP_snoc, applyV_nil, Option.bind_some, UpdElem.applyV_storage]
  cases t.eval σ <;> rfl

/-- One memory element on its own. -/
theorem applyP_memory1 (t : Tm C Γ .mem) :
    (Upd.nil.snoc (UpdElem.memory t)).applyP σ =
      (t.eval σ).map fun μ => ((σ.globG.withMem μ).1, σ.locV) := by
  rw [applyP_snoc, applyV_nil, Option.bind_some, UpdElem.applyV_memory]
  cases t.eval σ <;> rfl

/-- One local element on its own. -/
theorem applyP_local1 {t : LTy} (i : Idx Γ t) (r : Rhs C Γ t) :
    (Upd.nil.snoc (UpdElem.local i r)).applyP σ =
      (r.eval σ).map fun v => (σ.glob, σ.locV.set i v) := by
  rw [applyP_snoc, applyV_nil, Option.bind_some, UpdElem.applyV_local]
  cases r.eval σ <;> rfl

/-! ### Terms computed -/

theorem Tm.eval_storage : (Tm.app0 .storage : Tm C Γ .st).eval σ = some σ.storage := rfl
theorem Tm.eval_memory : (Tm.app0 .memory : Tm C Γ .mem).eval σ = some σ.glob.memT := rfl
theorem Tm.eval_lit {p : PrimTy} (v : p.Denote) : (Tm.app0 (.lit v) : Tm C Γ (.val p)).eval σ = some v :=
  rfl
theorem Tm.eval_pvV {p : PrimTy} (i : Idx Γ (.val p)) :
    (Tm.pvV i : Tm C Γ (.val p)).eval σ = some (TEnv.get i σ.env) := rfl

theorem Tm.eval_save {T : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path T)) (v : Tm C Γ (.sv T)) :
    (Tm.app3 .save s q v).eval σ =
      (s.eval σ).bind fun st => (q.eval σ).bind fun r => (v.eval σ).bind fun w => st.write r w := by
  rw [Tm.eval_app3, Op3.eval_eq_evalM]; rfl

theorem Tm.eval_push {E : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path (.ref (.array E))))
    (v : Tm C Γ (.sv E)) :
    (Tm.app3 .push s q v).eval σ = (s.eval σ).bind fun st => (q.eval σ).bind fun r =>
      st.push r fun _ => (v.eval σ).map SVal.strip := by
  rw [Tm.eval_app3, Op3.eval_eq_evalM]; rfl

theorem Tm.eval_write {T : Ty} (m : Tm C Γ .mem) (a : Tm C Γ (.addr T)) (v : Tm C Γ (.mv T)) :
    (Tm.app3 .write m a v).eval σ =
      (m.eval σ).bind fun μ => (a.eval σ).bind fun ad => (v.eval σ).bind fun w => μ.writeT ad w := by
  rw [Tm.eval_app3, Op3.eval_eq_evalM]; rfl

theorem Tm.eval_find {p : PrimTy} (s : Tm C Γ .st) (q : Tm C Γ (.path (.prim p))) :
    (Tm.app2 .find s q).eval σ =
      (s.eval σ).bind fun st => (q.eval σ).bind fun r => (st.find r).bind fun w => some w.view := by
  rw [Tm.eval_app2, Op2.eval_eq_evalM]; rfl

theorem Tm.eval_sfind {T : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path T)) :
    (Tm.app2 .sfind s q).eval σ = (s.eval σ).bind fun st => (q.eval σ).bind fun r => st.find r := by
  rw [Tm.eval_app2, Op2.eval_eq_evalM]; rfl

theorem Tm.eval_delAt {T : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path T)) :
    (Tm.app2 .delAt s q).eval σ = (s.eval σ).bind fun st => (q.eval σ).bind fun r => st.delete r := by
  rw [Tm.eval_app2, Op2.eval_eq_evalM]; rfl

theorem Tm.eval_pushSlot {E : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path (.ref (.array E)))) :
    (Tm.app2 .pushSlot s q).eval σ =
      (s.eval σ).bind fun st => (q.eval σ).bind fun r => st.push r some := by
  rw [Tm.eval_app2, Op2.eval_eq_evalM]; rfl

theorem Tm.eval_extend {E : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path (.ref (.array E)))) :
    (Tm.app2 .extend s q).eval σ =
      (s.eval σ).bind fun st => (q.eval σ).bind fun r => (st.pushPlace r).map (·.1) := by
  rw [Tm.eval_app2, Op2.eval_eq_evalM]
  show (s.eval σ).bind (fun st => (q.eval σ).bind fun r => (st.pushPlace r).bind fun p => some p.1) = _
  congr 1; funext st; congr 1; funext r
  cases st.pushPlace r <;> rfl

theorem Tm.eval_pop {E : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path (.ref (.array E)))) :
    (Tm.app2 .pop s q).eval σ = (s.eval σ).bind fun st => (q.eval σ).bind fun r => st.pop false r := by
  rw [Tm.eval_app2, Op2.eval_eq_evalM]; rfl

theorem Tm.eval_shrink {E : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path (.ref (.array E)))) :
    (Tm.app2 .shrink s q).eval σ = (s.eval σ).bind fun st => (q.eval σ).bind fun r => st.pop true r := by
  rw [Tm.eval_app2, Op2.eval_eq_evalM]; rfl

theorem Tm.eval_copyMem {R : RefTy} (m : Tm C Γ .mem) (i : Tm C Γ (.ident R)) :
    (Tm.app2 .copyMem m i).eval σ = (m.eval σ).bind fun μ => (i.eval σ).bind fun id =>
      (HRef.ofId? μ.H' R id).bind fun r => some (MVal.copyMToSt μ.heap (T := .ref R) r) := by
  rw [Tm.eval_app2, Op2.eval_eq_evalM]; rfl

theorem Tm.eval_sval {p : PrimTy} (t : Tm C Γ (.val p)) :
    (Tm.app1 .sval t).eval σ = (t.eval σ).map SVal.prim := by
  rw [Tm.eval_app1, Op1.eval_eq_evalM]; rfl

theorem Tm.eval_mval {p : PrimTy} (t : Tm C Γ (.val p)) :
    (Tm.app1 .mval t).eval σ = t.eval σ := by
  rw [Tm.eval_app1, Op1.eval_eq_evalM]; rfl

theorem Tm.eval_ref {R : RefTy} (t : Tm C Γ (.ident R)) :
    (Tm.app1 .ref t).eval σ = t.eval σ := by
  rw [Tm.eval_app1, Op1.eval_eq_evalM]; rfl

theorem Tm.eval_next {E : Ty} (q : Tm C Γ (.path (.ref (.array E)))) :
    (Tm.app1 .next q).eval σ = (q.eval σ).bind σ.storage.nextT := by
  rw [Tm.eval_app1, Op1.eval_eq_evalM]; rfl

theorem Tm.eval_castV {p q : PrimTy} (h : p = q) (t : Tm C Γ (.val p)) :
    (Tm.castV h t).eval σ = h ▸ t.eval σ := by
  subst h; rfl

theorem Tm.eval_binop (op : BinOp) {p : PrimTy} (h : op.accepts p = true) (a b : Tm C Γ (.val p)) :
    (Tm.app2 (.binop op h) a b).eval σ = (a.eval σ).bind fun x => binopT op x (b.eval σ) := by
  rw [Tm.eval_app2, Op2.eval_eq_evalM]; rfl

/-- A grown heap's memory, written at a typed address with a typed slot. -/
theorem Grown.writeT_toT {H : HTy} (m : Grown H (fun _ => Unit)) {T : Ty} (a : MAddr m.H' T)
    (v : MVal m.H' T) :
    m.writeT a.toT (MVal.toT T v) = (m.heap.writeAddr a v).map fun hp => ⟨m.ext, hp, ()⟩ := by
  have hv : MvT.toMVal m.H' T (MVal.toT T v) = some v := by
    cases T with
    | prim _ => rfl
    | ref R => exact HRef.ofId?_id (v : HRef m.H' R)
  simp only [Grown.writeT, MAddr.resolve_toT, hv, Option.bind_eq_bind, Option.bind_some]
  cases m.heap.writeAddr a v <;> rfl

theorem Grown.writeT_toT_prim {H : HTy} (m : Grown H (fun _ => Unit)) {p : PrimTy}
    (a : MAddr m.H' (.prim p)) (v : p.Denote) :
    m.writeT a.toT v = (m.heap.writeAddr a v).map fun hp => ⟨m.ext, hp, ()⟩ :=
  Grown.writeT_toT m a (T := .prim p) v

theorem TRes.ofOpt_some_bind {α β : Type} (a : α) (f : α → TRes β) :
    (TRes.ofOpt (some a) >>= f) = f a := rfl

theorem TRes.ofOpt_none_bind {α β : Type} (f : α → TRes β) :
    (TRes.ofOpt (none : Option α) >>= f) = .error .revert := rfl

/-- A storage write of a word is its save. -/
theorem Storage.write_prim {p : PrimTy} (st : Storage C) (r : SRef C (.prim p)) (x : p.Denote) :
    st.write r (.prim x) = st.save r (.prim x) := rfl

end Updates

/-! ## The agreements: the typed step against the update

Each update arm's typed step against what its update computes, as
`Premise.sound_update_typed` asks. -/

section Agrees

variable {Γ : Ctx} (σ : State C Γ)

theorem setLocal_agrees {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV)) (TRun.assignLocal i v σ)
      ((Upd.nil.snoc (UpdElem.setLocal i v)).applyP σ) := by
  rw [UpdElem.setLocal, applyP_local1]
  show TRes.AgreesO _ _ ((v.lower.eval σ).map _)
  refine (Val.lower_evalT σ v).cases (fun x hx => ?_) (fun hx => by rw [hx]; rfl)
  refine TRes.AgreesO.ret ?_
  rw [hx, State.locV_setLocal]
  rfl

theorem save_agrees {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV)) (TRun.assign l r σ)
      ((Upd.nil.snoc (UpdElem.save l r)).applyP σ) := by
  rw [UpdElem.save, applyP_storage1, Tm.eval_save, Tm.eval_storage, Option.bind_some]
  refine (Src.lower_valueT σ r).cases (fun sv hsv => ?_) (fun hsv => ?_)
  · refine (Loc.lower_resolveT σ l).cases (fun ref href => ?_) (fun href => by rw [href]; rfl)
    rw [href, hsv]
    show TRes.AgreesO _ (TRes.ofOpt (σ.storage.write ref sv) >>= _) ((σ.storage.write ref sv).map _)
    cases σ.storage.write ref sv <;> rfl
  · rw [hsv]
    cases l.lower.eval σ <;> rfl

theorem saveMem_agrees {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV)) (TRun.assignFromMem l p σ)
      ((Upd.nil.snoc (UpdElem.saveMem l p)).applyP σ) := by
  rw [UpdElem.saveMem, applyP_storage1, Tm.eval_save, Tm.eval_storage, Option.bind_some,
    Tm.eval_copyMem, Tm.eval_memory, Option.bind_some]
  refine (MPath.lower_mvalT σ p).cases (fun m hm => ?_) (fun hm => ?_)
  · refine (Loc.lower_resolveT σ l).cases (fun ref href => ?_) (fun href => by rw [href]; rfl)
    rw [href, hm]
    simp only [Option.bind_some, State.memT, HRef.ofId?_id, id]
    show TRes.AgreesO _ (TRes.ofOpt (σ.storage.write ref (MVal.copyMToSt σ.heap m)) >>= _)
      ((σ.storage.write ref (MVal.copyMToSt σ.heap m)).map _)
    cases σ.storage.write ref (MVal.copyMToSt σ.heap m) <;> rfl
  · rw [hm]
    cases l.lower.eval σ <;> rfl

theorem delAt_agrees {T : Ty} (l : Loc C Γ T) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV)) (TRun.delete l σ)
      ((Upd.nil.snoc (UpdElem.delAt l)).applyP σ) := by
  rw [UpdElem.delAt, applyP_storage1, Tm.eval_delAt, Tm.eval_storage, Option.bind_some]
  refine (Loc.lower_resolveT σ l).cases (fun ref href => ?_) (fun href => by rw [href]; rfl)
  rw [href]
  show TRes.AgreesO _ (TRes.ofOpt (σ.storage.delete ref) >>= _) ((σ.storage.delete ref).map _)
  cases σ.storage.delete ref <;> rfl

theorem writeMem_agrees {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV)) (TRun.assignMem l r σ)
      ((Upd.nil.snoc (UpdElem.writeMem l r)).applyP σ) := by
  rw [UpdElem.writeMem, applyP_memory1, Tm.eval_write, Tm.eval_memory, Option.bind_some]
  refine (MSrc.lower_mvalT σ r).cases (fun mv hmv => ?_) (fun hmv => ?_)
  · refine (MLoc.lower_addrT σ l).cases (fun a ha => ?_) (fun ha => by rw [ha]; rfl)
    rw [ha, hmv]
    simp only [Option.bind_some]
    rw [Grown.writeT_toT (σ.glob.memT) a mv]
    show TRes.AgreesO _ (TRes.ofOpt (σ.heap.writeAddr a mv) >>= _)
      (((σ.heap.writeAddr a mv).map _).map _)
    cases σ.heap.writeAddr a mv <;> rfl
  · rw [hmv]
    cases l.lower.eval σ <;> rfl

theorem rebindPath_agrees {R : RefTy} (i : Idx Γ (.alias R)) (p : SPath C Γ (.ref R)) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV)) (TRun.rebind i (.path p) σ)
      ((Upd.nil.snoc (UpdElem.rebind i p)).applyP σ) := by
  rw [UpdElem.rebind, applyP_local1]
  show TRes.AgreesO _ ((do pure (σ.storage, ← p.resolveT σ)) >>= _)
    (((p.lower.eval σ).bind fun r => some (some r)).map _)
  rw [bind_assoc]
  refine (SPath.lower_resolveT σ p).cases (fun ref href => ?_) (fun href => by rw [href]; rfl)
  refine TRes.AgreesO.ret ?_
  rw [href, State.locV_setLocal]
  rfl

theorem rebindMemAlias_agrees {R : RefTy} (i : Idx Γ (.mem R)) (p : MPath C Γ (.ref R)) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV)) (TRun.rebindMem i (.alias p) σ)
      ((Upd.nil.snoc (UpdElem.rebindMem i p)).applyP σ) := by
  rw [UpdElem.rebindMem, applyP_local1]
  show TRes.AgreesO _ ((do let r ← p.mvalT σ; pure (⟨σ, List.prefix_refl _, r⟩ :
      Grew C Γ σ.H (HRef · R))) >>= _)
    (((p.lower.eval σ).bind fun id => some (some id)).map _)
  rw [bind_assoc]
  refine (MPath.lower_mvalT σ p).cases (fun r hr => ?_) (fun hr => by rw [hr]; rfl)
  refine TRes.AgreesO.ret ?_
  rw [hr, State.locV_setLocal]
  rfl

end Agrees

/-! ### Compound targets -/

section OpLoc

variable {Γ : Ctx} (σ : State C Γ) {op : BinOp} {p : PrimTy}

theorem Tm.eval_read {p : PrimTy} (m : Tm C Γ .mem) (a : Tm C Γ (.addr (.prim p))) :
    (Tm.app2 .read m a).eval σ = (m.eval σ).bind fun μ => (a.eval σ).bind fun ad => μ.readT ad := by
  rw [Tm.eval_app2, Op2.eval_eq_evalM]; rfl

/-- A compound operator on two terms is `compoundT` on the integers they read. -/
theorem Tm.eval_compound (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
    (a b : Tm C Γ (.val p)) :
    (Tm.castV (BinOp.compound_ret hop p)
      (Tm.app2 (.binop op (BinOp.compound_accepts hop hp)) a b)).eval σ =
      (a.eval σ).bind fun x => (b.eval σ).bind fun y => compoundT op p (PrimTy.key x) (PrimTy.key y) := by
  rw [Tm.eval_castV, Tm.eval_binop]
  cases op <;> simp only [BinOp.hasCompoundAssign, Bool.false_eq_true] at hop <;>
    cases p <;> simp only [PrimTy.isNumeric, Bool.false_eq_true] at hp <;>
    cases a.eval σ <;> cases b.eval σ <;> rfl

/-- `++`/`--` on a term is `bumpT` on the integer it reads. -/
theorem Tm.eval_bump (o : IncDec) (hp : p.isNumeric = true) (a : Tm C Γ (.val p)) :
    (Tm.castV (BinOp.compound_ret (IncDec.binOp_compound o) p)
      (Tm.app2 (.binop o.binOp (BinOp.compound_accepts (IncDec.binOp_compound o) hp)) a
        (Tm.one p hp))).eval σ =
      (a.eval σ).bind fun x => bumpT o p (PrimTy.key x) := by
  rw [Tm.eval_castV, Tm.eval_binop]
  cases o <;> cases p <;> simp only [PrimTy.isNumeric, Bool.false_eq_true] at hp <;>
    cases a.eval σ <;> rfl

theorem storeLoc_agrees (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
    (L : Loc C Γ (.prim p)) (v : p.Denote) (t : Tm C Γ (.val p)) (ht : t.eval σ = some v) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV)) (do opStoreT σ op (← L.resolveT σ) v)
      ((Upd.nil.snoc (.storage (.app3 .save (.app0 .storage) L.lower (.app1 .sval
        (Tm.castV (BinOp.compound_ret hop p) (.app2 (.binop op (BinOp.compound_accepts hop hp))
          (Val.read L).lower t)))))).applyP σ) := by
  rw [applyP_storage1, Tm.eval_save, Tm.eval_storage, Option.bind_some, Tm.eval_sval,
    Tm.eval_compound σ hop hp, ht]
  show TRes.AgreesO _ _ (((L.lower.eval σ).bind fun r =>
    ((((Tm.app2 .find (.app0 .storage) L.lower).eval σ).bind fun x =>
      compoundT op p (PrimTy.key x) (PrimTy.key v)).map SVal.prim).bind fun w =>
        σ.storage.write r w).map _)
  rw [Tm.eval_find, Tm.eval_storage, Option.bind_some]
  refine (Loc.lower_resolveT σ L).cases (fun ref href => ?_) (fun href => by rw [href]; rfl)
  rw [href]
  simp only [Option.bind_some, id, opStoreT]
  cases hf : σ.storage.find ref with
  | none => rfl
  | some old =>
    simp only [Option.bind_some, TRes.ofOpt_some_bind]
    cases hc : compoundT op p (PrimTy.key (SVal.view old)) (PrimTy.key v) with
    | none => rfl
    | some new =>
      simp only [Option.map_some, Option.bind_some, TRes.ofOpt_some_bind]
      show TRes.AgreesO _ (TRes.ofOpt (σ.storage.save ref (.prim new)) >>= _)
        ((σ.storage.write ref (.prim new)).map _)
      rw [Storage.write_prim]
      cases σ.storage.save ref (.prim new) <;> rfl

theorem storeMem_agrees (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
    (L : MLoc C Γ (.prim p)) (v : p.Denote) (t : Tm C Γ (.val p)) (ht : t.eval σ = some v) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV)) (do opMemT σ op (← L.addrT σ) v)
      ((Upd.nil.snoc (.memory (.app3 .write (.app0 .memory) L.lower (.app1 .mval
        (Tm.castV (BinOp.compound_ret hop p) (.app2 (.binop op (BinOp.compound_accepts hop hp))
          (Val.readMem L).lower t)))))).applyP σ) := by
  rw [applyP_memory1, Tm.eval_write, Tm.eval_memory, Option.bind_some, Tm.eval_mval,
    Tm.eval_compound σ hop hp, ht]
  show TRes.AgreesO _ _ (((L.lower.eval σ).bind fun ad =>
    ((((Tm.app2 .read (.app0 .memory) L.lower).eval σ).bind fun x =>
      compoundT op p (PrimTy.key x) (PrimTy.key v))).bind fun w =>
        σ.glob.memT.writeT ad w).map _)
  rw [Tm.eval_read, Tm.eval_memory, Option.bind_some]
  refine (MLoc.lower_addrT σ L).cases (fun a ha => ?_) (fun ha => by rw [ha]; rfl)
  rw [ha]
  simp only [Option.bind_some, opMemT, Grown.readT, State.memT, MAddr.resolve_toT,
    Option.bind_eq_bind]
  change TRes.AgreesO _ _ ((((σ.heap.readAddr a).bind fun x => _).bind fun w =>
    Grown.writeT ⟨List.prefix_refl σ.H, σ.heap, ()⟩ a.toT w).map _)
  cases hf : σ.heap.readAddr a with
  | none => rfl
  | some old =>
    simp only [Option.bind_some, TRes.ofOpt_some_bind]
    cases hc : compoundT op p (PrimTy.key (p := p) old) (PrimTy.key v) with
    | none => rfl
    | some new =>
      simp only [Option.bind_some, TRes.ofOpt_some_bind]
      rw [Grown.writeT_toT_prim ⟨List.prefix_refl σ.H, σ.heap, ()⟩ a new]
      show TRes.AgreesO _ (TRes.ofOpt (σ.heap.writeAddr a new) >>= _)
        (((σ.heap.writeAddr a new).map _).map _)
      cases σ.heap.writeAddr a new <;> rfl

theorem opAssign_agrees (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
    (l : OpLoc C Γ p) (se : Simple C Γ p) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV)) (TRun.opAssign op l (.simple se) σ)
      ((Upd.nil.snoc (l.set (l.op op hop hp se.lower))).applyP σ) := by
  have hse := Simple.lower_evalT σ se
  show TRes.AgreesO _ (l.storeT σ op (se.evalT σ)) _
  cases l with
  | «local» i =>
    rw [OpLoc.set, applyP_local1]
    show TRes.AgreesO _ _ (((Tm.castV _ (.app2 (.binop op _) (.pvV i) se.lower)).eval σ).map _)
    rw [Tm.eval_compound σ hop hp, Tm.eval_pvV, hse]
    simp only [Option.bind_some, OpLoc.storeT]
    cases compoundT op p (PrimTy.key (TEnv.get i σ.env)) (PrimTy.key (se.evalT σ)) with
    | none => rfl
    | some new =>
      refine TRes.AgreesO.ret ?_
      rw [Option.map_some, State.locV_setLocal]
      rfl
  | root r h => exact storeLoc_agrees σ hop hp (.root r h) _ se.lower hse
  | field b f h => exact storeLoc_agrees σ hop hp (.field b f h) _ se.lower hse
  | index it b ie => exact storeLoc_agrees σ hop hp (.index it b (.simple ie)) _ se.lower hse
  | mfield b f h => exact storeMem_agrees σ hop hp (.field b f h) _ se.lower hse
  | mindex a b ie => exact storeMem_agrees σ hop hp (.index a b (.simple ie)) _ se.lower hse


/-- The update's first element, a storage write, before the second. -/
theorem applyV_storage1 (t : Tm C Γ .st) :
    (Upd.nil.snoc (UpdElem.storage t)).applyV σ =
      (t.eval σ).map fun st => (σ.globG.withStorage st, σ.locV) := by
  show (UpdElem.storage t : UpdElem C Γ Γ).applyV σ σ.globG σ.locV = _
  rw [UpdElem.applyV_storage]

theorem applyV_memory1 (t : Tm C Γ .mem) :
    (Upd.nil.snoc (UpdElem.memory t)).applyV σ =
      (t.eval σ).map fun μ => (σ.globG.withMem μ, σ.locV) := by
  show (UpdElem.memory t : UpdElem C Γ Γ).applyV σ σ.globG σ.locV = _
  rw [UpdElem.applyV_memory]

theorem applyV_local1 {t : LTy} (i : Idx Γ t) (r : Rhs C Γ t) :
    (Upd.nil.snoc (UpdElem.local i r)).applyV σ =
      (r.eval σ).map fun v => (σ.globG, σ.locV.set i v) := by
  show (UpdElem.local i r : UpdElem C Γ Γ).applyV σ σ.globG σ.locV = _
  rw [UpdElem.applyV_local]

/-- `x++`'s bumped value, read in the state before. -/
theorem Tm.eval_bumped (o : IncDec) (hp : p.isNumeric = true) (a : Tm C Γ (.val p)) :
    (Tm.bumped o hp a).eval σ =
      (a.eval σ).bind fun x => if o.isPre then bumpT o p (PrimTy.key x) else some x := by
  unfold Tm.bumped
  cases o.isPre with
  | true => exact Tm.eval_bump σ o hp a
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; cases a.eval σ <;> rfl

theorem bumpLoc_agrees (o : IncDec) (hp : p.isNumeric = true) (L : Loc C Γ (.prim p)) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV))
      ((do bumpStoreT σ o (← L.resolveT σ)) >>= fun x => pure x.1)
      ((Upd.nil.snoc (.storage (.app3 .save (.app0 .storage) L.lower (.app1 .sval
        (Tm.castV (BinOp.compound_ret (IncDec.binOp_compound o) p)
          (.app2 (.binop o.binOp (BinOp.compound_accepts (IncDec.binOp_compound o) hp))
            (Val.read L).lower (Tm.one p hp))))))).applyP σ) := by
  rw [applyP_storage1, Tm.eval_save, Tm.eval_storage, Option.bind_some, Tm.eval_sval,
    Tm.eval_bump σ o hp]
  show TRes.AgreesO _ _ (((L.lower.eval σ).bind fun r =>
    ((((Tm.app2 .find (.app0 .storage) L.lower).eval σ).bind fun x =>
      bumpT o p (PrimTy.key x)).map SVal.prim).bind fun w => σ.storage.write r w).map _)
  rw [Tm.eval_find, Tm.eval_storage, Option.bind_some, bind_assoc]
  refine (Loc.lower_resolveT σ L).cases (fun ref href => ?_) (fun href => by rw [href]; rfl)
  rw [href]
  simp only [Option.bind_some, id, bumpStoreT, bind_assoc]
  cases hf : σ.storage.find ref with
  | none => rfl
  | some old =>
    simp only [Option.bind_some, TRes.ofOpt_some_bind]
    cases hc : bumpT o p (PrimTy.key (SVal.view old)) with
    | none => rfl
    | some new =>
      simp only [Option.map_some, Option.bind_some, TRes.ofOpt_some_bind]
      rw [Storage.write_prim]
      cases σ.storage.save ref (.prim new) <;> rfl

theorem bumpMem_agrees (o : IncDec) (hp : p.isNumeric = true) (L : MLoc C Γ (.prim p)) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV))
      ((do bumpMemT σ o (← L.addrT σ)) >>= fun x => pure x.1)
      ((Upd.nil.snoc (.memory (.app3 .write (.app0 .memory) L.lower (.app1 .mval
        (Tm.castV (BinOp.compound_ret (IncDec.binOp_compound o) p)
          (.app2 (.binop o.binOp (BinOp.compound_accepts (IncDec.binOp_compound o) hp))
            (Val.readMem L).lower (Tm.one p hp))))))).applyP σ) := by
  rw [applyP_memory1, Tm.eval_write, Tm.eval_memory, Option.bind_some, Tm.eval_mval,
    Tm.eval_bump σ o hp]
  show TRes.AgreesO _ _ (((L.lower.eval σ).bind fun ad =>
    ((((Tm.app2 .read (.app0 .memory) L.lower).eval σ).bind fun x =>
      bumpT o p (PrimTy.key x))).bind fun w => σ.glob.memT.writeT ad w).map _)
  rw [Tm.eval_read, Tm.eval_memory, Option.bind_some, bind_assoc]
  refine (MLoc.lower_addrT σ L).cases (fun a ha => ?_) (fun ha => by rw [ha]; rfl)
  rw [ha]
  simp only [Option.bind_some, bumpMemT, Grown.readT, State.memT, MAddr.resolve_toT,
    Option.bind_eq_bind, bind_assoc]
  change TRes.AgreesO _ _ ((((σ.heap.readAddr a).bind fun x => _).bind fun w =>
    Grown.writeT ⟨List.prefix_refl σ.H, σ.heap, ()⟩ a.toT w).map _)
  cases hf : σ.heap.readAddr a with
  | none => rfl
  | some old =>
    simp only [Option.bind_some, TRes.ofOpt_some_bind]
    cases hc : bumpT o p (PrimTy.key (p := p) old) with
    | none => rfl
    | some new =>
      simp only [Option.bind_some, TRes.ofOpt_some_bind]
      rw [Grown.writeT_toT_prim ⟨List.prefix_refl σ.H, σ.heap, ()⟩ a new]
      cases σ.heap.writeAddr a new <;> rfl

theorem incDec_agrees (o : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    TRes.AgreesO (fun x : Out C σ.H Γ => (x.st.glob, x.st.locV)) (TRun.incDec o l σ)
      ((Upd.nil.snoc (l.set (l.op o.binOp (IncDec.binOp_compound o) hp (Tm.one p hp)))).applyP σ) := by
  show TRes.AgreesO _ (l.bumpT σ o >>= fun x => pure x.1) _
  cases l with
  | «local» i =>
    rw [OpLoc.set, applyP_local1]
    show TRes.AgreesO _ _ (((Tm.castV _ (.app2 (.binop o.binOp _) (.pvV i) (Tm.one p hp))).eval
      σ).map _)
    rw [Tm.eval_bump σ o hp, Tm.eval_pvV]
    simp only [Option.bind_some, OpLoc.bumpT, bind_assoc]
    cases bumpT o p (PrimTy.key (TEnv.get i σ.env)) with
    | none => rfl
    | some new =>
      refine TRes.AgreesO.ret ?_
      rw [Option.map_some, State.locV_setLocal]
      rfl
  | root r h => exact bumpLoc_agrees σ o hp (.root r h)
  | field b f h => exact bumpLoc_agrees σ o hp (.field b f h)
  | index it b ie => exact bumpLoc_agrees σ o hp (.index it b (.simple ie))
  | mfield b f h => exact bumpMem_agrees σ o hp (.field b f h)
  | mindex a b ie => exact bumpMem_agrees σ o hp (.index a b (.simple ie))

theorem bumpAssignLoc_agrees (i : Idx Γ (.val p)) (o : IncDec) (hp : p.isNumeric = true)
    (L : Loc C Γ (.prim p)) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV))
      ((do bumpStoreT σ o (← L.resolveT σ)) >>= fun x =>
        pure (⟨x.1.st.setLocal i x.2, x.1.ext⟩ : Out C σ.H Γ))
      (((Upd.nil.snoc (.storage (.app3 .save (.app0 .storage) L.lower (.app1 .sval
        (Tm.castV (BinOp.compound_ret (IncDec.binOp_compound o) p)
          (.app2 (.binop o.binOp (BinOp.compound_accepts (IncDec.binOp_compound o) hp))
            (Val.read L).lower (Tm.one p hp))))))).snoc
        (.local i (.val (Tm.bumped o hp (Val.read L).lower)))).applyP σ) := by
  rw [applyP_snoc, applyV_storage1, Tm.eval_save, Tm.eval_storage, Option.bind_some, Tm.eval_sval,
    Tm.eval_bump σ o hp]
  simp only [UpdElem.applyV_local]
  show TRes.AgreesO _ _ ((((L.lower.eval σ).bind fun r =>
    ((((Tm.app2 .find (.app0 .storage) L.lower).eval σ).bind fun x =>
      bumpT o p (PrimTy.key x)).map SVal.prim).bind fun w => σ.storage.write r w).map _).bind
    fun q => (((Tm.bumped o hp (Tm.app2 .find (.app0 .storage) L.lower)).eval σ).map _).map _)
  rw [Tm.eval_bumped, Tm.eval_find, Tm.eval_storage, Option.bind_some, bind_assoc]
  refine (Loc.lower_resolveT σ L).cases (fun ref href => ?_) (fun href => by rw [href]; rfl)
  rw [href]
  simp only [Option.bind_some, id, bumpStoreT, bind_assoc]
  cases hf : σ.storage.find ref with
  | none => rfl
  | some old =>
    simp only [Option.bind_some, TRes.ofOpt_some_bind]
    cases hc : bumpT o p (PrimTy.key (SVal.view old)) with
    | none => rfl
    | some new =>
      simp only [Option.map_some, Option.bind_some, TRes.ofOpt_some_bind]
      rw [Storage.write_prim]
      cases σ.storage.save ref (.prim new) with
      | none => rfl
      | some st =>
        refine TRes.AgreesO.ret ?_
        cases o.isPre <;>
          simp only [Option.map_some, Option.bind_some, Bool.false_eq_true, ↓reduceIte,
            State.locV_setLocal] <;> rfl

theorem bumpAssignMem_agrees (i : Idx Γ (.val p)) (o : IncDec) (hp : p.isNumeric = true)
    (L : MLoc C Γ (.prim p)) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV))
      ((do bumpMemT σ o (← L.addrT σ)) >>= fun x =>
        pure (⟨x.1.st.setLocal i x.2, x.1.ext⟩ : Out C σ.H Γ))
      (((Upd.nil.snoc (.memory (.app3 .write (.app0 .memory) L.lower (.app1 .mval
        (Tm.castV (BinOp.compound_ret (IncDec.binOp_compound o) p)
          (.app2 (.binop o.binOp (BinOp.compound_accepts (IncDec.binOp_compound o) hp))
            (Val.readMem L).lower (Tm.one p hp))))))).snoc
        (.local i (.val (Tm.bumped o hp (Val.readMem L).lower)))).applyP σ) := by
  rw [applyP_snoc, applyV_memory1, Tm.eval_write, Tm.eval_memory, Option.bind_some, Tm.eval_mval,
    Tm.eval_bump σ o hp]
  simp only [UpdElem.applyV_local]
  show TRes.AgreesO _ _ ((((L.lower.eval σ).bind fun ad =>
    ((((Tm.app2 .read (.app0 .memory) L.lower).eval σ).bind fun x =>
      bumpT o p (PrimTy.key x))).bind fun w => σ.glob.memT.writeT ad w).map _).bind
    fun q => (((Tm.bumped o hp (Tm.app2 .read (.app0 .memory) L.lower)).eval σ).map _).map _)
  rw [Tm.eval_bumped, Tm.eval_read, Tm.eval_memory, Option.bind_some, bind_assoc]
  refine (MLoc.lower_addrT σ L).cases (fun a ha => ?_) (fun ha => by rw [ha]; rfl)
  rw [ha]
  simp only [Option.bind_some, bumpMemT, Grown.readT, State.memT, MAddr.resolve_toT,
    Option.bind_eq_bind, bind_assoc]
  change TRes.AgreesO _ _ (((((σ.heap.readAddr a).bind fun x => _).bind fun w =>
    Grown.writeT ⟨List.prefix_refl σ.H, σ.heap, ()⟩ a.toT w).map _).bind fun q =>
      (((σ.heap.readAddr a).bind fun x => _).map _).map _)
  cases hf : σ.heap.readAddr a with
  | none => rfl
  | some old =>
    simp only [Option.bind_some, TRes.ofOpt_some_bind]
    cases hc : bumpT o p (PrimTy.key (p := p) old) with
    | none => rfl
    | some new =>
      simp only [Option.bind_some, TRes.ofOpt_some_bind]
      rw [Grown.writeT_toT_prim ⟨List.prefix_refl σ.H, σ.heap, ()⟩ a new]
      cases σ.heap.writeAddr a new with
      | none => rfl
      | some h' =>
        refine TRes.AgreesO.ret ?_
        cases o.isPre <;>
          simp only [Option.map_some, Option.bind_some, Bool.false_eq_true, ↓reduceIte,
            State.locV_setLocal] <;> rfl

theorem assignIncDec_agrees (i : Idx Γ (.val p)) (o : IncDec) (hp : p.isNumeric = true)
    (l : OpLoc C Γ p) :
    TRes.AgreesO (fun x : Out C σ.H Γ => (x.st.glob, x.st.locV)) (TRun.assignIncDec i o l σ)
      (((Upd.nil.snoc (l.set (l.op o.binOp (IncDec.binOp_compound o) hp (Tm.one p hp)))).snoc
        (.local i (.val (Tm.bumped o hp l.cur)))).applyP σ) := by
  show TRes.AgreesO _ (l.bumpT σ o >>= fun x =>
    pure (⟨x.1.st.setLocal i x.2, x.1.ext⟩ : Out C σ.H Γ)) _
  cases l with
  | «local» j =>
    rw [applyP_snoc, OpLoc.set, applyV_local1]
    simp only [UpdElem.applyV_local]
    show TRes.AgreesO _ _ ((((Tm.castV _ (.app2 (.binop o.binOp _) (.pvV j) (Tm.one p hp))).eval
      σ).map _).bind fun q => (((Tm.bumped o hp (.pvV j)).eval σ).map _).map _)
    rw [Tm.eval_bump σ o hp, Tm.eval_bumped, Tm.eval_pvV]
    simp only [Option.bind_some, OpLoc.bumpT, bind_assoc]
    cases hc : bumpT o p (PrimTy.key (TEnv.get j σ.env)) with
    | none => rfl
    | some new =>
      refine TRes.AgreesO.ret ?_
      cases o.isPre <;>
        simp only [Option.map_some, Option.bind_some, Bool.false_eq_true, ↓reduceIte,
          State.locV_setLocal] <;> rfl
  | root r h => exact bumpAssignLoc_agrees σ i o hp (.root r h)
  | field b f h => exact bumpAssignLoc_agrees σ i o hp (.field b f h)
  | index it b ie => exact bumpAssignLoc_agrees σ i o hp (.index it b (.simple ie))
  | mfield b f h => exact bumpAssignMem_agrees σ i o hp (.field b f h)
  | mindex a b ie => exact bumpAssignMem_agrees σ i o hp (.index a b (.simple ie))

end OpLoc

/-! ## The update arms -/

section Arms

variable {Γ : Ctx} {m : Modality} (σ : State C Γ)

/-- `localValueAssign`, the reads, `binopAssignment`, `unopAssignment`, the
length reads: `{v := e}` for `v = e;`. -/
theorem sound_setLocal {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) :
    Premise.Runs m (.assignLocal i v) (.setLocal i v) σ :=
  Premise.sound_update_typed σ (setLocal_agrees σ i v) fun _ =>
    ((Val.evalT_ends σ v).bind fun _ => TRes.Ends.ok _).1

/-- `storageRootWriteStore`, `storageFieldWriteSave`, `storageIndexWrite*Save`,
`…CopySource`: `{storage := save(storage, l, src)}`. -/
theorem sound_save {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    Premise.Runs m (.assign l r) (.save l r) σ :=
  Premise.sound_update_typed (s := .assign l r) σ (save_agrees σ l r) fun _ =>
    ((Src.valueT_ends σ r).bind fun _ => (Loc.resolveT_ends σ l).bind fun _ =>
      (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _).1

/-- `memoryToStorage*CopyRoot`: `{storage := save(storage, l, copyMem(memory, p))}`. -/
theorem sound_saveMem {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
    Premise.Runs m (.assignFromMem l p) (.saveMem l p) σ :=
  Premise.sound_update_typed (s := .assignFromMem l p) σ (saveMem_agrees σ l p) fun _ =>
    ((MPath.mvalT_ends σ p).bind fun _ => (Loc.resolveT_ends σ l).bind fun _ =>
      (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _).1

/-- `storageRootDelete`, `storageFieldDelete`, `storageIndexDelete`,
`storageIndexArrayDelete`: `{storage := delAt(storage, l)}`. -/
theorem sound_delAt {T : Ty} (l : Loc C Γ T) : Premise.Runs m (.delete l) (.delAt l) σ :=
  Premise.sound_update_typed σ (delAt_agrees σ l) fun _ =>
    ((Loc.resolveT_ends σ l).bind fun _ => (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _).1

/-- `memoryFieldWrite`, `memoryIndexWriteArray`, `memoryFieldWriteCopy`,
`memoryIndexWriteCopy`: `{memory := write(memory, l, src)}`. -/
theorem sound_writeMem {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) :
    Premise.Runs m (.assignMem l r) (.writeMem l r) σ :=
  Premise.sound_update_typed σ (writeMem_agrees σ l r) fun _ =>
    ((MSrc.mvalT_ends σ r).bind fun _ => (MLoc.addrT_ends σ l).bind fun _ =>
      (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _).1

/-- `storageLocalRootRebind`, `…BindLocalRoot`: `{lsv := p}`. -/
theorem sound_rebindPath {R : RefTy} (i : Idx Γ (.alias R)) (p : SPath C Γ (.ref R)) :
    Premise.Runs m (.rebind i (.path p)) (.upd1 (UpdElem.rebind i p)) σ :=
  Premise.sound_update_typed σ (rebindPath_agrees σ i p) fun _ =>
    (((SPath.resolveT_ends σ p).bind fun _ => TRes.Ends.ok _).bind fun _ => TRes.Ends.ok _).1

/-- `memoryRootRebind`, `memoryFieldReadAliasRoot`, `memoryIndexReadArrayMemory`:
`{mv := p}`. -/
theorem sound_rebindMemAlias {R : RefTy} (i : Idx Γ (.mem R)) (p : MPath C Γ (.ref R)) :
    Premise.Runs m (.rebindMem i (.alias p)) (.upd1 (UpdElem.rebindMem i p)) σ :=
  Premise.sound_update_typed σ (rebindMemAlias_agrees σ i p) fun _ =>
    ((MRhs.evalT_ends σ (.alias p)).bind fun _ => TRes.Ends.ok _).1

/-- `localOpAssign`, `storage*OpAssign`, `memory*OpAssign`: `{l := l ⊕ se}`. -/
theorem sound_opAssign {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (se : Simple C Γ p) :
    Premise.Runs m (.opAssign op hop hp l (.simple se)) (.upd1 (l.set (l.op op hop hp se.lower))) σ :=
  Premise.sound_update_typed σ (opAssign_agrees σ hop hp l se) (fun _ =>
    (TRes.Ends.bind (TRes.Ends.ok _) fun _ => OpLoc.storeT_ends σ op l _).1)

/-- `localIncrement`, `storage*Increment`, `memory*Increment`: `{l := l ± 1}`. -/
theorem sound_incDec {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    Premise.Runs m (.incDec op hp l)
      (.upd1 (l.set (l.op op.binOp (IncDec.binOp_compound op) hp (Tm.one p hp)))) σ :=
  Premise.sound_update_typed σ (incDec_agrees σ op hp l) (fun _ =>
    ((OpLoc.bumpT_ends σ op l).bind fun _ => TRes.Ends.ok _).1)

/-- `localAssignIncrement`, `…IncrementAssignment`:
`{l := l ± 1 ‖ v := bumped(l)}`. -/
theorem sound_assignIncDec {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (hs : l.recvSimple = true) :
    Premise.Runs m (.assignIncDec i op hp l hs) (assignIncStep i op hp l) σ :=
  Premise.sound_update_typed σ (assignIncDec_agrees σ i op hp l) (fun _ =>
    ((OpLoc.bumpT_ends σ op l).bind fun _ => TRes.Ends.ok _).1)

end Arms

/-! ## The other update arms (`Step.lean`): the agreements -/

section Agrees2

variable {Γ : Ctx} (σ : State C Γ)

theorem Storage.pushPlace_fst {E : Ty} (st : Storage C) (r : SRef C (.ref (.array E))) :
    (st.pushPlace r).map (·.1) = st.push r some := by
  unfold Storage.pushPlace Storage.push
  cases st.find r with
  | none => rfl
  | some v =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    split
    · cases st.save r _ <;> rfl
    · rfl

/-- A push as a place returns the slot past the live elements found. -/
theorem Storage.pushPlace_some {E : Ty} {st st' : Storage C} {r : SRef C (.ref (.array E))}
    {n : PrimTy.uint.Denote} (h : st.pushPlace r = some (st', n)) :
    ∃ v, st.find r = some v ∧
      n = lenU (SVal.view v : ArrView E).n (SVal.view v : ArrView E).hn := by
  unfold Storage.pushPlace at h
  cases hf : st.find r with
  | none => rw [hf] at h; cases h
  | some v =>
    refine ⟨v, rfl, ?_⟩
    rw [hf] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · cases hs : st.save r _ with
      | none => rw [hs] at h; cases h
      | some s' =>
        rw [hs] at h
        cases h
        rfl
    · cases h

theorem pushSlot_agrees {E : Ty} (b : SPath C Γ (.array E)) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV)) (TRun.push b none σ)
      ((Upd.nil.snoc (UpdElem.pushSlot b)).applyP σ) := by
  rw [UpdElem.pushSlot, applyP_storage1, Tm.eval_pushSlot, Tm.eval_storage, Option.bind_some]
  refine (SPath.lower_resolveT σ b).cases (fun ref href => ?_) (fun href => by rw [href]; rfl)
  rw [href]
  show TRes.AgreesO _ (if σ.storage.full ref then .error .exhausted else
    TRes.ofOpt (σ.storage.push ref some) >>= fun st =>
      pure (⟨σ.withStorage st, List.prefix_refl _⟩ : Out C σ.H Γ)) ((σ.storage.push ref some).map _)
  split
  · trivial
  · cases σ.storage.push ref some <;> rfl

theorem extend_agrees {E : Ty} (b : SPath C Γ (.array E)) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV)) (TRun.push b none σ)
      ((Upd.nil.snoc (UpdElem.extend b)).applyP σ) := by
  have h := pushSlot_agrees σ b
  rw [UpdElem.pushSlot, applyP_storage1, Tm.eval_pushSlot, Tm.eval_storage, Option.bind_some] at h
  rw [UpdElem.extend, applyP_storage1, Tm.eval_extend, Tm.eval_storage, Option.bind_some]
  simp only [Storage.pushPlace_fst]
  exact h

theorem pushSome_agrees {E : Ty} (b : SPath C Γ (.array E)) (v : Src C Γ E) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV)) (TRun.push b (some v) σ)
      ((Upd.nil.snoc (UpdElem.push b v)).applyP σ) := by
  rw [UpdElem.push, applyP_storage1, Tm.eval_push, Tm.eval_storage, Option.bind_some]
  refine (SPath.lower_resolveT σ b).cases (fun ref href => ?_) (fun href => by rw [href]; rfl)
  rw [href]
  simp only [Option.bind_some, id]
  refine (Src.lower_valueT σ v).cases (fun sv hsv => ?_) (fun hsv => ?_)
  · rw [hsv]
    show TRes.AgreesO _ (if σ.storage.full ref then .error .exhausted else
      TRes.ofOpt (σ.storage.push ref fun _ => some sv.strip) >>= fun st =>
        pure (⟨σ.withStorage st, List.prefix_refl _⟩ : Out C σ.H Γ))
      ((σ.storage.push ref fun _ => some sv.strip).map _)
    split
    · trivial
    · cases σ.storage.push ref fun _ => some sv.strip <;> rfl
  · rw [hsv]
    show (σ.storage.push ref fun _ => none).map _ = none
    rw [Storage.push_none]
    rfl

theorem pop_agrees {E : Ty} (b : SPath C Γ (.array E)) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV)) (TRun.pop b σ)
      ((Upd.nil.snoc (if b.elemMapping then UpdElem.shrink b else UpdElem.pop b)).applyP σ) := by
  have e : (Upd.nil.snoc (if b.elemMapping then UpdElem.shrink b else UpdElem.pop b)).applyP σ =
      ((b.lower.eval σ).bind fun r => σ.storage.pop E.isMapping r).map
        fun st => ((σ.withStorage st).glob, σ.locV) := by
    show (Upd.nil.snoc (if E.isMapping then UpdElem.shrink b else UpdElem.pop b)).applyP σ = _
    cases E.isMapping with
    | true =>
      simp only [↓reduceIte, UpdElem.shrink, applyP_storage1, Tm.eval_shrink, Tm.eval_storage,
        Option.bind_some]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, UpdElem.pop, applyP_storage1, Tm.eval_pop,
        Tm.eval_storage, Option.bind_some]
  rw [e]
  refine (SPath.lower_resolveT σ b).cases (fun ref href => ?_) (fun href => by rw [href]; rfl)
  rw [href]
  show TRes.AgreesO _ (TRes.ofOpt (σ.storage.pop E.isMapping ref) >>= _)
    ((σ.storage.pop E.isMapping ref).map _)
  cases σ.storage.pop E.isMapping ref <;> rfl

theorem rebindPush_agrees {R : RefTy} (i : Idx Γ (.alias R)) (b : SPath C Γ (.array (.ref R)))
    (hd : (Ty.ref R).defaultOkS = true) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV)) (TRun.rebind i (.push b hd) σ)
      ((Upd.pushBind i b).applyP σ) := by
  rw [Upd.pushBind, applyP_snoc, applyV_storage1, Tm.eval_extend, Tm.eval_storage, Option.bind_some]
  simp only [UpdElem.applyV_local]
  show TRes.AgreesO _ _ ((((b.lower.eval σ).bind fun r => (σ.storage.pushPlace r).map (·.1)).map
    _).bind fun q => ((((Tm.app1 .next b.lower).eval σ).bind fun r => some (some r)).map _).map _)
  rw [Tm.eval_next]
  show TRes.AgreesO _ ((do
      let ref ← b.resolveT σ
      if σ.storage.full ref then .error .exhausted else do
      let (st, n) ← TRes.ofOpt (σ.storage.pushPlace ref)
      pure (st, ref.index (.arr .dyn) n)) >>= fun x =>
        pure (⟨(σ.withStorage x.1).setLocal i (some x.2), List.prefix_refl _⟩ : Out C σ.H Γ)) _
  rw [bind_assoc]
  refine (SPath.lower_resolveT σ b).cases (fun ref href => ?_) (fun href => by rw [href]; rfl)
  rw [href]
  simp only [Option.bind_some, id]
  split
  · trivial
  · cases hp : σ.storage.pushPlace ref with
    | none => rfl
    | some q =>
      obtain ⟨st', n⟩ := q
      obtain ⟨v, hv, rfl⟩ := Storage.pushPlace_some hp
      refine TRes.AgreesO.ret ?_
      simp only [Option.map_some, Option.bind_some, Storage.nextT, hv, State.locV_setLocal]
      rfl

/-! ### A push's update is out of gas where the run is -/

theorem TRes.AgreesO.eq_ok {α : Type} {t : TRes α} {u : Option α} {a : α}
    (h : TRes.AgreesO id t u) (he : t.Ends) (hu : u = some a) : t = .ok a := by
  subst hu
  match t, h with
  | .ok _, h => cases h; rfl
  | .error .revert, h => cases h
  | .error .panic, h => exact h.elim
  | .error .diverge, _ => exact absurd rfl he.1
  | .error .exhausted, _ => exact absurd rfl he.2

/-- The array a push reads, where its update says it is full: the run is
out of gas there. -/
theorem push_exhausted {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E))
    {ref : SRef C (.ref (.array E))} (hq : b.lower.eval σ = some ref)
    (hv : ∀ r, v = some r → (r.lower.eval σ).isSome) (hf : σ.storage.full ref = true) :
    TRun.push b v σ = .error .exhausted := by
  have hr := (SPath.lower_resolveT σ b).eq_ok (SPath.resolveT_ends σ b) hq
  unfold TRun.push
  rw [hr]
  cases v with
  | none => exact if_pos hf
  | some r =>
    obtain ⟨sv, hsv⟩ := Option.isSome_iff_exists.1 (hv r rfl)
    have hval := (Src.lower_valueT σ r).eq_ok (Src.valueT_ends σ r) hsv
    dsimp only
    rw [hval]
    exact if_pos hf

theorem pushSlot_exh {E : Ty} (b : SPath C Γ (.array E))
    (h : TRun.push b none σ = .error .revert) :
    (Upd.nil.snoc (UpdElem.pushSlot b)).exh σ = false := by
  refine Upd.exh_of_exhAny ?_
  show (false || (Tm.app2 .pushSlot (.app0 .storage) b.lower).exhB σ) = false
  rw [Tm.exhB_app2_pushFree σ _ _ _ rfl (SPath.lower_pushFree b)]
  show (false || Op2.exhB .pushSlot (some σ.storage) (b.lower.eval σ)) = false
  cases hq : b.lower.eval σ with
  | none => rfl
  | some ref =>
    cases hf : σ.storage.full ref with
    | false => show (false || σ.storage.full ref) = false; rw [hf]; rfl
    | true => rw [push_exhausted σ b none hq nofun hf] at h; cases h

theorem extend_exh {E : Ty} (b : SPath C Γ (.array E))
    (h : TRun.push b none σ = .error .revert) :
    (Upd.nil.snoc (UpdElem.extend b)).exh σ = false := by
  refine Upd.exh_of_exhAny ?_
  show (false || (Tm.app2 .extend (.app0 .storage) b.lower).exhB σ) = false
  rw [Tm.exhB_app2_pushFree σ _ _ _ rfl (SPath.lower_pushFree b)]
  show (false || Op2.exhB .extend (some σ.storage) (b.lower.eval σ)) = false
  cases hq : b.lower.eval σ with
  | none => rfl
  | some ref =>
    cases hf : σ.storage.full ref with
    | false => show (false || σ.storage.full ref) = false; rw [hf]; rfl
    | true => rw [push_exhausted σ b none hq nofun hf] at h; cases h

theorem pushSome_exh {E : Ty} (b : SPath C Γ (.array E)) (r : Src C Γ E)
    (h : TRun.push b (some r) σ = .error .revert) :
    (Upd.nil.snoc (UpdElem.push b r)).exh σ = false := by
  refine Upd.exh_of_exhAny ?_
  show (false || (Tm.app3 .push (.app0 .storage) b.lower r.lower).exhB σ) = false
  rw [Tm.exhB_app3_pushFree σ _ _ _ _ rfl (SPath.lower_pushFree b) (Src.lower_pushFree r)]
  show (false || Op3.exhB .push (some σ.storage) (b.lower.eval σ) (r.lower.eval σ)) = false
  cases hq : b.lower.eval σ with
  | none => rfl
  | some ref =>
    cases hv : r.lower.eval σ with
    | none => rfl
    | some sv =>
      cases hf : σ.storage.full ref with
      | false => show (false || σ.storage.full ref) = false; rw [hf]; rfl
      | true =>
        rw [push_exhausted σ b (some r) hq (fun r' hr => by cases hr; rw [hv]; rfl) hf] at h
        cases h

theorem pushBind_exh {R : RefTy} (i : Idx Γ (.alias R)) (b : SPath C Γ (.array (.ref R)))
    (hd : (Ty.ref R).defaultOkS = true) (h : TRun.rebind i (.push b hd) σ = .error .revert) :
    (Upd.pushBind i b).exh σ = false := by
  refine Upd.exh_of_exhAny ?_
  show ((false || (Tm.app2 .extend (.app0 .storage) b.lower).exhB σ) ||
    (Rhs.path (Tm.app1 .next b.lower)).exhB σ) = false
  rw [Tm.exhB_app2_pushFree σ _ _ _ rfl (SPath.lower_pushFree b),
    Rhs.exhB_of_pushFree σ _ (by simp only [Rhs.pushFree, Tm.pushFree, SPath.lower_pushFree])]
  show ((false || Op2.exhB .extend (some σ.storage) (b.lower.eval σ)) || false) = false
  cases hq : b.lower.eval σ with
  | none => rfl
  | some ref =>
    cases hf : σ.storage.full ref with
    | false => show ((false || σ.storage.full ref) || false) = false; rw [hf]; rfl
    | true =>
      have hr := (SPath.lower_resolveT σ b).eq_ok (SPath.resolveT_ends σ b) hq
      have ha : ARhs.evalT σ (.push b hd) = .error .exhausted := by
        simp only [ARhs.evalT, hr]
        exact if_pos hf
      have hx : TRun.rebind i (.push b hd) σ = .error .exhausted := by
        show (ARhs.evalT σ (.push b hd) >>= _) = _
        rw [ha]
        rfl
      rw [hx] at h
      cases h

theorem applyV_pay {Δ : Ctx} (r a : Tm C Γ (.val .uint)) (g : GlobT C σ.H) (ℓ : LocsV C Δ) :
    (UpdElem.pay r a : UpdElem C Γ Δ).applyV σ g ℓ =
      (r.eval σ).bind fun addr => (a.eval σ).map fun amt =>
        (g.withNet (if addr.1 = σ.tx.selfAddress.1 then g.1.net
          else setBy addr ((lookupBy addr g.1.net).getD 0 - amt.1) g.1.net), ℓ) := by
  rw [UpdElem.applyV_eq_applyVM]
  show ((UpdElem.pay r a : UpdElem C Γ Δ).globT σ g).bind _ = _
  rw [UpdElem.globT_eq_globTM]
  show (((r.eval σ).bind fun addr => (a.eval σ).bind fun amt => some _).bind _) = _
  cases r.eval σ with
  | none => rfl
  | some x => cases a.eval σ <;> rfl

theorem transferBox_agrees (sadr se : Simple C Γ .uint) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV))
      (TRun.transfer (.simple sadr) (.simple se) σ) ((Upd.nil.snoc (UpdElem.payTo sadr se)).applyP σ) := by
  rw [UpdElem.payTo, applyP_snoc, applyV_nil, Option.bind_some, applyV_pay, Simple.lower_evalT,
    Simple.lower_evalT]
  rfl

/-- `pv = a.send(v);`'s outcome, by the updates of `sendNoCallback*`. -/
theorem send_sim (pv : Idx Γ (.val .bool)) (sadr se : Simple C Γ .uint) :
    ∃ U ∈ [(Upd.nil.snoc (UpdElem.payTo sadr se)).snoc (.local pv (.val (Tm.lit (p := .bool) true))),
        Upd.nil.snoc (.local pv (.val (Tm.lit (p := .bool) false)))],
      U.applyP σ = some ((sendT σ pv (sadr.evalT σ) (se.evalT σ)).st.glob,
          (sendT σ pv (sadr.evalT σ) (se.evalT σ)).st.locV) := by
  have e₁ : ((Upd.nil.snoc (UpdElem.payTo sadr se)).snoc
      (.local pv (.val (Tm.lit (p := .bool) true)))).applyP σ =
        some (((σ.pay (sadr.evalT σ) (se.evalT σ).1).setLocal pv (true : Bool)).glob,
          ((σ.pay (sadr.evalT σ) (se.evalT σ).1).setLocal pv (true : Bool)).locV) := by
    rw [applyP_snoc, UpdElem.payTo]
    show ((((UpdElem.pay sadr.lower se.lower : UpdElem C Γ Γ).applyV σ σ.globG σ.locV)).bind _) = _
    rw [applyV_pay, Simple.lower_evalT, Simple.lower_evalT, State.locV_setLocal]
    rfl
  have e₂ : (Upd.nil.snoc (.local pv (.val (Tm.lit (C := C) (Γ := Γ) (p := .bool) false)))).applyP
      σ = some ((σ.setLocal pv (false : Bool)).glob, (σ.setLocal pv (false : Bool)).locV) := by
    rw [applyP_local1, State.locV_setLocal]; rfl
  unfold sendT
  split
  · exact ⟨_, List.mem_cons_self .., e₁⟩
  · exact ⟨_, List.mem_cons_self .., e₁⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), e₂⟩

end Agrees2

/-! ### Allocations -/

section Alloc

variable {Γ : Ctx} (σ : State C Γ)

theorem LTy.VDen.ofT_wk {H H' : HTy} (e : H <+: H') :
    (t : LTy) → (v : t.TDenote C H) → LTy.VDen.ofT t (LTy.TDenote.wk e t v) = LTy.VDen.ofT t v
  | .val _, _ | .alias _, _ | .mem _, none | .mem _, some _ | .old, _ | .oldNet, _
  | .kint, _ => rfl

/-- An adopted heap leaves the locals' values as they were. -/
theorem State.locV_adopt {α : HTy → Type} (g : Grown σ.H α) : (σ.adopt g).1.locV = σ.locV := by
  funext t i
  show LTy.VDen.ofT t (TEnv.get i (TEnv.wk g.ext Γ σ.env)) = _
  rw [TEnv.get_wk, LTy.VDen.ofT_wk]
  rfl

theorem applyV_decl1 {t : LTy} (x : Var) (r : Rhs C Γ t) :
    (Upd.nil.decl x r).applyV σ = (r.eval σ).map fun v => (σ.globG, σ.locV.push v) := by
  show (r.eval σ).bind _ = _
  cases r.eval σ <;> rfl

theorem Tm.eval_alloc (R : RefTy) (h : (Ty.ref R).mapFree = true) :
    (Tm.app1 (.alloc R h) (.app0 .memory) : Tm C Γ (.ident R)).eval σ =
      some ((σ.heap.allocDefault R h).val : HRef _ R).id := rfl

theorem Tm.eval_addM (R : RefTy) (h : (Ty.ref R).mapFree = true) :
    (Tm.app1 (.addM R h) (.app0 .memory) : Tm C Γ .mem).eval σ =
      some (σ.glob.memT.then (σ.heap.allocDefault R h)) := rfl

theorem declMemFresh_agrees (R : RefTy) (x : Var) (hm : (Ty.ref R).mapFree = true) :
    TRes.AgreesO (fun o : Out C σ.H (.mem R :: Γ) => (o.st.glob, o.st.locV))
      (TRun.declMem R none hm σ)
      (((Upd.nil.decl x (.mref (.app1 (.alloc R hm) (.app0 .memory)))).snoc
        (.memory (.app1 (.addM R hm) (.app0 .memory)))).applyP σ) := by
  rw [applyP_snoc, applyV_decl1]
  simp only [UpdElem.applyV_memory]
  refine congrArg some (Prod.ext rfl ?_)
  show σ.locV.push _ = ((σ.adopt (σ.heap.allocDefault R hm)).1.push (t := .mem R) (some _)).locV
  rw [State.locV_push, State.locV_adopt]
  rfl

theorem allocFresh_agrees {R : RefTy} (i : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV)) (TRun.deleteMem (.var i hm) σ)
      ((Upd.allocFresh i hm).applyP σ) := by
  rw [Upd.allocFresh, applyP_snoc, applyV_local1]
  simp only [UpdElem.applyV_memory]
  refine congrArg some (Prod.ext rfl ?_)
  show σ.locV.set i _ = ((σ.adopt (σ.heap.allocDefault R hm)).1.setLocal i (some _)).locV
  rw [State.locV_setLocal, State.locV_adopt]
  rfl

theorem Tm.eval_copy {R : RefTy} (h : (Ty.ref R).mapFree = true) (v : Tm C Γ (.sv (.ref R))) :
    (Tm.app2 (.copy h) (.app0 .memory) v).eval σ =
      (v.eval σ).map fun sv => ((sv.copyStToM σ.heap h).val : HRef _ R).id := by
  rw [Tm.eval_app2, Op2.eval_eq_evalM]
  show (v.eval σ).bind _ = _
  cases v.eval σ <;> rfl

theorem Tm.eval_copySt {R : RefTy} (h : (Ty.ref R).mapFree = true) (v : Tm C Γ (.sv (.ref R))) :
    (Tm.app2 (.copySt h) (.app0 .memory) v).eval σ =
      (v.eval σ).map fun sv => σ.glob.memT.then (sv.copyStToM σ.heap h) := by
  rw [Tm.eval_app2, Op2.eval_eq_evalM]
  show (v.eval σ).bind _ = _
  cases v.eval σ <;> rfl

/-- `{mv := freshId(copySt(memory, v)) ‖ memory := copySt(memory, v)}`, where
`v` reads `sv`: the copy adopted, `mv` naming it. -/
theorem allocCopy_applyP {R : RefTy} (i : Idx Γ (.mem R)) (h : (Ty.ref R).mapFree = true)
    (v : Tm C Γ (.sv (.ref R))) {sv : SVal (.ref R)} (hv : v.eval σ = some sv) :
    (Upd.allocCopy i h v).applyP σ =
      some (((σ.copyStToMG sv h).st.setLocal i (some (σ.copyStToMG sv h).val)).glob,
        ((σ.copyStToMG sv h).st.setLocal i (some (σ.copyStToMG sv h).val)).locV) := by
  rw [Upd.allocCopy, applyP_snoc, applyV_local1]
  simp only [UpdElem.applyV_memory]
  show (((((Tm.app2 (.copy h) (.app0 .memory) v).eval σ).bind fun id => some (some id)).map
    _).bind fun q => (((Tm.app2 (.copySt h) (.app0 .memory) v).eval σ).map _).map _) = _
  rw [Tm.eval_copy, Tm.eval_copySt, hv]
  refine congrArg some (Prod.ext rfl ?_)
  show σ.locV.set i _ = ((σ.adopt (sv.copyStToM σ.heap h)).1.setLocal i (some _)).locV
  rw [State.locV_setLocal, State.locV_adopt]
  rfl

theorem allocCopy_applyP_none {R : RefTy} (i : Idx Γ (.mem R)) (h : (Ty.ref R).mapFree = true)
    (v : Tm C Γ (.sv (.ref R))) (hv : v.eval σ = none) : (Upd.allocCopy i h v).applyP σ = none := by
  rw [Upd.allocCopy, applyP_snoc, applyV_local1]
  show (((((Tm.app2 (.copy h) (.app0 .memory) v).eval σ).bind fun id => some (some id)).map
    _).bind _) = _
  rw [Tm.eval_copy, hv]
  rfl

/-- `memoryStorageCopy`: a deep copy of `sfind(storage, p)`. -/
theorem allocCopy_copy_agrees {R : RefTy} (i : Idx Γ (.mem R)) (p : SPath C Γ (.ref R))
    (hm : (Ty.ref R).mapFree = true) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV)) (TRun.rebindMem i (.copy p hm) σ)
      ((Upd.allocCopy i hm (.app2 .sfind (.app0 .storage) p.lower)).applyP σ) := by
  show TRes.AgreesO _ ((do
      let r ← p.resolveT σ
      let sv ← TRes.ofOpt (σ.storage.find r)
      let g := σ.copyStToMG sv hm
      pure (⟨g.st, g.ext, g.val⟩ : Grew C Γ σ.H (HRef · R))) >>= fun g =>
        pure (⟨g.st.setLocal i (some g.val), g.ext⟩ : Out C σ.H Γ)) _
  rw [bind_assoc]
  refine (SPath.lower_resolveT σ p).cases (fun ref href => ?_) (fun href => ?_)
  · cases hf : σ.storage.find ref with
    | none =>
      exact allocCopy_applyP_none σ i hm _ (by rw [Tm.eval_sfind, Tm.eval_storage, href]; exact hf)
    | some sv =>
      exact allocCopy_applyP σ i hm _ (by rw [Tm.eval_sfind, Tm.eval_storage, href]; exact hf)
  · exact allocCopy_applyP_none σ i hm _ (by rw [Tm.eval_sfind, Tm.eval_storage, href]; rfl)

/-- `memoryArrayFreshAlloc`: `newArr(R, n)` copied. -/
theorem allocCopy_newArr_agrees {R : RefTy} (i : Idx Γ (.mem R)) (n : Simple C Γ .uint)
    (h : R.newArrOk = true) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV)) (TRun.rebindMem i (.newArr n h) σ)
      ((Upd.allocCopy i (RefTy.mapFree_of_newArrOk h) (.app1 (.newArr h) n.lower)).applyP σ) := by
  rw [allocCopy_applyP σ i _ _ (sv := newArrT R (n.evalT σ) h)
    (by rw [Tm.eval_app1, Op1.eval_eq_evalM]; show (n.lower.eval σ).map _ = _
        rw [Simple.lower_evalT]; rfl)]
  rfl

theorem MAddr.toT_wk {H H' : HTy} (e : H <+: H') {T : Ty} (a : MAddr H T) :
    (a.wk e).toT = a.toT := by
  cases a <;> rfl

theorem clearPrim_agrees {p : PrimTy} (l : MLoc C Γ (.prim p)) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV)) (TRun.deleteMem (.loc l) σ)
      ((Upd.nil.snoc (UpdElem.clearMem (.prim p) l.lower l.mapFree)).applyP σ) := by
  rw [UpdElem.clearMem, applyP_memory1, Tm.eval_write, Tm.eval_memory, Option.bind_some,
    Tm.eval_mval, Tm.eval_lit]
  refine (MLoc.lower_addrT σ l).cases (fun a ha => ?_) (fun ha => by rw [ha]; rfl)
  rw [ha]
  simp only [Option.bind_some]
  rw [Grown.writeT_toT_prim σ.glob.memT a (PrimTy.dflt p)]
  show TRes.AgreesO _ (TRes.ofOpt (σ.heap.writeAddr a (PrimTy.dflt p)) >>= _)
    (((σ.heap.writeAddr a (PrimTy.dflt p)).map _).map _)
  cases σ.heap.writeAddr a (PrimTy.dflt p) <;> rfl

theorem clearRef_agrees {R : RefTy} (l : MLoc C Γ (.ref R)) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV)) (TRun.deleteMem (.loc l) σ)
      ((Upd.nil.snoc (UpdElem.clearMem (.ref R) l.lower l.mapFree)).applyP σ) := by
  rw [UpdElem.clearMem, applyP_memory1, Tm.eval_write, Tm.eval_addM, Option.bind_some, Tm.eval_ref,
    Tm.eval_alloc]
  refine (MLoc.lower_addrT σ l).cases (fun a ha => ?_) (fun ha => by rw [ha]; rfl)
  rw [ha]
  simp only [Option.bind_some]
  have hw := Grown.writeT_toT (σ.glob.memT.then (σ.heap.allocDefault R l.mapFree))
    (a.wk (σ.heap.allocDefault R l.mapFree).ext) (T := .ref R)
    (σ.heap.allocDefault R l.mapFree).val
  rw [MAddr.toT_wk] at hw
  rw [show ((σ.heap.allocDefault R l.mapFree).val : HRef _ R).id =
    MVal.toT (.ref R) (σ.heap.allocDefault R l.mapFree).val from rfl, hw]
  show TRes.AgreesO _ (TRun.clearT σ a l.mapFree)
    ((((σ.adopt (σ.heap.allocDefault R l.mapFree)).1.heap.writeAddr
      (a.wk (σ.heap.allocDefault R l.mapFree).ext) (σ.heap.allocDefault R l.mapFree).val).map _).map _)
  simp only [TRun.clearT, State.allocDefaultG, State.grow]
  split
  · rename_i hp heq
    rw [heq]
    refine congrArg some (Prod.ext rfl ?_)
    show σ.locV = ((σ.adopt (σ.heap.allocDefault R l.mapFree)).1.withHeap hp).locV
    exact (State.locV_adopt σ _).symm
  · rename_i heq
    rw [heq]
    rfl

end Alloc

/-! ## The other update arms (`Step.lean`) -/

section Arms2

variable {Γ : Ctx} {m : Modality} (σ : State C Γ)

/-- `storagePushLengthSave`: `{storage := pushSlot(storage, b)}`. -/
theorem sound_pushSlot {E : Ty} (b : SPath C Γ (.array E))
    (hd : (none.isSome || E.defaultOkS) = true) :
    Premise.Runs m (.push b none hd) (.upd1 (UpdElem.pushSlot b)) σ :=
  Premise.sound_update_typed σ (pushSlot_agrees σ b) (fun _ => TRun.push_nd σ b none)
    (hx := pushSlot_exh σ b)

/-- `storagePushLengthSaveReferenceElement`: `{storage := extend(storage, b)}`. -/
theorem sound_extend {E : Ty} (b : SPath C Γ (.array E))
    (hd : (none.isSome || E.defaultOkS) = true) :
    Premise.Runs m (.push b none hd) (.upd1 (UpdElem.extend b)) σ :=
  Premise.sound_update_typed σ (extend_agrees σ b) (fun _ => TRun.push_nd σ b none)
    (hx := extend_exh σ b)

/-- `storagePushValueSave`, `storagePushValueCopySource`:
`{storage := push(storage, b, src)}`. -/
theorem sound_pushSome {E : Ty} (b : SPath C Γ (.array E)) (r : Src C Γ E)
    (hd : ((some r).isSome || E.defaultOkS) = true) :
    Premise.Runs m (.push b (some r) hd) (.upd1 (UpdElem.push b r)) σ :=
  Premise.sound_update_typed σ (pushSome_agrees σ b r) (fun _ => TRun.push_nd σ b (some r))
    (hx := pushSome_exh σ b r)

/-- `storagePopSave`, `storagePopSaveMappingElement`. -/
theorem sound_pop {E : Ty} (b : SPath C Γ (.array E)) :
    Premise.Runs m (.pop b) (.upd1 (if b.elemMapping then UpdElem.shrink b else UpdElem.pop b)) σ :=
  Premise.sound_update_typed σ (pop_agrees σ b) (fun _ =>
    ((SPath.resolveT_ends σ b).bind fun _ => (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _).1)
    (hx := fun _ => Upd.exh_of_pushFree (by
      split <;> simp only [Upd.pushFree, UpdElem.pushFree, UpdElem.pop, UpdElem.shrink,
        Tm.pushFree, Op2.pushFree, SPath.lower_pushFree, Bool.and_self]))

/-- `storageLocalRootPushBind`, `storageLocalRootPushBindMappingElement`:
`{storage := extend(storage, b) ‖ lsv := next(b)}`. -/
theorem sound_rebindPush {R : RefTy} (i : Idx Γ (.alias R)) (b : SPath C Γ (.array (.ref R)))
    (hd : (Ty.ref R).defaultOkS = true) :
    Premise.Runs m (.rebind i (.push b hd)) (.update (Upd.pushBind i b)) σ :=
  Premise.sound_update_typed σ (rebindPush_agrees σ i b hd) (fun _ =>
    TRes.NoDiv.bind (ARhs.evalT_nd σ (.push b hd)) fun _ => TRes.NoDiv.ok _)
    (hx := pushBind_exh σ i b hd)

/-- `transferNoCallbackBox`: `{net := …}`. -/
theorem sound_transferBox (sadr se : Simple C Γ .uint) :
    Premise.Runs m (.transfer (.simple sadr) (.simple se)) (.upd1 (UpdElem.payTo sadr se)) σ :=
  Premise.sound_update_typed σ (transferBox_agrees σ sadr se) fun _ => TRes.NoDiv.ok _

/-- `transferDiamond` (Lean): the goal fails. -/
theorem sound_done_false {Γ' : Ctx} (s : Stmt C Γ Γ') : Premise.Sound m s (.done false) σ :=
  Premise.sound_done σ false fun h => nomatch h

/-- `sendNoCallbackBox`, `sendNoCallbackDiamond`: the payment with `pv` true,
or `pv` false. -/
theorem sound_send (pv : Idx Γ (.val .bool)) (sadr se : Simple C Γ .uint) (fs : List (Fml C Γ)) :
    Premise.Sound m (.send pv (.simple sadr) (.simple se)) (.cases fs
      [(Upd.nil.snoc (UpdElem.payTo sadr se)).snoc (.local pv (.val (Tm.lit (p := .bool) true))),
        Upd.nil.snoc (.local pv (.val (Tm.lit (p := .bool) false)))]) σ :=
  Premise.sound_cases_typed (s := .send pv (.simple sadr) (.simple se))
    (t := TRun.send pv (.simple sadr) (.simple se)) σ (TRes.AgreesO.pure _)
    (fun _ => send_sim σ pv sadr se) (fun _ => TRes.NoDiv.ok _) (hx := fun U hU _ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hU
      rcases hU with rfl | rfl <;> exact Upd.exh_of_pushFree (by
        simp only [Upd.pushFree, UpdElem.pushFree, UpdElem.payTo, Rhs.pushFree, Tm.pushFree,
          Simple.lower_pushFree, Bool.and_self]))

/-- `memoryReferenceDeclFreshAlloc`. -/
theorem sound_declMemFresh (R : RefTy) (x : Var)
    (hd : (none.isSome || (Ty.ref R).defaultOkS) = true) (hm : (Ty.ref R).mapFree = true) :
    Premise.Runs m (.declMem R x none hd hm) (.update ((Upd.nil.decl x
      (.mref (.app1 (.alloc R hm) (.app0 .memory)))).snoc
        (.memory (.app1 (.addM R hm) (.app0 .memory))))) σ :=
  Premise.sound_update_typed σ (declMemFresh_agrees σ R x hm) fun _ => TRes.NoDiv.ok _

/-- `memoryRootDeleteFreshRebind`. -/
theorem sound_deleteMemVar {R : RefTy} (i : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    (hd : (Ty.ref R).defaultOkS = true) :
    Premise.Runs m (.deleteMem (.var i hm) hd) (.update (Upd.allocFresh i hm)) σ :=
  Premise.sound_update_typed σ (allocFresh_agrees σ i hm) fun _ => TRes.NoDiv.ok _

/-- `memoryStorageCopy`. -/
theorem sound_allocCopy_copy {R : RefTy} (i : Idx Γ (.mem R)) (p : SPath C Γ (.ref R))
    (hm : (Ty.ref R).mapFree = true) :
    Premise.Runs m (.rebindMem i (.copy p hm))
      (.allocCopy i hm (.app2 .sfind (.app0 .storage) p.lower)) σ :=
  Premise.sound_update_typed σ (allocCopy_copy_agrees σ i p hm) fun _ =>
    ((MRhs.evalT_ends σ (.copy p hm)).bind fun _ => TRes.Ends.ok _).1

/-- `memoryArrayFreshAlloc`. -/
theorem sound_allocCopy_newArr {R : RefTy} (i : Idx Γ (.mem R)) (n : Simple C Γ .uint)
    (h : R.newArrOk = true) :
    Premise.Runs m (.rebindMem i (.newArr n h))
      (.allocCopy i (RefTy.mapFree_of_newArrOk h) (.app1 (.newArr h) n.lower)) σ :=
  Premise.sound_update_typed σ (allocCopy_newArr_agrees σ i n h) fun _ =>
    ((MRhs.evalT_ends σ (.newArr n h)).bind fun _ => TRes.Ends.ok _).1

theorem clearT_ends : {T : Ty} → (a : MAddr σ.H T) → (hm : T.mapFree = true) →
    (TRun.clearT σ a hm).Ends
  | .prim _, _, _ => (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _
  | .ref R, a, hm => by
    simp only [TRun.clearT]
    split <;> exact ⟨(fun h => nomatch h), fun h => nomatch h⟩

/-- `memoryFieldDelete*`, `memoryIndexDelete*`: a slot reset to its default,
or written a fresh default object. -/
theorem sound_clearMem {T : Ty} (l : MLoc C Γ T) (hd : T.defaultOkS = true) :
    Premise.Runs m (.deleteMem (.loc l) hd) (.clearMem T l.lower l.mapFree) σ := by
  cases T with
  | prim p =>
    exact Premise.sound_update_typed σ (clearPrim_agrees σ l) fun _ =>
      ((MLoc.addrT_ends σ l).bind fun a => clearT_ends σ a _).1
  | ref R =>
    exact Premise.sound_update_typed σ (clearRef_agrees σ l) fun _ =>
      ((MLoc.addrT_ends σ l).bind fun a => clearT_ends σ a _).1

theorem applyP_decl1 {t : LTy} (x : Var) (r : Rhs C Γ t) :
    (Upd.nil.decl x r).applyP σ = (r.eval σ).map fun v => (σ.glob, σ.locV.push v) := by
  show ((r.eval σ).bind _).map _ = _
  cases r.eval σ <;> rfl

/-- `valueDeclSkip`: `{v := defVal(T)}`. -/
theorem sound_valueDeclSkip (p : PrimTy) (x : Var) :
    Premise.Runs m (.declLocal p x none)
      (.update (Upd.nil.decl x (.val (.app0 (.lit (PrimTy.dflt p)))))) σ :=
  Premise.sound_update_typed (s := .declLocal p x none) (t := TRun.declLocal p none) σ
    (TRes.AgreesO.ret (by rw [applyP_decl1, State.locV_push]; rfl)) fun _ => TRes.NoDiv.ok _

/-- `storageLocalDeclSkip`: `{lsv := unset}`. -/
theorem sound_storageLocalDeclSkip (R : RefTy) (x : Var) :
    Premise.Runs m (.declStorage R x none) (.update (Upd.nil.decl (t := .alias R) x .unset)) σ :=
  Premise.sound_update_typed (s := .declStorage R x none) (t := TRun.declStorage R none) σ
    (TRes.AgreesO.ret (by rw [applyP_decl1, State.locV_push]; rfl)) fun _ => TRes.NoDiv.ok _

/-- `revertBox`, `revertDiamond`. -/
theorem sound_revert :
    Premise.Sound m (.revert : Stmt C Γ Γ) (.done (m == .box)) σ :=
  Premise.sound_done σ _ fun h =>
    ⟨by cases m <;> first | rfl | exact absurd h (by decide), .revert, rfl, by decide⟩

end Arms2

end Solidity
