import Solidity.Calculus.SoundKit
import Solidity.Theory.StateWrites

/-!
# Soundness of the update arms

The rules of `Calculus/Arms.lean` and `Step.lean` whose premise is an
update (`Premise.Sound`, `Calculus/ProvesSound.lean`).  An update is a
term of `Update.lean`, read on the erasure, so each arm states that the
statement's typed step (`TRun.*`, `Semantics/Run.lean`) agrees with the
update applied to the erasure of the state it starts in (`*_agrees`,
`TRes.Agrees`), and closes with `Premise.sound_update_typed`
(`Calculus/SoundKit.lean`).  An agreement composes the evaluators' (the
typed evaluator against the lowered term, `Calculus/LowerRun.lean`) with
the write's (`Semantics/StorageErase.lean`, `Semantics/HeapErase.lean`),
after an equation that reads the update's terms in the order the statement
reads them (`Theory/StateWrites.lean`'s frame lemmas, on `σ.glob`).

The arms ask of the typed run that it does not diverge under the diamond:
an expression, a location and every write but a push neither diverge nor
are exhausted (`Val.evalT_ends` and its kin,
`Semantics/Ends.lean`), and a push onto `2^256 - 1` elements is
exhausted (`TRun.push_nd`, decision 15), which both modalities accept.  Every
statement is on it: no struct repeats a member name (decision 16).
-/

namespace Solidity
open Solidity (Modality Srt Op0 Op1 Op2 Op3 NoPanic evalBinop)
open Semantics (Value SVal MVal Seg Halt Res)
open Solidity (readAddr)

variable {C : Contract}

/-! ## Updates on the erasure: the terms in the statement's order

The update reads its right-hand sides in the state it is applied in, the
statement left to right; both reach the same writes through the same reads,
and a write of the storage (the heap) changes nothing else
(`Theory/StateWrites.lean`'s `*_with`).  Each equation leaves the
statement's locations as terms (`P`, `A`), read once. -/

section Updates

variable {Γ : Ctx} (σ : EState C Γ)

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

theorem upd2_apply (e₁ e₂ : UpdElem C Γ Γ) :
    ((Upd.nil.snoc e₁).snoc e₂).apply σ = (do e₂.write σ (← e₁.write σ σ)) := rfl

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
  storage_glob σ _ (Semantics.State.saveStorage_with _ _ _ _)

/-- A heap write through the term, as the statement's write. -/
theorem writeAddr_glob (mv : Semantics.MVal) (a : Semantics.Addr) :
    (writeAddr σ.glob mv a >>= fun μ =>
      pure (σ.withGlob { σ.glob with heap := μ.heap, nextId := μ.nextId })) =
      σ.withGlob <$> writeAddr σ.glob mv a :=
  memory_glob σ _ (Solidity.writeAddr_with _ _ _)

theorem bind_withGlob (x : Res Semantics.State) :
    (x >>= fun τ => pure (σ.withGlob τ)) = σ.withGlob <$> x := by
  cases x <;> rfl

theorem writeAddr_ok_with {s x : Semantics.State} {mv : Semantics.MVal} {a : Semantics.Addr}
    (h : writeAddr s mv a = .ok x) : { s with heap := x.heap, nextId := x.nextId } = x := by
  have e := Solidity.writeAddr_with s mv a
  rw [h] at e
  exact Except.ok.inj e

/-- A global step's state and value, with the locals. -/
def glob₂ (x : Semantics.State × Value) : EState C Γ × Value := (σ.withGlob x.1, x.2)

/-- `storage := save(storage, P, P ⊕ t)`: the compound write at the path. -/
theorem save_compound {op : BinOp} (hop : op.hasCompoundAssign = true) (p : PrimTy)
    (P : Tm C Γ .path) (t : Tm C Γ .val) {w : Value} (ht : t.eval σ = .ok w) :
    (UpdElem.storage (.app3 .save .storage P
      (.app1 .sval rfl (.app2 (.binop op p) (.app2 .find .storage P) t)))).write σ σ = (do
      let (rt, segs) ← P.eval σ
      σ.withGlob <$> opStore σ.glob op p rt segs w) := by
  simp only [UpdElem.write, Tm.eval, Op3.eval, Op2.eval, Op1.eval, Op0.eval,
    evalBinop_compound hop, ht, opStore, bind_assoc, pure_bind, writeStorage_toSVal,
    saveStorage_glob, map_bind]
  cases P.eval σ <;> rfl

/-- `memory := write(memory, A, A ⊕ t)`: the compound write at the address. -/
theorem write_compound {op : BinOp} (hop : op.hasCompoundAssign = true) (p : PrimTy)
    (A : Tm C Γ .addr) (t : Tm C Γ .val) {w : Value} (ht : t.eval σ = .ok w) :
    (UpdElem.memory (.app3 .write .memory A
      (.app1 .mval rfl (.app2 (.binop op p) (.app2 .read .memory A) t)))).write σ σ = (do
      σ.withGlob <$> opMem σ.glob op p (← A.eval σ) w) := by
  simp only [UpdElem.write, Tm.eval, Op3.eval, Op2.eval, Op1.eval, Op0.eval,
    evalBinop_compound hop, ht, opMem, Solidity.readLoc_eq, Semantics.writeLoc_eq, bind_assoc,
    pure_bind, writeAddr_glob, map_bind]
  cases A.eval σ <;> rfl

/-- `storage := save(storage, P, P ± 1)`: the bump at the path. -/
theorem save_bump (op : IncDec) (p : PrimTy) (P : Tm C Γ .path) :
    (UpdElem.storage (.app3 .save .storage P
      (.app1 .sval rfl (.app2 (.binop op.binOp p) (.app2 .find .storage P) Tm.one)))).write σ σ =
      ((do
        let (rt, segs) ← P.eval σ
        glob₂ σ <$> bumpStore σ.glob op p rt segs) >>= fun y => pure y.1) := by
  simp only [UpdElem.write, Tm.eval, Op3.eval, Op2.eval, Op1.eval, Op0.eval,
    evalBinop_bump, Solidity.applyBinOp_bump, bumpStore, bind_assoc, pure_bind,
    writeStorage_toSVal, saveStorage_glob, map_bind, map_pure, glob₂, bind_withGlob]
  cases P.eval σ <;> rfl

/-- `memory := write(memory, A, A ± 1)`: the bump at the address. -/
theorem write_bump (op : IncDec) (p : PrimTy) (A : Tm C Γ .addr) :
    (UpdElem.memory (.app3 .write .memory A
      (.app1 .mval rfl (.app2 (.binop op.binOp p) (.app2 .read .memory A) Tm.one)))).write σ σ =
      ((do glob₂ σ <$> bumpMem σ.glob op p (← A.eval σ)) >>= fun y => pure y.1) := by
  simp only [UpdElem.write, Tm.eval, Op3.eval, Op2.eval, Op1.eval, Op0.eval,
    evalBinop_bump, Solidity.applyBinOp_bump, bumpMem, Solidity.readLoc_eq,
    Semantics.writeLoc_eq, bind_assoc, pure_bind, writeAddr_glob, map_bind, map_pure, glob₂,
    bind_withGlob]
  cases A.eval σ <;> rfl

/-- The value `x++` gives at a path is what `bumped(find(storage, P))` reads in
the state before. -/
theorem bumped_find (op : IncDec) (p : PrimTy) (P : Tm C Γ .path) {q : Name × List Seg}
    (hq : P.eval σ = .ok q) {τ : Semantics.State} {v : Value}
    (hb : bumpStore σ.glob op p q.1 q.2 = .ok (τ, v)) :
    (Tm.bumped op p (.app2 .find .storage P)).eval σ = .ok v := by
  unfold Tm.bumped
  simp only [bumpStore, SemanticsProperties.Res.bind_eq_ok] at hb
  obtain ⟨sv, hsv, old, hold, n, hn, new, hnew, τ', hτ', he⟩ := hb
  cases Except.ok.inj he
  split <;> simp only [Tm.eval, Op2.eval, Op0.eval, evalBinop_bump, Solidity.applyBinOp_bump,
    Res.bind_ok, pure_bind, bind_assoc, hq, hsv, hold, hn, hnew] <;> rfl

/-- The value `x++` gives at an address is what `bumped(read(memory, A))`
reads in the state before. -/
theorem bumped_read (op : IncDec) (p : PrimTy) (A : Tm C Γ .addr) {a : Semantics.Addr}
    (ha : A.eval σ = .ok a) {τ : Semantics.State} {v : Value}
    (hb : bumpMem σ.glob op p a = .ok (τ, v)) :
    (Tm.bumped op p (.app2 .read .memory A)).eval σ = .ok v := by
  unfold Tm.bumped
  simp only [bumpMem, SemanticsProperties.Res.bind_eq_ok] at hb
  obtain ⟨old, hold, n, hn, new, hnew, τ', hτ', he⟩ := hb
  cases Except.ok.inj he
  simp only [Solidity.readLoc_eq, SemanticsProperties.Res.bind_eq_ok] at hold
  obtain ⟨r, hr, hro⟩ := hold
  split <;> simp only [Tm.eval, Op2.eval, Op0.eval, evalBinop_bump, Solidity.applyBinOp_bump,
    Res.bind_ok, pure_bind, bind_assoc, ha, hr, hro, hn, hnew] <;> rfl

/-- `{P := P ± 1 ‖ v := bumped(P)}` at a path. -/
theorem save_bump_assign (op : IncDec) (p : PrimTy) (P : Tm C Γ .path) (i : Idx Γ (.val p)) :
    ((Upd.nil.snoc (UpdElem.storage (.app3 .save .storage P
      (.app1 .sval rfl (.app2 (.binop op.binOp p) (.app2 .find .storage P) Tm.one))))).snoc
      (.local i (.val (Tm.bumped op p (.app2 .find .storage P))))).apply σ =
      ((do
        let (rt, segs) ← P.eval σ
        glob₂ σ <$> bumpStore σ.glob op p rt segs) >>= fun y => pure (y.1.setLocal i y.2)) := by
  rw [upd2_apply, save_bump, bind_assoc]
  cases hq : P.eval σ with
  | error => rfl
  | ok q =>
    obtain ⟨rt, segs⟩ := q
    show ((glob₂ σ <$> bumpStore σ.glob op p rt segs) >>= fun y => (pure y.1 : Res _) >>= _) =
      ((glob₂ σ <$> bumpStore σ.glob op p rt segs) >>= fun y => pure (y.1.setLocal i y.2))
    cases hb : bumpStore σ.glob op p rt segs with
    | error => rfl
    | ok x =>
      obtain ⟨τ, v⟩ := x
      show (do pure ((σ.withGlob τ).setLocal i
        (← (Tm.bumped op p (.app2 .find .storage P)).eval σ))) = _
      rw [bumped_find σ op p P hq hb]; rfl

/-- `{A := A ± 1 ‖ v := bumped(A)}` at an address. -/
theorem write_bump_assign (op : IncDec) (p : PrimTy) (A : Tm C Γ .addr) (i : Idx Γ (.val p)) :
    ((Upd.nil.snoc (UpdElem.memory (.app3 .write .memory A
      (.app1 .mval rfl (.app2 (.binop op.binOp p) (.app2 .read .memory A) Tm.one))))).snoc
      (.local i (.val (Tm.bumped op p (.app2 .read .memory A))))).apply σ =
      ((do glob₂ σ <$> bumpMem σ.glob op p (← A.eval σ)) >>= fun y =>
        pure (y.1.setLocal i y.2)) := by
  rw [upd2_apply, write_bump, bind_assoc]
  cases ha : A.eval σ with
  | error => rfl
  | ok a =>
    show ((glob₂ σ <$> bumpMem σ.glob op p a) >>= fun y => (pure y.1 : Res _) >>= _) =
      ((glob₂ σ <$> bumpMem σ.glob op p a) >>= fun y => pure (y.1.setLocal i y.2))
    cases hb : bumpMem σ.glob op p a with
    | error => rfl
    | ok x =>
      obtain ⟨τ, v⟩ := x
      show (do pure ((σ.withGlob τ).setLocal i
        (← (Tm.bumped op p (.app2 .read .memory A)).eval σ))) = _
      rw [bumped_read σ op p A ha hb]; rfl

end Updates

/-! ## The agreements: the typed step against the update

Each update arm's typed step against its update applied to the erasure, as
`Premise.sound_update_typed` asks. -/

section Agrees

variable {Γ : Ctx} (σ : State C Γ)

theorem setLocal_agrees {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (TRun.assignLocal i v σ)
      ((Upd.nil.snoc (.local i (.val v.lower))).apply σ.erase) :=
  TRes.Agrees.bind (Val.lower_evalT σ v) fun x =>
    TRes.Agrees.of_eq (congrArg Except.ok (State.setLocal_erase σ i x).symm)

theorem save_agrees {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (TRun.assign l r σ)
      ((Upd.nil.snoc (.storage (.app3 .save .storage l.lower r.lower))).apply σ.erase) := by
  have e : (Upd.nil.snoc (.storage (.app3 .save .storage l.lower r.lower))).apply σ.erase = (do
      let sv ← r.lower.eval σ.erase
      let (root, segs) ← l.lower.eval σ.erase
      σ.erase.withGlob <$> σ.erase.glob.writeStorage root segs sv) := by
    show (do
      let st ← Op3.eval σ.erase.glob .save (pure σ.erase.glob) (l.lower.eval σ.erase)
        (r.lower.eval σ.erase)
      pure (σ.erase.withGlob { σ.erase.glob with storage := st.storage })) = _
    simp only [Op3.eval, bind_assoc, pure_bind]
    congr 1; funext sv; congr 1; funext q
    exact storage_glob σ.erase _ (Semantics.State.writeStorage_with _ _ _ _)
  rw [e]
  refine TRes.Agrees.bind (Src.lower_valueT σ r) fun sv => ?_
  refine TRes.Agrees.bind (Loc.lower_resolveT σ l) fun ref => ?_
  show TRes.Agrees _ (do
      let st ← TRes.ofOpt (σ.storage.write ref sv)
      pure (⟨σ.withStorage st, List.prefix_refl _⟩ : Out C σ.H Γ))
    (σ.erase.withGlob <$> σ.erase.glob.writeStorage ref.root ref.path.erase sv.erase)
  rw [Storage.writeStorage_erase (σ := σ.erase.glob) rfl ref sv]
  cases σ.storage.write ref sv <;> rfl

theorem saveMem_agrees {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (TRun.assignFromMem l p σ)
      ((Upd.nil.snoc (.storage (.app3 .save .storage l.lower
        (.app2 .copyMem .memory p.lower)))).apply σ.erase) := by
  have e : (Upd.nil.snoc (.storage (.app3 .save .storage l.lower
      (.app2 .copyMem .memory p.lower)))).apply σ.erase = (do
      let id ← p.lower.eval σ.erase
      let sv ← Semantics.copyMem σ.erase.glob (.ref id)
      let (root, segs) ← l.lower.eval σ.erase
      σ.erase.withGlob <$> σ.erase.glob.writeStorage root segs sv) := by
    show (do
      let st ← Op3.eval σ.erase.glob .save (pure σ.erase.glob) (l.lower.eval σ.erase)
        (Op2.eval σ.erase.glob .copyMem (pure σ.erase.glob) (p.lower.eval σ.erase))
      pure (σ.erase.withGlob { σ.erase.glob with storage := st.storage })) = _
    simp only [Op3.eval, Op2.eval, bind_assoc, pure_bind]
    congr 1; funext id; congr 1; funext sv; congr 1; funext q
    exact storage_glob σ.erase _ (Semantics.State.writeStorage_with _ _ _ _)
  rw [e]
  refine TRes.Agrees.bind (MPath.lower_mvalT σ p) fun m => ?_
  show TRes.Agrees _ _ (do
    let sv ← Semantics.copyMem σ.erase.glob (MVal.erase (.ref R) m)
    let (root, segs) ← l.lower.eval σ.erase
    σ.erase.withGlob <$> σ.erase.glob.writeStorage root segs sv)
  rw [State.copyMem_erase (T := .ref R) σ m, ok_bind]
  refine TRes.Agrees.bind (Loc.lower_resolveT σ l) fun ref => ?_
  show TRes.Agrees _ (do
      let st ← TRes.ofOpt (σ.storage.write ref (σ.copyMToSt (T := .ref R) m))
      pure (⟨σ.withStorage st, List.prefix_refl _⟩ : Out C σ.H Γ))
    (σ.erase.withGlob <$> σ.erase.glob.writeStorage ref.root ref.path.erase
      (σ.copyMToSt (T := .ref R) m).erase)
  rw [Storage.writeStorage_erase (σ := σ.erase.glob) rfl ref]
  cases σ.storage.write ref (σ.copyMToSt (T := .ref R) m) <;> rfl

theorem delAt_agrees {T : Ty} (l : Loc C Γ T) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (TRun.delete l σ)
      ((Upd.nil.snoc (.storage (.app2 .delAt .storage l.lower))).apply σ.erase) := by
  have e : (Upd.nil.snoc (.storage (.app2 .delAt .storage l.lower))).apply σ.erase = (do
      let (root, segs) ← l.lower.eval σ.erase
      let cur ← σ.erase.glob.findStorage root segs
      σ.erase.withGlob <$> σ.erase.glob.saveStorage root segs cur.defaultOf) := by
    show (do
      let st ← Op2.eval σ.erase.glob .delAt (pure σ.erase.glob) (l.lower.eval σ.erase)
      pure (σ.erase.withGlob { σ.erase.glob with storage := st.storage })) = _
    simp only [Op2.eval, bind_assoc, pure_bind]
    congr 1; funext q; congr 1; funext cur
    exact storage_glob σ.erase _ (Semantics.State.saveStorage_with _ _ _ _)
  rw [e]
  refine TRes.Agrees.bind (Loc.lower_resolveT σ l) fun ref => ?_
  show TRes.Agrees _ (do
      let st ← TRes.ofOpt (σ.storage.delete ref)
      pure (⟨σ.withStorage st, List.prefix_refl _⟩ : Out C σ.H Γ))
    (do
      let cur ← σ.erase.glob.findStorage ref.root ref.path.erase
      σ.erase.withGlob <$> σ.erase.glob.saveStorage ref.root ref.path.erase cur.defaultOf)
  rw [← map_bind, Storage.delete_erase (σ := σ.erase.glob) rfl ref]
  cases σ.storage.delete ref <;> rfl

theorem writeMem_agrees {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (TRun.assignMem l r σ)
      ((Upd.nil.snoc (.memory (.app3 .write .memory l.lower r.lower))).apply σ.erase) := by
  have e : (Upd.nil.snoc (.memory (.app3 .write .memory l.lower r.lower))).apply σ.erase = (do
      let mv ← r.lower.eval σ.erase
      let a ← l.lower.eval σ.erase
      σ.erase.withGlob <$> writeAddr σ.erase.glob mv a) := by
    show (do
      let μ ← Op3.eval σ.erase.glob .write (pure σ.erase.glob) (l.lower.eval σ.erase)
        (r.lower.eval σ.erase)
      pure (σ.erase.withGlob { σ.erase.glob with heap := μ.heap, nextId := μ.nextId })) = _
    simp only [Op3.eval, bind_assoc, pure_bind]
    congr 1; funext mv; congr 1; funext a
    exact memory_glob σ.erase _ (Solidity.writeAddr_with _ _ _)
  rw [e]
  refine TRes.Agrees.bind (MSrc.lower_mvalT σ r) fun mv => ?_
  refine TRes.Agrees.bind (MLoc.lower_addrT σ l) fun a => ?_
  show TRes.Agrees _ (do
      let hp ← TRes.ofOpt (σ.heap.writeAddr a mv)
      pure (⟨σ.withHeap hp, List.prefix_refl _⟩ : Out C σ.H Γ))
    (σ.erase.withGlob <$> writeAddr σ.erase.glob (MVal.erase T mv) a.erase)
  rw [writeAddr_erase σ a mv]
  cases σ.heap.writeAddr a mv <;> rfl

theorem rebindPath_agrees {R : RefTy} (i : Idx Γ (.alias R)) (p : SPath C Γ (.ref R)) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (TRun.rebind i (.path p) σ)
      ((Upd.nil.snoc (.local i (.path p.lower))).apply σ.erase) := by
  simp only [TRun.rebind, ARhs.evalT, upd1_apply, UpdElem.write, Rhs.eval, bind_assoc, pure_bind]
  exact TRes.Agrees.bind (SPath.lower_resolveT σ p) fun ref =>
    TRes.Agrees.of_eq (congrArg Except.ok (State.setLocal_erase σ i (some ref)).symm)

theorem rebindMemAlias_agrees {R : RefTy} (i : Idx Γ (.mem R)) (p : MPath C Γ (.ref R)) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (TRun.rebindMem i (.alias p) σ)
      ((Upd.nil.snoc (.local i (.mref p.lower))).apply σ.erase) := by
  simp only [TRun.rebindMem, MRhs.evalT, upd1_apply, UpdElem.write, Rhs.eval, bind_assoc,
    pure_bind]
  exact TRes.Agrees.bind (MPath.lower_mvalT σ p) fun r =>
    TRes.Agrees.of_eq (congrArg Except.ok (State.setLocal_erase σ i (some r)).symm)

/-! ### Compound targets -/

section OpLoc

variable {op : BinOp} {p : PrimTy}

theorem storeLoc_agrees (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
    (L : Loc C Γ (.prim p)) (v : p.Denote) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (do opStoreT σ op (← L.resolveT σ) v)
      (do
        let (rt, segs) ← L.lower.eval σ.erase
        σ.erase.withGlob <$> opStore σ.erase.glob op p rt segs (PrimTy.erase v)) :=
  TRes.Agrees.bind (Loc.lower_resolveT σ L) fun ref => opStoreT_erase σ hop hp ref v

theorem storeMem_agrees (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
    (L : MLoc C Γ (.prim p)) (v : p.Denote) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (do opMemT σ op (← L.addrT σ) v)
      (do σ.erase.withGlob <$> opMem σ.erase.glob op p (← L.lower.eval σ.erase) (PrimTy.erase v)) :=
  TRes.Agrees.bind (MLoc.lower_addrT σ L) fun a => opMemT_erase σ hop hp a v

theorem bumpLoc_agrees (o : IncDec) (hp : p.isNumeric = true) (L : Loc C Γ (.prim p)) :
    TRes.Agrees (fun x : Out C σ.H Γ × p.Denote => (x.1.st.erase, PrimTy.erase x.2))
      (do bumpStoreT σ o (← L.resolveT σ))
      (do
        let (rt, segs) ← L.lower.eval σ.erase
        glob₂ σ.erase <$> bumpStore σ.erase.glob o p rt segs) :=
  TRes.Agrees.bind (Loc.lower_resolveT σ L) fun ref => bumpStoreT_erase σ o hp ref fun _ _ => rfl

theorem bumpMem_agrees (o : IncDec) (hp : p.isNumeric = true) (L : MLoc C Γ (.prim p)) :
    TRes.Agrees (fun x : Out C σ.H Γ × p.Denote => (x.1.st.erase, PrimTy.erase x.2))
      (do bumpMemT σ o (← L.addrT σ))
      (do glob₂ σ.erase <$> bumpMem σ.erase.glob o p (← L.lower.eval σ.erase)) :=
  TRes.Agrees.bind (MLoc.lower_addrT σ L) fun a => bumpMemT_erase σ o hp a fun _ _ => rfl

theorem opAssign_agrees (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
    (l : OpLoc C Γ p) (se : Simple C Γ p) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (TRun.opAssign op l (.simple se) σ)
      ((Upd.nil.snoc (l.set (l.op op se.lower))).apply σ.erase) := by
  have hse := Simple.lower_evalT σ se
  rw [upd1_apply]
  show TRes.Agrees _ (l.storeT σ op (se.evalT σ)) _
  cases l with
  | «local» i =>
    show TRes.Agrees _ _
      (do pure (σ.erase.setLocal i (← evalBinop op p (Env.get i σ.erase.env) (se.lower.eval σ.erase))))
    rw [hse, evalBinop_compound hop, State.erase_get, LTy.TDenote.erase_val, ok_bind,
      compound_erase' hop hp]
    show TRes.Agrees _ (do
      let new ← TRes.ofOpt (compoundT op p (PrimTy.key (TEnv.get i σ.env)) (PrimTy.key (se.evalT σ)))
      pure (⟨σ.setLocal i new, List.prefix_refl _⟩ : Out C σ.H Γ)) _
    cases compoundT op p (PrimTy.key (TEnv.get i σ.env)) (PrimTy.key (se.evalT σ)) with
    | none => rfl
    | some new => exact TRes.Agrees.of_eq (congrArg Except.ok (State.setLocal_erase σ i new).symm)
  | root r h =>
    exact (storeLoc_agrees σ hop hp (.root r h) _).of_eq_right
      (save_compound σ.erase hop p _ _ hse).symm
  | field b f h =>
    exact (storeLoc_agrees σ hop hp (.field b f h) _).of_eq_right
      (save_compound σ.erase hop p _ _ hse).symm
  | index it b ie =>
    exact (storeLoc_agrees σ hop hp (.index it b (.simple ie)) _).of_eq_right
      (save_compound σ.erase hop p _ _ hse).symm
  | mfield b f h =>
    exact (storeMem_agrees σ hop hp (.field b f h) _).of_eq_right
      (write_compound σ.erase hop p _ _ hse).symm
  | mindex a b ie =>
    exact (storeMem_agrees σ hop hp (.index a b (.simple ie)) _).of_eq_right
      (write_compound σ.erase hop p _ _ hse).symm

/-- `l++` on a local, against `{v := v ± 1}`, by its value too. -/
theorem bumpLocal_agrees (o : IncDec) (hp : p.isNumeric = true) (i : Idx Γ (.val p)) :
    TRes.Agrees (fun x : Out C σ.H Γ × p.Denote => (x.1.st.erase, PrimTy.erase x.2))
      ((OpLoc.local i).bumpT σ o)
      (do
        let new ← evalBinop o.binOp p (Env.get i σ.erase.env) (pure (.int 1))
        pure (σ.erase.setLocal i new, if o.isPre then new else Env.get i σ.erase.env)) := by
  simp only [OpLoc.bumpT, State.erase_get, LTy.TDenote.erase_val, evalBinop_bump,
    Solidity.applyBinOp_bump, asInt_erase_numeric hp, ok_bind, pure_bind, bump_erase hp]
  cases Solidity.bumpT o p (PrimTy.key (TEnv.get i σ.env)) with
  | none => rfl
  | some new =>
    refine TRes.Agrees.of_eq ?_
    rw [State.setLocal_erase]
    cases o.isPre <;> rfl

theorem incDec_agrees (o : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    TRes.Agrees (fun x : Out C σ.H Γ => x.st.erase) (TRun.incDec o l σ)
      ((Upd.nil.snoc (l.set (l.op o.binOp .one))).apply σ.erase) := by
  rw [upd1_apply]
  show TRes.Agrees _ (l.bumpT σ o >>= fun x => pure x.1) _
  cases l with
  | «local» i =>
    refine TRes.Agrees.of_eq_right ((bumpLocal_agrees σ o hp i).bind_fst) ?_
    simp only [UpdElem.write, Rhs.eval, OpLoc.set, OpLoc.op, OpLoc.cur, Tm.eval, Op2.eval,
      Op0.eval, bind_assoc, pure_bind]
  | root r h =>
    exact (bumpLoc_agrees σ o hp (.root r h)).bind_fst.of_eq_right (save_bump σ.erase o p _).symm
  | field b f h =>
    exact (bumpLoc_agrees σ o hp (.field b f h)).bind_fst.of_eq_right
      (save_bump σ.erase o p _).symm
  | index it b ie =>
    exact (bumpLoc_agrees σ o hp (.index it b (.simple ie))).bind_fst.of_eq_right
      (save_bump σ.erase o p _).symm
  | mfield b f h =>
    exact (bumpMem_agrees σ o hp (.field b f h)).bind_fst.of_eq_right
      (write_bump σ.erase o p _).symm
  | mindex a b ie =>
    exact (bumpMem_agrees σ o hp (.index a b (.simple ie))).bind_fst.of_eq_right
      (write_bump σ.erase o p _).symm

theorem assignIncDec_agrees (i : Idx Γ (.val p)) (o : IncDec) (hp : p.isNumeric = true)
    (l : OpLoc C Γ p) :
    TRes.Agrees (fun x : Out C σ.H Γ => x.st.erase) (TRun.assignIncDec i o l σ)
      (((Upd.nil.snoc (l.set (l.op o.binOp .one))).snoc
        (.local i (.val (Tm.bumped o p l.cur)))).apply σ.erase) := by
  have hk : ∀ x : Out C σ.H Γ × p.Denote, TRes.Agrees (fun x : Out C σ.H Γ => x.st.erase)
      (pure (⟨x.1.st.setLocal i x.2, x.1.ext⟩ : Out C σ.H Γ))
      (pure ((x.1.st.erase, PrimTy.erase x.2).1.setLocal i (x.1.st.erase, PrimTy.erase x.2).2)) :=
    fun x => TRes.Agrees.of_eq (congrArg Except.ok (State.setLocal_erase x.1.st i x.2).symm)
  show TRes.Agrees _ (l.bumpT σ o >>= fun x =>
    pure (⟨x.1.st.setLocal i x.2, x.1.ext⟩ : Out C σ.H Γ)) _
  cases l with
  | «local» j =>
    refine TRes.Agrees.of_eq_right (TRes.Agrees.bind
      (k' := fun y : EState C Γ × Value => pure (y.1.setLocal i y.2)) (bumpLocal_agrees σ o hp j) hk) ?_
    rw [upd2_apply]
    simp only [UpdElem.write, Rhs.eval, OpLoc.set, OpLoc.op, OpLoc.cur, Tm.bumped, Tm.eval,
      Op2.eval, Op0.eval, bind_assoc, pure_bind]
    cases hb : evalBinop o.binOp p (Env.get j σ.erase.env) (pure (.int 1)) with
    | error => rfl
    | ok new =>
      cases o.isPre <;> simp only [Bool.false_eq_true, ↓reduceIte, Tm.eval, Op2.eval, Op0.eval,
        pure_bind, hb] <;> rfl
  | root r h =>
    exact (TRes.Agrees.bind (bumpLoc_agrees σ o hp (.root r h)) hk).of_eq_right
      (save_bump_assign σ.erase o p _ i).symm
  | field b f h =>
    exact (TRes.Agrees.bind (bumpLoc_agrees σ o hp (.field b f h)) hk).of_eq_right
      (save_bump_assign σ.erase o p _ i).symm
  | index it b ie =>
    exact (TRes.Agrees.bind (bumpLoc_agrees σ o hp (.index it b (.simple ie))) hk).of_eq_right
      (save_bump_assign σ.erase o p _ i).symm
  | mfield b f h =>
    exact (TRes.Agrees.bind (bumpMem_agrees σ o hp (.field b f h)) hk).of_eq_right
      (write_bump_assign σ.erase o p _ i).symm
  | mindex a b ie =>
    exact (TRes.Agrees.bind (bumpMem_agrees σ o hp (.index a b (.simple ie))) hk).of_eq_right
      (write_bump_assign σ.erase o p _ i).symm

end OpLoc

end Agrees

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
    Premise.Runs m (.rebind i (.path p)) (.upd1 (.local i (.path p.lower))) σ :=
  Premise.sound_update_typed σ (rebindPath_agrees σ i p) fun _ =>
    (((SPath.resolveT_ends σ p).bind fun _ => TRes.Ends.ok _).bind fun _ => TRes.Ends.ok _).1

/-- `memoryRootRebind`, `memoryFieldReadAliasRoot`, `memoryIndexReadArrayMemory`:
`{mv := p}`. -/
theorem sound_rebindMemAlias {R : RefTy} (i : Idx Γ (.mem R)) (p : MPath C Γ (.ref R)) :
    Premise.Runs m (.rebindMem i (.alias p)) (.upd1 (.local i (.mref p.lower))) σ :=
  Premise.sound_update_typed σ (rebindMemAlias_agrees σ i p) fun _ =>
    ((MRhs.evalT_ends σ (.alias p)).bind fun _ => TRes.Ends.ok _).1

/-- `localOpAssign`, `storage*OpAssign`, `memory*OpAssign`: `{l := l ⊕ se}`. -/
theorem sound_opAssign {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (se : Simple C Γ p) :
    Premise.Runs m (.opAssign op hop hp l (.simple se)) (.upd1 (l.set (l.op op se.lower))) σ :=
  Premise.sound_update_typed σ (opAssign_agrees σ hop hp l se) fun _ =>
    (TRes.Ends.bind (TRes.Ends.ok _) fun _ => OpLoc.storeT_ends σ op l _).1

/-- `localIncrement`, `storage*Increment`, `memory*Increment`: `{l := l ± 1}`. -/
theorem sound_incDec {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    Premise.Runs m (.incDec op hp l) (.upd1 (l.set (l.op op.binOp .one))) σ :=
  Premise.sound_update_typed σ (incDec_agrees σ op hp l) fun _ =>
    ((OpLoc.bumpT_ends σ op l).bind fun _ => TRes.Ends.ok _).1

/-- `localAssignIncrement`, `…IncrementAssignment`:
`{l := l ± 1 ‖ v := bumped(l)}`. -/
theorem sound_assignIncDec {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (hs : l.recvSimple = true) :
    Premise.Runs m (.assignIncDec i op hp l hs) (.update ((Upd.nil.snoc
      (l.set (l.op op.binOp .one))).snoc (.local i (.val (Tm.bumped op p l.cur))))) σ :=
  Premise.sound_update_typed σ (assignIncDec_agrees σ i op hp l) fun _ =>
    ((OpLoc.bumpT_ends σ op l).bind fun _ => TRes.Ends.ok _).1

end Arms

/-! ## The other update arms (`Step.lean`): the agreements -/

section Agrees2

variable {Γ : Ctx} (σ : State C Γ)

/-- `b.push()` against the slot pushed on the erasure. -/
theorem pushNone_agrees {E : Ty} (b : SPath C Γ (.array E)) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (TRun.push b none σ) (do
      let (root, segs) ← b.lower.eval σ.erase
      σ.erase.withGlob <$> pushAt σ.erase.glob E root segs pure) := by
  refine TRes.Agrees.bind (SPath.lower_resolveT σ b) fun ref => ?_
  show TRes.Agrees _ (if σ.storage.full ref then .error .exhausted else do
      let st ← TRes.ofOpt (σ.storage.push ref fun slot => some slot)
      pure (⟨σ.withStorage st, List.prefix_refl _⟩ : Out C σ.H Γ))
    (σ.erase.withGlob <$> pushAt σ.erase.glob E ref.root ref.path.erase pure)
  cases hfull : σ.storage.full ref
  · rw [if_neg Bool.false_ne_true]
    rw [Storage.pushAt_erase (σ := σ.erase.glob) rfl ref pure (fun slot => some slot)
      (fun _ => rfl) (.inl hfull)]
    cases σ.storage.push ref (fun slot => some slot) <;> rfl
  · trivial

theorem pushSlot_agrees {E : Ty} (b : SPath C Γ (.array E)) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (TRun.push b none σ)
      ((Upd.nil.snoc (.storage (.app2 (.pushSlot E) .storage b.lower))).apply σ.erase) := by
  refine (pushNone_agrees σ b).of_eq_right ?_
  rw [upd1_apply]
  show _ = (do
    let st ← Op2.eval σ.erase.glob (.pushSlot E) (pure σ.erase.glob) (b.lower.eval σ.erase)
    pure (σ.erase.withGlob { σ.erase.glob with storage := st.storage }))
  simp only [Op2.eval, bind_assoc, pure_bind]
  congr 1; funext q
  exact (storage_glob σ.erase _ (Solidity.pushAt_with _ _ _ _ _)).symm

theorem extend_agrees {E : Ty} (b : SPath C Γ (.array E)) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (TRun.push b none σ)
      ((Upd.nil.snoc (.storage (.app2 (.extend E) .storage b.lower))).apply σ.erase) := by
  refine (pushNone_agrees σ b).of_eq_right ?_
  rw [upd1_apply]
  show _ = (do
    let st ← Op2.eval σ.erase.glob (.extend E) (pure σ.erase.glob) (b.lower.eval σ.erase)
    pure (σ.erase.withGlob { σ.erase.glob with storage := st.storage }))
  simp only [Op2.eval, pushPlaceAt, pushAt, SemanticsProperties.State.saveStorage_eq, bind_assoc,
    pure_bind]
  simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  cases b.lower.eval σ.erase with
  | error => rfl
  | ok q =>
    simp only
    cases σ.erase.glob.findStorage q.1 q.2 with
    | error => rfl
    | ok v =>
      cases v with
      | array elems shadow fx =>
        simp only
        cases σ.erase.glob.storeRes q.1 q.2 _ <;> rfl
      | _ => rfl

theorem pushSome_agrees {E : Ty} (b : SPath C Γ (.array E)) (r : Src C Γ E) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (TRun.push b (some r) σ)
      ((Upd.nil.snoc (.storage (.app3 .push .storage b.lower r.lower))).apply σ.erase) := by
  have e : (Upd.nil.snoc (.storage (.app3 .push .storage b.lower r.lower))).apply σ.erase = (do
      let (root, segs) ← b.lower.eval σ.erase
      σ.erase.withGlob <$> pushAt σ.erase.glob E root segs
        fun _ => do pure (← r.lower.eval σ.erase).strip) := by
    rw [upd1_apply]
    show (do
      let st ← Op3.eval σ.erase.glob .push (pure σ.erase.glob) (b.lower.eval σ.erase)
        (r.lower.eval σ.erase)
      pure (σ.erase.withGlob { σ.erase.glob with storage := st.storage })) = _
    simp only [Op3.eval, bind_assoc, pure_bind]
    congr 1; funext q
    rw [Solidity.pushAt_const σ.erase.glob .uint E]
    exact storage_glob σ.erase _ (Solidity.pushAt_with _ _ _ _ _)
  rw [e]
  refine TRes.Agrees.bind (SPath.lower_resolveT σ b) fun ref => ?_
  show TRes.Agrees _ (do
      let sv ← r.valueT σ
      if σ.storage.full ref then .error .exhausted else do
      let st ← TRes.ofOpt (σ.storage.push ref fun _ => some sv.strip)
      pure (⟨σ.withStorage st, List.prefix_refl _⟩ : Out C σ.H Γ))
    (σ.erase.withGlob <$> pushAt σ.erase.glob E ref.root ref.path.erase
      fun _ => do pure (← r.lower.eval σ.erase).strip)
  have ha := Src.lower_valueT σ r
  have hn := Src.valueT_noPanic σ r
  revert ha hn
  cases r.valueT σ with
  | ok sv =>
    intro ha _
    have hval : ∀ x : SVal E, (fun _ => do pure (← r.lower.eval σ.erase).strip) x.erase =
        toRes SVal.erase ((fun _ => some sv.strip) x) := fun _ => by
      show (do pure (← r.lower.eval σ.erase).strip) = _
      rw [show r.lower.eval σ.erase = .ok sv.erase from ha, ok_bind, ← SVal.strip_erase]
      rfl
    show TRes.Agrees _ (if σ.storage.full ref then .error .exhausted else do
        let st ← TRes.ofOpt (σ.storage.push ref fun _ => some sv.strip)
        pure (⟨σ.withStorage st, List.prefix_refl _⟩ : Out C σ.H Γ)) _
    cases hfull : σ.storage.full ref
    · rw [if_neg Bool.false_ne_true]
      rw [Storage.pushAt_erase (σ := σ.erase.glob) rfl ref _ _ hval (.inl hfull)]
      cases σ.storage.push ref (fun _ => some sv.strip) <;> rfl
    · trivial
  | error e =>
    intro ha hn
    cases e with
    | diverge => trivial
    | exhausted => trivial
    | panic => exact absurd rfl hn
    | revert =>
      have hval : ∀ x : SVal E, (fun _ => do pure (← r.lower.eval σ.erase).strip) x.erase =
          toRes SVal.erase ((fun _ => (none : Option (SVal E))) x) := fun _ => by
        show (do pure (← r.lower.eval σ.erase).strip) = _
        rw [show r.lower.eval σ.erase = .error .revert from ha]
        rfl
      rw [Storage.pushAt_erase (σ := σ.erase.glob) rfl ref _ _ hval (.inr fun _ => rfl)]
      have hnone : σ.storage.push ref (fun _ => (none : Option (SVal E))) = none := by
        simp only [Storage.push]
        cases σ.storage.find ref <;> rfl
      rw [hnone]
      rfl

theorem pop_agrees {E : Ty} (b : SPath C Γ (.array E)) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (TRun.pop b σ)
      ((Upd.nil.snoc (.storage (.app2 (if E.isMapping then .shrink else .pop)
        .storage b.lower))).apply σ.erase) := by
  have e : (Upd.nil.snoc (.storage (.app2 (if E.isMapping then .shrink else .pop)
      .storage b.lower))).apply σ.erase = (do
      let (root, segs) ← b.lower.eval σ.erase
      σ.erase.withGlob <$> popAt σ.erase.glob E.isMapping root segs) := by
    rw [upd1_apply]
    by_cases hE : E.isMapping = true
    · rw [if_pos hE]
      show (do
        let st ← Op2.eval σ.erase.glob .shrink (pure σ.erase.glob) (b.lower.eval σ.erase)
        pure (σ.erase.withGlob { σ.erase.glob with storage := st.storage })) = _
      simp only [Op2.eval, hE, bind_assoc, pure_bind]
      congr 1; funext q
      exact storage_glob σ.erase _ (Solidity.popAt_with _ _ _ _)
    · have hE' : E.isMapping = false := by simpa only [Bool.not_eq_true] using hE
      rw [if_neg hE]
      show (do
        let st ← Op2.eval σ.erase.glob .pop (pure σ.erase.glob) (b.lower.eval σ.erase)
        pure (σ.erase.withGlob { σ.erase.glob with storage := st.storage })) = _
      simp only [Op2.eval, hE', bind_assoc, pure_bind]
      congr 1; funext q
      exact storage_glob σ.erase _ (Solidity.popAt_with _ _ _ _)
  rw [e]
  refine TRes.Agrees.bind (SPath.lower_resolveT σ b) fun ref => ?_
  show TRes.Agrees _ (do
      let st ← TRes.ofOpt (σ.storage.pop E.isMapping ref)
      pure (⟨σ.withStorage st, List.prefix_refl _⟩ : Out C σ.H Γ))
    (σ.erase.withGlob <$> popAt σ.erase.glob E.isMapping ref.root ref.path.erase)
  rw [Storage.popAt_erase (σ := σ.erase.glob) rfl E.isMapping ref]
  cases σ.storage.pop E.isMapping ref <;> rfl

theorem rebindPush_agrees {R : RefTy} (i : Idx Γ (.alias R)) (b : SPath C Γ (.array (.ref R)))
    (hd : (Ty.ref R).defaultOkS = true) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (TRun.rebind i (.push b hd) σ)
      (((Upd.nil.snoc (.storage (.app2 (.extend (.ref R)) .storage b.lower))).snoc
        (.local i (.path (.app1 .next rfl b.lower)))).apply σ.erase) := by
  have e : ((Upd.nil.snoc (.storage (.app2 (.extend (.ref R)) .storage b.lower))).snoc
      (.local i (.path (.app1 .next rfl b.lower)))).apply σ.erase = (do
      let (root, segs) ← b.lower.eval σ.erase
      let (τ, n) ← pushPlaceAt σ.erase.glob (.ref R) root segs
      pure ((σ.erase.withGlob τ).setLocal i (some (root, segs ++ [.at n])))) := by
    rw [upd2_apply]
    simp only [UpdElem.write, Rhs.eval, Tm.eval, Op2.eval, Op1.eval, Op0.eval, pushPlaceAt,
      SemanticsProperties.State.saveStorage_eq, bind_assoc, pure_bind]
    simp only [bind, Except.bind, pure, Except.pure]
    cases b.lower.eval σ.erase with
    | error => rfl
    | ok q =>
      simp only
      cases σ.erase.glob.findStorage q.1 q.2 with
      | error => rfl
      | ok v =>
        cases v with
        | array elems shadow fx =>
          simp only
          cases σ.erase.glob.storeRes q.1 q.2 _ <;> rfl
        | _ => rfl
  rw [e]
  simp only [TRun.rebind, ARhs.evalT, bind_assoc]
  refine TRes.Agrees.bind (SPath.lower_resolveT σ b) fun r => ?_
  show TRes.Agrees _ ((if σ.storage.full r then .error .exhausted else do
        let (st, n) ← TRes.ofOpt (σ.storage.pushPlace r)
        pure (st, r.index (.arr .dyn) n)) >>= fun x =>
      pure (⟨(σ.withStorage x.1).setLocal i (some x.2), List.prefix_refl _⟩ : Out C σ.H Γ))
    (do
      let (τ, n) ← pushPlaceAt σ.erase.glob (.ref R) r.root r.path.erase
      pure ((σ.erase.withGlob τ).setLocal i (some (r.root, r.path.erase ++ [.at n]))))
  cases hfull : σ.storage.full r
  · rw [if_neg Bool.false_ne_true]
    rw [Storage.pushPlaceAt_erase (σ := σ.erase.glob) rfl r hfull]
    cases σ.storage.pushPlace r with
    | none => rfl
    | some x =>
      refine TRes.Agrees.of_eq (congrArg Except.ok ?_)
      rw [State.setLocal_erase]
      show (σ.withStorage x.1).erase.setLocal i (some (r.root, r.path.erase ++ [.at (x.2 : Int)])) =
        (σ.withStorage x.1).erase.setLocal i (some (r.index (.arr .dyn) x.2).erase)
      rw [SRef.erase_index]
  · trivial

theorem transferBox_agrees (sadr se : Simple C Γ .uint) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (TRun.transfer (.simple sadr) (.simple se) σ)
      ((Upd.nil.snoc (.payTo sadr se)).apply σ.erase) := by
  show TRes.Agrees _
    (.ok (⟨σ.pay (sadr.evalT σ).1 (se.evalT σ).1, List.prefix_refl _⟩ : Out C σ.H Γ)) _
  refine TRes.Agrees.of_eq ?_
  rw [upd1_apply]
  simp only [UpdElem.write, Simple.lower_evalT, PrimTy.asInt_erase_uint, Res.bind_ok,
    if_neg (Int.not_lt.mpr (PrimTy.uint_nonneg (se.evalT σ)))]
  rfl

/-- `pv = a.send(v);`'s outcome, by the updates of `sendNoCallback*`. -/
theorem send_sim (pv : Idx Γ (.val .bool)) (sadr se : Simple C Γ .uint) :
    ∃ U ∈ [(Upd.nil.snoc (.payTo sadr se)).snoc (.local pv (.val (Tm.lit (.bool true)))),
        Upd.nil.snoc (.local pv (.val (Tm.lit (.bool false))))],
      Res.Sim (U.apply σ.erase)
        (.ok (sendT σ pv (sadr.evalT σ).1 (se.evalT σ).1).st.erase) := by
  have hk := PrimTy.uint_nonneg (se.evalT σ)
  have e₁ : ((Upd.nil.snoc (.payTo sadr se)).snoc
      (.local pv (.val (Tm.lit (.bool true))))).apply σ.erase =
        .ok ((σ.pay (sadr.evalT σ).1 (se.evalT σ).1).setLocal pv (true : Bool)).erase := by
    rw [upd2_apply, State.setLocal_erase]
    simp only [UpdElem.write, Rhs.eval, Tm.eval, Op0.eval, Simple.lower_evalT,
      PrimTy.asInt_erase_uint, Res.bind_ok, if_neg (Int.not_lt.mpr hk)]
    rfl
  have e₂ : (Upd.nil.snoc (.local pv (.val (Tm.lit (C := C) (Γ := Γ) (.bool false))))).apply
      σ.erase = .ok (σ.setLocal pv (false : Bool)).erase := by
    rw [State.setLocal_erase]; rfl
  unfold sendT
  cases Semantics.lookupBy (sendKey (sadr.evalT σ).1 (se.evalT σ).1) σ.tx.ext with
  | none => exact ⟨_, List.mem_cons_self .., by rw [e₁]; exact Res.Sim.refl _⟩
  | some x =>
    cases x with
    | ok => exact ⟨_, List.mem_cons_self .., by rw [e₁]; exact Res.Sim.refl _⟩
    | _ =>
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by rw [e₂]; exact Res.Sim.refl _⟩

theorem declMemFresh_agrees (R : RefTy) (x : Var) (hm : (Ty.ref R).mapFree = true) :
    TRes.Agrees (fun o : Out C σ.H (.mem R :: Γ) => o.st.erase) (TRun.declMem R none hm σ)
      (((Upd.nil.decl x (.mref (.app1 (.alloc R) rfl .memory))).snoc
        (.memory (.app1 (.addM R) rfl .memory))).apply σ.erase) := by
  have e : ((Upd.nil.decl x (.mref (.app1 (.alloc R) rfl .memory))).snoc
      (.memory (.app1 (.addM R) rfl .memory))).apply σ.erase = (do
      let (τ', id) ← Semantics.allocDefault σ.erase.glob R
      pure ((σ.erase.withGlob τ').push (t := .mem R) (some id))) := by
    show (do
      let τ ← (Upd.nil.decl x (.mref (.app1 (.alloc R) rfl .memory))).apply σ.erase
      UpdElem.write σ.erase (.memory (.app1 (.addM R) rfl .memory)) τ) = _
    simp only [Upd.apply, UpdElem.write, Rhs.eval, Tm.eval, Op1.eval, Op0.eval,
      Solidity.allocDefault_eq, bind_assoc, pure_bind]
    simp only [bind, Except.bind, pure, Except.pure]
    cases Solidity.allocHN σ.erase.glob R <;> rfl
  rw [e, State.allocDefault_erase σ R hm, ok_bind]
  refine TRes.Agrees.of_eq (congrArg Except.ok ?_)
  show _ = ((σ.allocDefault R hm).1.push (t := .mem R) (some (σ.allocDefault R hm).2)).erase
  rw [State.push_erase, ← TRun.State.allocDefault_glob]
  rfl

theorem deleteMemVar_agrees {R : RefTy} (i : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (TRun.deleteMem (.var i hm) σ)
      (((Upd.nil.snoc (.local i (.mref (.app1 (.alloc R) rfl .memory)))).snoc
        (.memory (.app1 (.addM R) rfl .memory))).apply σ.erase) := by
  have e : ((Upd.nil.snoc (.local i (.mref (.app1 (.alloc R) rfl .memory)))).snoc
      (.memory (.app1 (.addM R) rfl .memory))).apply σ.erase = (do
      let (τ', id) ← Semantics.allocDefault σ.erase.glob R
      pure ((σ.erase.withGlob τ').setLocal i (some id))) := by
    rw [upd2_apply]
    simp only [UpdElem.write, Rhs.eval, Tm.eval, Op1.eval, Op0.eval,
      Solidity.allocDefault_eq, bind_assoc, pure_bind]
    simp only [bind, Except.bind, pure, Except.pure]
    cases Solidity.allocHN σ.erase.glob R <;> rfl
  rw [e, State.allocDefault_erase σ _ hm, ok_bind]
  refine TRes.Agrees.of_eq (congrArg Except.ok ?_)
  show _ = ((σ.allocDefault _ hm).1.setLocal i (some (σ.allocDefault _ hm).2)).erase
  rw [State.setLocal_erase, ← TRun.State.allocDefault_glob]
  rfl

theorem allocCopy_agrees {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) (v : Tm C Γ .sv)
    (hr : TRes.Agrees (fun g : Grew C Γ σ.H (HRef · R) => (g.st.erase, (g.val : HRef _ R).id))
      (r.evalT σ) (do
        let (τ, mv) ← Semantics.copyStToM σ.erase.glob (← v.eval σ.erase)
        pure (σ.erase.withGlob τ, ← mv.asRef))) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (TRun.rebindMem i r σ)
      (((Upd.nil.snoc (.local i (.mref (.app2 .copy .memory v)))).snoc
        (.memory (.app2 .copySt .memory v))).apply σ.erase) := by
  have e : ((Upd.nil.snoc (.local i (.mref (.app2 .copy .memory v)))).snoc
      (.memory (.app2 .copySt .memory v))).apply σ.erase = (do
      let (τ', id) ← (do
        let (τ, mv) ← Semantics.copyStToM σ.erase.glob (← v.eval σ.erase)
        pure (σ.erase.withGlob τ, ← mv.asRef))
      pure (τ'.setLocal i (some id))) := by
    rw [upd2_apply]
    simp only [UpdElem.write, Rhs.eval, Tm.eval, Op2.eval, Op0.eval,
      Solidity.copyStToM_eq, bind_assoc, pure_bind]
    simp only [bind, Except.bind, pure, Except.pure]
    cases v.eval σ.erase with
    | error => rfl
    | ok sv =>
      simp only
      cases Solidity.copyHN σ.erase.glob sv with
      | error => rfl
      | ok q =>
        simp only
        cases q.2.2.asRef <;> rfl
  rw [e]
  exact TRes.Agrees.bind hr fun g =>
    TRes.Agrees.of_eq (congrArg Except.ok (State.setLocal_erase g.st i (some g.val)).symm)

/-- `memoryStorageCopy`'s right-hand side: a deep copy of `sfind(storage, p)`. -/
theorem allocCopy_copy {R : RefTy} (p : SPath C Γ (.ref R)) (hm : (Ty.ref R).mapFree = true) :
    TRes.Agrees (fun g : Grew C Γ σ.H (HRef · R) => (g.st.erase, (g.val : HRef _ R).id))
      ((MRhs.copy p hm).evalT σ) (do
        let (τ, mv) ← Semantics.copyStToM σ.erase.glob
          (← (Tm.app2 .sfind .storage p.lower : Tm C Γ .sv).eval σ.erase)
        pure (σ.erase.withGlob τ, ← mv.asRef)) := by
  show TRes.Agrees _ _ (do
    let sv ← (do
      let τ ← pure σ.erase.glob
      let (r, segs) ← p.lower.eval σ.erase
      τ.findStorage r segs)
    let (τ, mv) ← Semantics.copyStToM σ.erase.glob sv
    pure (σ.erase.withGlob τ, ← mv.asRef))
  simp only [pure_bind, bind_assoc]
  refine TRes.Agrees.bind (SPath.lower_resolveT σ p) fun r => ?_
  show TRes.Agrees _ (do
      let sv ← TRes.ofOpt (σ.storage.find r)
      let g := σ.copyStToMG sv hm
      pure (⟨g.st, g.ext, g.val⟩ : Grew C Γ σ.H (HRef · R)))
    (do
      let sv ← σ.erase.glob.findStorage r.root r.path.erase
      let (τ, mv) ← Semantics.copyStToM σ.erase.glob sv
      pure (σ.erase.withGlob τ, ← mv.asRef))
  rw [Storage.findStorage_erase (σ := σ.erase.glob) rfl r]
  refine TRes.Agrees.bind (TRes.Agrees.ofOpt _) fun sv => ?_
  rw [State.copyStToM_erase σ sv hm]
  exact TRes.Agrees.of_eq (by
    show Except.ok (σ.erase.withGlob (σ.copyStToM sv hm).1.erase.glob, _) = _
    rw [State.copyStToM, State.withGlob_adopt]
    rfl)

/-- `memoryArrayFreshAlloc`'s right-hand side: `newArr(R, n)` copied. -/
theorem allocCopy_newArr {R : RefTy} (n : Simple C Γ .uint) (h : R.newArrOk = true) :
    TRes.Agrees (fun g : Grew C Γ σ.H (HRef · R) => (g.st.erase, (g.val : HRef _ R).id))
      ((MRhs.newArr n h).evalT σ) (do
        let (τ, mv) ← Semantics.copyStToM σ.erase.glob
          (← (Tm.app1 (.newArr R) rfl n.lower : Tm C Γ .sv).eval σ.erase)
        pure (σ.erase.withGlob τ, ← mv.asRef)) := by
  show TRes.Agrees _ _ (do
    let sv ← (do pure (newArrVal R (← (← n.lower.eval σ.erase).asInt)))
    let (τ, mv) ← Semantics.copyStToM σ.erase.glob sv
    pure (σ.erase.withGlob τ, ← mv.asRef))
  rw [Simple.lower_evalT σ n, ok_bind, PrimTy.asInt_erase_uint, ok_bind, pure_bind,
    ← newArrT_erase R _ h]
  rw [State.copyStToM_erase σ _ (RefTy.mapFree_of_newArrOk h)]
  exact TRes.Agrees.of_eq (by
    show Except.ok (σ.erase.withGlob (σ.copyStToM _ _).1.erase.glob, _) = _
    rw [State.copyStToM, State.withGlob_adopt]
    rfl)

/-- `delete l` at a memory location: the slot reset to its default, or
written a fresh default object, up to the halt (the update allocates before
it reads the address). -/
theorem clearMem_sim {T : Ty} (l : MLoc C Γ T) (hd : T.defaultOkS = true) :
    ∃ U, Premise.clearMem l.lower T = .update U ∧
      Res.Sim (U.apply σ.erase)
        (do σ.erase.withGlob <$> memClear σ.erase.glob (← l.lower.eval σ.erase) T) := by
  cases T with
  | prim p =>
    refine ⟨_, rfl, Res.Sim.of_eq ?_⟩
    rw [upd1_apply]
    show _ = _
    simp only [UpdElem.write, Tm.eval, Op3.eval, Op1.eval, Op0.eval, memClear, bind_assoc,
      pure_bind, writeAddr_glob]
  | ref R =>
    refine ⟨_, rfl, ?_⟩
    rw [upd1_apply]
    simp only [UpdElem.write, Tm.eval, Op3.eval, Op1.eval, Op0.eval, memClear,
      Solidity.allocDefault_eq, bind_assoc, pure_bind]
    simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
    have ha : NoPanic (l.lower.eval σ.erase) := Tm.eval_noPanic σ.erase l.lower
    have hal : NoPanic (Solidity.allocHN σ.erase.glob R) := Solidity.allocHN_noPanic σ.erase.glob R
    revert ha hal
    cases l.lower.eval σ.erase with
    | error e =>
      cases Solidity.allocHN σ.erase.glob R with
      | error e' => exact fun ha hal => ⟨fun h => absurd (congrArg Except.error h) hal,
          fun h => absurd (congrArg Except.error h) ha⟩
      | ok q => intro _ _; exact Res.Sim.refl _
    | ok a =>
      cases Solidity.allocHN σ.erase.glob R with
      | error e' => intro _ _; exact Res.Sim.refl _
      | ok q =>
        intro _ _
        simp only
        cases hw : writeAddr _ _ a with
        | error => exact Res.Sim.refl _
        | ok μ =>
          simp only [writeAddr_ok_with hw]
          exact Res.Sim.refl _

end Agrees2

/-! ## The other update arms (`Step.lean`) -/

section Arms2

variable {Γ : Ctx} {m : Modality} (σ : State C Γ)

/-- `storagePushLengthSave`: `{storage := pushSlot(storage, b)}`. -/
theorem sound_pushSlot {E : Ty} (b : SPath C Γ (.array E))
    (hd : (none.isSome || E.defaultOkS) = true) :
    Premise.Runs m (.push b none hd) (.upd1 (.storage (.app2 (.pushSlot E) .storage b.lower))) σ :=
  Premise.sound_update_typed σ (pushSlot_agrees σ b) fun _ => TRun.push_nd σ b none

/-- `storagePushLengthSaveReferenceElement`: `{storage := extend(storage, b)}`. -/
theorem sound_extend {E : Ty} (b : SPath C Γ (.array E))
    (hd : (none.isSome || E.defaultOkS) = true) :
    Premise.Runs m (.push b none hd) (.upd1 (.storage (.app2 (.extend E) .storage b.lower))) σ :=
  Premise.sound_update_typed σ (extend_agrees σ b) fun _ => TRun.push_nd σ b none

/-- `storagePushValueSave`, `storagePushValueCopySource`:
`{storage := push(storage, b, src)}`. -/
theorem sound_pushSome {E : Ty} (b : SPath C Γ (.array E)) (r : Src C Γ E)
    (hd : ((some r).isSome || E.defaultOkS) = true) :
    Premise.Runs m (.push b (some r) hd)
      (.upd1 (.storage (.app3 .push .storage b.lower r.lower))) σ :=
  Premise.sound_update_typed σ (pushSome_agrees σ b r) fun _ => TRun.push_nd σ b (some r)

/-- `storagePopSave`, `storagePopSaveMappingElement`. -/
theorem sound_pop {E : Ty} (b : SPath C Γ (.array E)) :
    Premise.Runs m (.pop b) (.upd1 (.storage (.app2 (if E.isMapping then .shrink else .pop)
      .storage b.lower))) σ :=
  Premise.sound_update_typed σ (pop_agrees σ b) fun _ =>
    ((SPath.resolveT_ends σ b).bind fun _ => (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _).1

/-- `storageLocalRootPushBind`, `storageLocalRootPushBindMappingElement`:
`{storage := extend(storage, b) ‖ lsv := next(b)}`. -/
theorem sound_rebindPush {R : RefTy} (i : Idx Γ (.alias R)) (b : SPath C Γ (.array (.ref R)))
    (hd : (Ty.ref R).defaultOkS = true) :
    Premise.Runs m (.rebind i (.push b hd)) (.update ((Upd.nil.snoc
      (.storage (.app2 (.extend (.ref R)) .storage b.lower))).snoc
      (.local i (.path (.app1 .next rfl b.lower))))) σ :=
  Premise.sound_update_typed σ (rebindPush_agrees σ i b hd) fun _ =>
    TRes.NoDiv.bind (ARhs.evalT_nd σ (.push b hd)) fun _ => TRes.NoDiv.ok _

/-- `transferNoCallbackBox`: `{net := …}`. -/
theorem sound_transferBox (sadr se : Simple C Γ .uint) :
    Premise.Runs m (.transfer (.simple sadr) (.simple se)) (.upd1 (.payTo sadr se)) σ :=
  Premise.sound_update_typed σ (transferBox_agrees σ sadr se) fun _ => TRes.NoDiv.ok _

/-- `transferDiamond` (Lean): the goal fails. -/
theorem sound_done_false {Γ' : Ctx} (s : Stmt C Γ Γ') : Premise.Sound m s (.done false) σ :=
  Premise.sound_done σ false fun h => nomatch h

/-- `sendNoCallbackBox`, `sendNoCallbackDiamond`: the payment with `pv` true,
or `pv` false. -/
theorem sound_send (pv : Idx Γ (.val .bool)) (sadr se : Simple C Γ .uint) (fs : List (Fml C Γ)) :
    Premise.Sound m (.send pv (.simple sadr) (.simple se)) (.cases fs
      [(Upd.nil.snoc (.payTo sadr se)).snoc (.local pv (.val (Tm.lit (.bool true)))),
        Upd.nil.snoc (.local pv (.val (Tm.lit (.bool false))))]) σ :=
  Premise.sound_cases_typed (s := .send pv (.simple sadr) (.simple se))
    (t := TRun.send pv (.simple sadr) (.simple se)) σ (TRes.Agrees.pure _)
    (fun _ => send_sim σ pv sadr se) fun _ => TRes.NoDiv.ok _

/-- `memoryReferenceDeclFreshAlloc`. -/
theorem sound_declMemFresh (R : RefTy) (x : Var)
    (hd : (none.isSome || (Ty.ref R).defaultOkS) = true) (hm : (Ty.ref R).mapFree = true) :
    Premise.Runs m (.declMem R x none hd hm) (.update ((Upd.nil.decl x
      (.mref (.app1 (.alloc R) rfl .memory))).snoc (.memory (.app1 (.addM R) rfl .memory)))) σ :=
  Premise.sound_update_typed σ (declMemFresh_agrees σ R x hm) fun _ => TRes.NoDiv.ok _

/-- `memoryRootDeleteFreshRebind`. -/
theorem sound_deleteMemVar {R : RefTy} (i : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    (hd : (Ty.ref R).defaultOkS = true) :
    Premise.Runs m (.deleteMem (.var i hm) hd) (.update ((Upd.nil.snoc
      (.local i (.mref (.app1 (.alloc R) rfl .memory)))).snoc
      (.memory (.app1 (.addM R) rfl .memory)))) σ :=
  Premise.sound_update_typed σ (deleteMemVar_agrees σ i hm) fun _ => TRes.NoDiv.ok _

/-- `memoryStorageCopy`, `memoryArrayFreshAlloc`, given the right-hand
side's typed evaluation against the copy on the erasure (`allocCopy_copy`,
`allocCopy_newArr`). -/
theorem sound_allocCopy {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) (v : Tm C Γ .sv)
    (hr : TRes.Agrees (fun g : Grew C Γ σ.H (HRef · R) => (g.st.erase, (g.val : HRef _ R).id))
      (r.evalT σ) (do
        let (τ, mv) ← Semantics.copyStToM σ.erase.glob (← v.eval σ.erase)
        pure (σ.erase.withGlob τ, ← mv.asRef))) :
    Premise.Runs m (.rebindMem i r) (.allocCopy i v) σ :=
  Premise.sound_update_typed σ (allocCopy_agrees σ i r v hr) fun _ =>
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
  obtain ⟨U, hU, hs⟩ := clearMem_sim σ l hd
  rw [hU]
  exact Premise.sound_updateSim_typed (t := TRun.deleteMem (.loc l)) σ
    (TRes.Agrees.bind (MLoc.lower_addrT σ l) fun a => TRun.clearT_erase σ a l.mapFree) hs
    fun _ => ((MLoc.addrT_ends σ l).bind fun a => clearT_ends σ a _).1

/-- `valueDeclSkip`: `{v := defVal(T)}`. -/
theorem sound_valueDeclSkip (p : PrimTy) (x : Var) :
    Premise.Runs m (.declLocal p x none)
      (.update (Upd.nil.decl x (.val (p := p) (.app0 (.lit p.default))))) σ :=
  Premise.sound_update_typed (s := .declLocal p x none) (t := TRun.declLocal p none) σ
    (TRes.Agrees.of_eq (congrArg Except.ok (by
      show σ.erase.push (PrimTy.default p) = (σ.push (t := .val p) (PrimTy.dflt p)).erase
      rw [← PrimTy.erase_dflt]; rfl)))
    fun _ => TRes.NoDiv.ok _

/-- `storageLocalDeclSkip`: `{lsv := unset}`. -/
theorem sound_storageLocalDeclSkip (R : RefTy) (x : Var) :
    Premise.Runs m (.declStorage R x none) (.update (Upd.nil.decl (t := .alias R) x .unset)) σ :=
  Premise.sound_update_typed (s := .declStorage R x none) (t := TRun.declStorage R none) σ
    (TRes.Agrees.pure _) fun _ => TRes.NoDiv.ok _

/-- `revertBox`, `revertDiamond`. -/
theorem sound_revert :
    Premise.Sound m (.revert : Stmt C Γ Γ) (.done (m == .box)) σ :=
  Premise.sound_done σ _ fun h =>
    ⟨by cases m <;> first | rfl | exact absurd h (by decide), .revert, rfl, by decide⟩

end Arms2

end Solidity
