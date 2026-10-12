import Solidity.Calculus.SoundKit
import Solidity.Theory.StateWrites

/-!
# Soundness of the update arms

The rules of `Calculus/Arms.lean` and `Step.lean` whose premise is an
update (`Premise.Sound`, `Calculus/ProvesSound.lean`).  An update is a
term of `Update.lean`, computed on the typed state as a global part and the
locals' values (`Upd.applyV`), so each arm states that the statement's
typed step (`TRun.*`, `Semantics/Run.lean`) agrees with what the update
computes in the state it starts in (`*_agrees`, `TRes.Agrees` against
`State.globE` and `State.loc`), and closes with `Premise.sound_update_typed`
(`Calculus/SoundKit.lean`).  An agreement composes the evaluators' (the
typed evaluator against the lowered term, `Calculus/LowerRun.lean`) with
the write's (`Semantics/StorageErase.lean`, `Semantics/HeapErase.lean`),
after an equation that reads the update's terms in the order the statement
reads them (`Theory/StateWrites.lean`'s frame lemmas, on `σ.globE`).

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

/-! ## Updates computed: the terms in the statement's order

The update reads its right-hand sides in the state it is applied in, the
statement left to right; both reach the same writes through the same reads,
and a write of the storage (the heap) changes nothing else
(`Theory/StateWrites.lean`'s `*_with`).  Each equation leaves the
statement's locations as terms (`P`, `A`), read once. -/

section Updates

variable {Γ : Ctx} (σ : State C Γ)

/-- A storage write through the term: the global part with the storage it
leaves, the locals kept. -/
theorem storage_glob (x : Res Semantics.State)
    (hx : (x >>= fun τ => pure { σ.globE with storage := τ.storage }) = x) :
    (x >>= fun st => pure ({ σ.globE with storage := st.storage }, σ.loc)) = (·, σ.loc) <$> x := by
  conv => rhs; rw [← hx]
  cases x <;> rfl

/-- A heap write through the term. -/
theorem memory_glob (x : Res Semantics.State)
    (hx : (x >>= fun μ => pure { σ.globE with heap := μ.heap, nextId := μ.nextId }) = x) :
    (x >>= fun μ => pure ({ σ.globE with heap := μ.heap, nextId := μ.nextId }, σ.loc)) =
      (·, σ.loc) <$> x := by
  conv => rhs; rw [← hx]
  cases x <;> rfl

theorem upd1_applyV (e : UpdElem C Γ Γ) :
    (Upd.nil.snoc e).applyV σ = e.applyV σ σ.globE σ.loc := rfl

theorem upd2_applyV (e₁ e₂ : UpdElem C Γ Γ) :
    ((Upd.nil.snoc e₁).snoc e₂).applyV σ =
      (do let q ← e₁.applyV σ σ.globE σ.loc; e₂.applyV σ q.1 q.2) := rfl

/-- A `storage :=` element, computed. -/
theorem storage_applyV {Δ : Ctx} (s : Tm C Γ .st) (g : Semantics.State) (ℓ : Locs C Δ) :
    (UpdElem.storage s : UpdElem C Γ Δ).applyV σ g ℓ =
      (s.eval σ >>= fun st => pure ({ g with storage := st.storage }, ℓ)) := by
  simp only [UpdElem.applyV, UpdElem.globT]
  cases s.eval σ <;> rfl

/-- A `memory :=` element, computed. -/
theorem memory_applyV {Δ : Ctx} (m : Tm C Γ .mem) (g : Semantics.State) (ℓ : Locs C Δ) :
    (UpdElem.memory m : UpdElem C Γ Δ).applyV σ g ℓ =
      (m.eval σ >>= fun μ => pure ({ g with heap := μ.heap, nextId := μ.nextId }, ℓ)) := by
  simp only [UpdElem.applyV, UpdElem.globT]
  cases m.eval σ <;> rfl

/-- A local's element, computed. -/
theorem local_applyV {Δ : Ctx} {t : LTy} (i : Idx Δ t) (r : Rhs C Γ t) (g : Semantics.State)
    (ℓ : Locs C Δ) :
    (UpdElem.local i r : UpdElem C Γ Δ).applyV σ g ℓ = (r.eval σ >>= fun v => pure (g, ℓ.set i v)) :=
  rfl

/-- A typed state with a local set, read as an update computes it. -/
theorem pair_setLocal {t : LTy} (i : Idx Γ t) (v : t.TDenote C σ.H) :
    ((σ.setLocal i v).globE, (σ.setLocal i v).loc) = (σ.globE, σ.loc.set i (LTy.TDenote.erase t v)) := by
  rw [State.loc_setLocal]; rfl

theorem Res.bind_ok {α β : Type} (a : α) (f : α → Res β) : ((Except.ok a : Res α) >>= f) = f a :=
  rfl

theorem writeStorage_toSVal (s : Semantics.State) (r : Name) (segs : List Seg) (v : Value) :
    s.writeStorage r segs v.toSVal = s.saveStorage r segs v.toSVal := by
  cases v <;> rfl

/-- A storage save through the term, as the statement's write. -/
theorem saveStorage_glob (r : Name) (segs : List Seg) (v : Semantics.SVal) :
    (σ.globE.saveStorage r segs v >>= fun d =>
      pure ({ σ.globE with storage := d.storage }, σ.loc)) =
      (·, σ.loc) <$> σ.globE.saveStorage r segs v :=
  storage_glob σ _ (Semantics.State.saveStorage_with _ _ _ _)

/-- A heap write through the term, as the statement's write. -/
theorem writeAddr_glob (mv : Semantics.MVal) (a : Semantics.Addr) :
    (writeAddr σ.globE mv a >>= fun μ =>
      pure ({ σ.globE with heap := μ.heap, nextId := μ.nextId }, σ.loc)) =
      (·, σ.loc) <$> writeAddr σ.globE mv a :=
  memory_glob σ _ (Solidity.writeAddr_with _ _ _)

theorem bind_withGlob (x : Res Semantics.State) :
    (x >>= fun τ => pure (τ, σ.loc)) = (·, σ.loc) <$> x := by
  cases x <;> rfl

theorem writeAddr_ok_with {s x : Semantics.State} {mv : Semantics.MVal} {a : Semantics.Addr}
    (h : writeAddr s mv a = .ok x) : { s with heap := x.heap, nextId := x.nextId } = x := by
  have e := Solidity.writeAddr_with s mv a
  rw [h] at e
  exact Except.ok.inj e

/-- A global step's state and value, with the locals. -/
def glob₂ (x : Semantics.State × Value) : (Semantics.State × Locs C Γ) × Value :=
  ((x.1, σ.loc), x.2)

/-- `storage := save(storage, P, P ⊕ t)`: the compound write at the path. -/
theorem save_compound {op : BinOp} (hop : op.hasCompoundAssign = true) (p : PrimTy)
    (P : Tm C Γ .path) (t : Tm C Γ .val) {w : Value} (ht : t.eval σ = .ok w) :
    (UpdElem.storage (.app3 .save .storage P
      (.app1 .sval rfl (.app2 (.binop op p) (.app2 .find .storage P) t)))).applyV σ σ.globE σ.loc =
      (do
        let (rt, segs) ← P.eval σ
        (·, σ.loc) <$> opStore σ.globE op p rt segs w) := by
  rw [storage_applyV]
  simp only [Tm.eval, Op3.eval, Op2.eval, Op1.eval, Op0.eval,
    evalBinop_compound hop, ht, opStore, bind_assoc, pure_bind, writeStorage_toSVal,
    saveStorage_glob, map_bind]
  cases P.eval σ <;> rfl

/-- `memory := write(memory, A, A ⊕ t)`: the compound write at the address. -/
theorem write_compound {op : BinOp} (hop : op.hasCompoundAssign = true) (p : PrimTy)
    (A : Tm C Γ .addr) (t : Tm C Γ .val) {w : Value} (ht : t.eval σ = .ok w) :
    (UpdElem.memory (.app3 .write .memory A
      (.app1 .mval rfl (.app2 (.binop op p) (.app2 .read .memory A) t)))).applyV σ σ.globE σ.loc =
      (do (·, σ.loc) <$> opMem σ.globE op p (← A.eval σ) w) := by
  rw [memory_applyV]
  simp only [Tm.eval, Op3.eval, Op2.eval, Op1.eval, Op0.eval,
    evalBinop_compound hop, ht, opMem, Solidity.readLoc_eq, Semantics.writeLoc_eq, bind_assoc,
    pure_bind, writeAddr_glob, map_bind]
  cases A.eval σ <;> rfl

/-- `storage := save(storage, P, P ± 1)`: the bump at the path. -/
theorem save_bump (op : IncDec) (p : PrimTy) (P : Tm C Γ .path) :
    (UpdElem.storage (.app3 .save .storage P
      (.app1 .sval rfl (.app2 (.binop op.binOp p) (.app2 .find .storage P) Tm.one)))).applyV σ
      σ.globE σ.loc =
      ((do
        let (rt, segs) ← P.eval σ
        glob₂ σ <$> bumpStore σ.globE op p rt segs) >>= fun y => pure y.1) := by
  rw [storage_applyV]
  simp only [Tm.eval, Op3.eval, Op2.eval, Op1.eval, Op0.eval,
    evalBinop_bump, Solidity.applyBinOp_bump, bumpStore, bind_assoc, pure_bind,
    writeStorage_toSVal, saveStorage_glob, map_bind, map_pure, glob₂, bind_withGlob]
  cases P.eval σ <;> rfl

/-- `memory := write(memory, A, A ± 1)`: the bump at the address. -/
theorem write_bump (op : IncDec) (p : PrimTy) (A : Tm C Γ .addr) :
    (UpdElem.memory (.app3 .write .memory A
      (.app1 .mval rfl (.app2 (.binop op.binOp p) (.app2 .read .memory A) Tm.one)))).applyV σ
      σ.globE σ.loc =
      ((do glob₂ σ <$> bumpMem σ.globE op p (← A.eval σ)) >>= fun y => pure y.1) := by
  rw [memory_applyV]
  simp only [Tm.eval, Op3.eval, Op2.eval, Op1.eval, Op0.eval,
    evalBinop_bump, Solidity.applyBinOp_bump, bumpMem, Solidity.readLoc_eq,
    Semantics.writeLoc_eq, bind_assoc, pure_bind, writeAddr_glob, map_bind, map_pure, glob₂,
    bind_withGlob]
  cases A.eval σ <;> rfl

/-- The value `x++` gives at a path is what `bumped(find(storage, P))` reads in
the state before. -/
theorem bumped_find (op : IncDec) (p : PrimTy) (P : Tm C Γ .path) {q : Name × List Seg}
    (hq : P.eval σ = .ok q) {τ : Semantics.State} {v : Value}
    (hb : bumpStore σ.globE op p q.1 q.2 = .ok (τ, v)) :
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
    (hb : bumpMem σ.globE op p a = .ok (τ, v)) :
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
      (.local i (.val (Tm.bumped op p (.app2 .find .storage P))))).applyV σ =
      ((do
        let (rt, segs) ← P.eval σ
        glob₂ σ <$> bumpStore σ.globE op p rt segs) >>= fun y =>
          pure (y.1.1, y.1.2.set i y.2)) := by
  rw [upd2_applyV, save_bump, bind_assoc]
  cases hq : P.eval σ with
  | error => rfl
  | ok q =>
    obtain ⟨rt, segs⟩ := q
    show ((glob₂ σ <$> bumpStore σ.globE op p rt segs) >>= fun y => (pure y.1 : Res _) >>= _) =
      ((glob₂ σ <$> bumpStore σ.globE op p rt segs) >>= fun y => pure (y.1.1, y.1.2.set i y.2))
    cases hb : bumpStore σ.globE op p rt segs with
    | error => rfl
    | ok x =>
      obtain ⟨τ, v⟩ := x
      show (do pure (τ, σ.loc.set i
        (← (Tm.bumped op p (.app2 .find .storage P)).eval σ))) = _
      rw [bumped_find σ op p P hq hb]; rfl

/-- `{A := A ± 1 ‖ v := bumped(A)}` at an address. -/
theorem write_bump_assign (op : IncDec) (p : PrimTy) (A : Tm C Γ .addr) (i : Idx Γ (.val p)) :
    ((Upd.nil.snoc (UpdElem.memory (.app3 .write .memory A
      (.app1 .mval rfl (.app2 (.binop op.binOp p) (.app2 .read .memory A) Tm.one))))).snoc
      (.local i (.val (Tm.bumped op p (.app2 .read .memory A))))).applyV σ =
      ((do glob₂ σ <$> bumpMem σ.globE op p (← A.eval σ)) >>= fun y =>
        pure (y.1.1, y.1.2.set i y.2)) := by
  rw [upd2_applyV, write_bump, bind_assoc]
  cases ha : A.eval σ with
  | error => rfl
  | ok a =>
    show ((glob₂ σ <$> bumpMem σ.globE op p a) >>= fun y => (pure y.1 : Res _) >>= _) =
      ((glob₂ σ <$> bumpMem σ.globE op p a) >>= fun y => pure (y.1.1, y.1.2.set i y.2))
    cases hb : bumpMem σ.globE op p a with
    | error => rfl
    | ok x =>
      obtain ⟨τ, v⟩ := x
      show (do pure (τ, σ.loc.set i
        (← (Tm.bumped op p (.app2 .read .memory A)).eval σ))) = _
      rw [bumped_read σ op p A ha hb]; rfl

end Updates

/-! ## The agreements: the typed step against the update

Each update arm's typed step against what its update computes, as
`Premise.sound_update_typed` asks. -/

section Agrees

variable {Γ : Ctx} (σ : State C Γ)

theorem setLocal_agrees {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) :
    TRes.Agrees (fun o : Out C σ.H Γ => (o.st.globE, o.st.loc)) (TRun.assignLocal i v σ)
      ((Upd.nil.snoc (.local i (.val v.lower))).applyV σ) :=
  TRes.Agrees.bind (Val.lower_evalT σ v) fun x =>
    TRes.Agrees.of_eq (congrArg Except.ok (pair_setLocal σ i x).symm)

theorem save_agrees {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    TRes.Agrees (fun o : Out C σ.H Γ => (o.st.globE, o.st.loc)) (TRun.assign l r σ)
      ((Upd.nil.snoc (.storage (.app3 .save .storage l.lower r.lower))).applyV σ) := by
  have e : (Upd.nil.snoc (.storage (.app3 .save .storage l.lower r.lower))).applyV σ = (do
      let sv ← r.lower.eval σ
      let (root, segs) ← l.lower.eval σ
      (·, σ.loc) <$> σ.globE.writeStorage root segs sv) := by
    rw [upd1_applyV, storage_applyV]
    show (do
      let st ← Op3.eval σ.globE .save (pure σ.globE) (l.lower.eval σ)
        (r.lower.eval σ)
      pure (({ σ.globE with storage := st.storage }, σ.loc))) = _
    simp only [Op3.eval, bind_assoc, pure_bind]
    congr 1; funext sv; congr 1; funext q
    exact storage_glob σ _ (Semantics.State.writeStorage_with _ _ _ _)
  rw [e]
  refine TRes.Agrees.bind (Src.lower_valueT σ r) fun sv => ?_
  refine TRes.Agrees.bind (Loc.lower_resolveT σ l) fun ref => ?_
  show TRes.Agrees _ (do
      let st ← TRes.ofOpt (σ.storage.write ref sv)
      pure (⟨σ.withStorage st, List.prefix_refl _⟩ : Out C σ.H Γ))
    ((·, σ.loc) <$> σ.globE.writeStorage ref.root ref.path.erase sv.erase)
  rw [Storage.writeStorage_erase (σ := σ.globE) rfl ref sv]
  cases σ.storage.write ref sv <;> rfl

theorem saveMem_agrees {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
    TRes.Agrees (fun o : Out C σ.H Γ => (o.st.globE, o.st.loc)) (TRun.assignFromMem l p σ)
      ((Upd.nil.snoc (.storage (.app3 .save .storage l.lower
        (.app2 .copyMem .memory p.lower)))).applyV σ) := by
  have e : (Upd.nil.snoc (.storage (.app3 .save .storage l.lower
      (.app2 .copyMem .memory p.lower)))).applyV σ = (do
      let id ← p.lower.eval σ
      let sv ← Semantics.copyMem σ.globE (.ref id)
      let (root, segs) ← l.lower.eval σ
      (·, σ.loc) <$> σ.globE.writeStorage root segs sv) := by
    rw [upd1_applyV, storage_applyV]
    show (do
      let st ← Op3.eval σ.globE .save (pure σ.globE) (l.lower.eval σ)
        (Op2.eval σ.globE .copyMem (pure σ.globE) (p.lower.eval σ))
      pure (({ σ.globE with storage := st.storage }, σ.loc))) = _
    simp only [Op3.eval, Op2.eval, bind_assoc, pure_bind]
    congr 1; funext id; congr 1; funext sv; congr 1; funext q
    exact storage_glob σ _ (Semantics.State.writeStorage_with _ _ _ _)
  rw [e]
  refine TRes.Agrees.bind (MPath.lower_mvalT σ p) fun m => ?_
  show TRes.Agrees _ _ (do
    let sv ← Semantics.copyMem σ.globE (MVal.erase (.ref R) m)
    let (root, segs) ← l.lower.eval σ
    (·, σ.loc) <$> σ.globE.writeStorage root segs sv)
  rw [State.copyMem_erase (T := .ref R) σ m, ok_bind]
  refine TRes.Agrees.bind (Loc.lower_resolveT σ l) fun ref => ?_
  show TRes.Agrees _ (do
      let st ← TRes.ofOpt (σ.storage.write ref (σ.copyMToSt (T := .ref R) m))
      pure (⟨σ.withStorage st, List.prefix_refl _⟩ : Out C σ.H Γ))
    ((·, σ.loc) <$> σ.globE.writeStorage ref.root ref.path.erase
      (σ.copyMToSt (T := .ref R) m).erase)
  rw [Storage.writeStorage_erase (σ := σ.globE) rfl ref]
  cases σ.storage.write ref (σ.copyMToSt (T := .ref R) m) <;> rfl

theorem delAt_agrees {T : Ty} (l : Loc C Γ T) :
    TRes.Agrees (fun o : Out C σ.H Γ => (o.st.globE, o.st.loc)) (TRun.delete l σ)
      ((Upd.nil.snoc (.storage (.app2 .delAt .storage l.lower))).applyV σ) := by
  have e : (Upd.nil.snoc (.storage (.app2 .delAt .storage l.lower))).applyV σ = (do
      let (root, segs) ← l.lower.eval σ
      let cur ← σ.globE.findStorage root segs
      (·, σ.loc) <$> σ.globE.saveStorage root segs cur.defaultOf) := by
    rw [upd1_applyV, storage_applyV]
    show (do
      let st ← Op2.eval σ.globE .delAt (pure σ.globE) (l.lower.eval σ)
      pure (({ σ.globE with storage := st.storage }, σ.loc))) = _
    simp only [Op2.eval, bind_assoc, pure_bind]
    congr 1; funext q; congr 1; funext cur
    exact storage_glob σ _ (Semantics.State.saveStorage_with _ _ _ _)
  rw [e]
  refine TRes.Agrees.bind (Loc.lower_resolveT σ l) fun ref => ?_
  show TRes.Agrees _ (do
      let st ← TRes.ofOpt (σ.storage.delete ref)
      pure (⟨σ.withStorage st, List.prefix_refl _⟩ : Out C σ.H Γ))
    (do
      let cur ← σ.globE.findStorage ref.root ref.path.erase
      (·, σ.loc) <$> σ.globE.saveStorage ref.root ref.path.erase cur.defaultOf)
  rw [← map_bind, Storage.delete_erase (σ := σ.globE) rfl ref]
  cases σ.storage.delete ref <;> rfl

theorem writeMem_agrees {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) :
    TRes.Agrees (fun o : Out C σ.H Γ => (o.st.globE, o.st.loc)) (TRun.assignMem l r σ)
      ((Upd.nil.snoc (.memory (.app3 .write .memory l.lower r.lower))).applyV σ) := by
  have e : (Upd.nil.snoc (.memory (.app3 .write .memory l.lower r.lower))).applyV σ = (do
      let mv ← r.lower.eval σ
      let a ← l.lower.eval σ
      (·, σ.loc) <$> writeAddr σ.globE mv a) := by
    rw [upd1_applyV, memory_applyV]
    show (do
      let μ ← Op3.eval σ.globE .write (pure σ.globE) (l.lower.eval σ)
        (r.lower.eval σ)
      pure (({ σ.globE with heap := μ.heap, nextId := μ.nextId }, σ.loc))) = _
    simp only [Op3.eval, bind_assoc, pure_bind]
    congr 1; funext mv; congr 1; funext a
    exact memory_glob σ _ (Solidity.writeAddr_with _ _ _)
  rw [e]
  refine TRes.Agrees.bind (MSrc.lower_mvalT σ r) fun mv => ?_
  refine TRes.Agrees.bind (MLoc.lower_addrT σ l) fun a => ?_
  show TRes.Agrees _ (do
      let hp ← TRes.ofOpt (σ.heap.writeAddr a mv)
      pure (⟨σ.withHeap hp, List.prefix_refl _⟩ : Out C σ.H Γ))
    ((·, σ.loc) <$> writeAddr σ.globE (MVal.erase T mv) a.erase)
  rw [writeAddr_erase σ a mv]
  cases σ.heap.writeAddr a mv <;> rfl

theorem rebindPath_agrees {R : RefTy} (i : Idx Γ (.alias R)) (p : SPath C Γ (.ref R)) :
    TRes.Agrees (fun o : Out C σ.H Γ => (o.st.globE, o.st.loc)) (TRun.rebind i (.path p) σ)
      ((Upd.nil.snoc (.local i (.path p.lower))).applyV σ) := by
  simp only [TRun.rebind, ARhs.evalT, upd1_applyV, local_applyV, Rhs.eval, bind_assoc, pure_bind]
  exact TRes.Agrees.bind (SPath.lower_resolveT σ p) fun ref =>
    TRes.Agrees.of_eq (congrArg Except.ok (pair_setLocal σ i (some ref)).symm)

theorem rebindMemAlias_agrees {R : RefTy} (i : Idx Γ (.mem R)) (p : MPath C Γ (.ref R)) :
    TRes.Agrees (fun o : Out C σ.H Γ => (o.st.globE, o.st.loc)) (TRun.rebindMem i (.alias p) σ)
      ((Upd.nil.snoc (.local i (.mref p.lower))).applyV σ) := by
  simp only [TRun.rebindMem, MRhs.evalT, upd1_applyV, local_applyV, Rhs.eval, bind_assoc,
    pure_bind]
  exact TRes.Agrees.bind (MPath.lower_mvalT σ p) fun r =>
    TRes.Agrees.of_eq (congrArg Except.ok (pair_setLocal σ i (some r)).symm)

/-! ### Compound targets -/

section OpLoc

variable {op : BinOp} {p : PrimTy}

theorem storeLoc_agrees (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
    (L : Loc C Γ (.prim p)) (v : p.Denote) :
    TRes.Agrees (fun o : Out C σ.H Γ => (o.st.globE, o.st.loc)) (do opStoreT σ op (← L.resolveT σ) v)
      (do
        let (rt, segs) ← L.lower.eval σ
        (·, σ.loc) <$> opStore σ.globE op p rt segs (PrimTy.erase v)) :=
  TRes.Agrees.bind (Loc.lower_resolveT σ L) fun ref => opStoreT_erase σ hop hp ref v

theorem storeMem_agrees (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
    (L : MLoc C Γ (.prim p)) (v : p.Denote) :
    TRes.Agrees (fun o : Out C σ.H Γ => (o.st.globE, o.st.loc)) (do opMemT σ op (← L.addrT σ) v)
      (do (·, σ.loc) <$> opMem σ.globE op p (← L.lower.eval σ) (PrimTy.erase v)) :=
  TRes.Agrees.bind (MLoc.lower_addrT σ L) fun a => opMemT_erase σ hop hp a v

theorem bumpLoc_agrees (o : IncDec) (hp : p.isNumeric = true) (L : Loc C Γ (.prim p)) :
    TRes.Agrees (fun x : Out C σ.H Γ × p.Denote => ((x.1.st.globE, x.1.st.loc), PrimTy.erase x.2))
      (do bumpStoreT σ o (← L.resolveT σ))
      (do
        let (rt, segs) ← L.lower.eval σ
        glob₂ σ <$> bumpStore σ.globE o p rt segs) :=
  TRes.Agrees.bind (Loc.lower_resolveT σ L) fun ref => bumpStoreT_erase σ o hp ref fun _ _ => rfl

theorem bumpMem_agrees (o : IncDec) (hp : p.isNumeric = true) (L : MLoc C Γ (.prim p)) :
    TRes.Agrees (fun x : Out C σ.H Γ × p.Denote => ((x.1.st.globE, x.1.st.loc), PrimTy.erase x.2))
      (do bumpMemT σ o (← L.addrT σ))
      (do glob₂ σ <$> bumpMem σ.globE o p (← L.lower.eval σ)) :=
  TRes.Agrees.bind (MLoc.lower_addrT σ L) fun a => bumpMemT_erase σ o hp a fun _ _ => rfl

theorem opAssign_agrees (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
    (l : OpLoc C Γ p) (se : Simple C Γ p) :
    TRes.Agrees (fun o : Out C σ.H Γ => (o.st.globE, o.st.loc)) (TRun.opAssign op l (.simple se) σ)
      ((Upd.nil.snoc (l.set (l.op op se.lower))).applyV σ) := by
  have hse := Simple.lower_evalT σ se
  rw [upd1_applyV]
  show TRes.Agrees _ (l.storeT σ op (se.evalT σ)) _
  cases l with
  | «local» i =>
    show TRes.Agrees _ _
      (do pure (σ.globE, σ.loc.set i
        (← evalBinop op p (PrimTy.erase (p := p) (TEnv.get i σ.env)) (se.lower.eval σ))))
    rw [hse, evalBinop_compound hop, ok_bind, compound_erase' hop hp]
    show TRes.Agrees _ (do
      let new ← TRes.ofOpt (compoundT op p (PrimTy.key (TEnv.get i σ.env)) (PrimTy.key (se.evalT σ)))
      pure (⟨σ.setLocal i new, List.prefix_refl _⟩ : Out C σ.H Γ)) _
    cases compoundT op p (PrimTy.key (TEnv.get i σ.env)) (PrimTy.key (se.evalT σ)) with
    | none => rfl
    | some new => exact TRes.Agrees.of_eq (congrArg Except.ok (pair_setLocal σ i new).symm)
  | root r h =>
    exact (storeLoc_agrees σ hop hp (.root r h) _).of_eq_right
      (save_compound σ hop p _ _ hse).symm
  | field b f h =>
    exact (storeLoc_agrees σ hop hp (.field b f h) _).of_eq_right
      (save_compound σ hop p _ _ hse).symm
  | index it b ie =>
    exact (storeLoc_agrees σ hop hp (.index it b (.simple ie)) _).of_eq_right
      (save_compound σ hop p _ _ hse).symm
  | mfield b f h =>
    exact (storeMem_agrees σ hop hp (.field b f h) _).of_eq_right
      (write_compound σ hop p _ _ hse).symm
  | mindex a b ie =>
    exact (storeMem_agrees σ hop hp (.index a b (.simple ie)) _).of_eq_right
      (write_compound σ hop p _ _ hse).symm

/-- `l++` on a local, against `{v := v ± 1}`, by its value too. -/
theorem bumpLocal_agrees (o : IncDec) (hp : p.isNumeric = true) (i : Idx Γ (.val p)) :
    TRes.Agrees (fun x : Out C σ.H Γ × p.Denote => ((x.1.st.globE, x.1.st.loc), PrimTy.erase x.2))
      ((OpLoc.local i).bumpT σ o)
      (do
        let new ← evalBinop o.binOp p (σ.getE i) (pure (.int 1))
        pure ((σ.globE, σ.loc.set i new), if o.isPre then new else σ.getE i)) := by
  simp only [OpLoc.bumpT, State.getE, LTy.TDenote.erase_val, evalBinop_bump,
    Solidity.applyBinOp_bump, asInt_erase_numeric hp, ok_bind, pure_bind, bump_erase hp]
  cases Solidity.bumpT o p (PrimTy.key (TEnv.get i σ.env)) with
  | none => rfl
  | some new =>
    refine TRes.Agrees.of_eq ?_
    rw [pair_setLocal]
    cases o.isPre <;> rfl

theorem incDec_agrees (o : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    TRes.Agrees (fun x : Out C σ.H Γ => (x.st.globE, x.st.loc)) (TRun.incDec o l σ)
      ((Upd.nil.snoc (l.set (l.op o.binOp .one))).applyV σ) := by
  rw [upd1_applyV]
  show TRes.Agrees _ (l.bumpT σ o >>= fun x => pure x.1) _
  cases l with
  | «local» i =>
    refine TRes.Agrees.of_eq_right ((bumpLocal_agrees σ o hp i).bind_fst) ?_
    simp only [UpdElem.applyV, Rhs.eval, OpLoc.set, OpLoc.op, OpLoc.cur, Tm.eval, Op2.eval,
      Op0.eval, bind_assoc, pure_bind]
  | root r h =>
    exact (bumpLoc_agrees σ o hp (.root r h)).bind_fst.of_eq_right (save_bump σ o p _).symm
  | field b f h =>
    exact (bumpLoc_agrees σ o hp (.field b f h)).bind_fst.of_eq_right
      (save_bump σ o p _).symm
  | index it b ie =>
    exact (bumpLoc_agrees σ o hp (.index it b (.simple ie))).bind_fst.of_eq_right
      (save_bump σ o p _).symm
  | mfield b f h =>
    exact (bumpMem_agrees σ o hp (.field b f h)).bind_fst.of_eq_right
      (write_bump σ o p _).symm
  | mindex a b ie =>
    exact (bumpMem_agrees σ o hp (.index a b (.simple ie))).bind_fst.of_eq_right
      (write_bump σ o p _).symm

theorem assignIncDec_agrees (i : Idx Γ (.val p)) (o : IncDec) (hp : p.isNumeric = true)
    (l : OpLoc C Γ p) :
    TRes.Agrees (fun x : Out C σ.H Γ => (x.st.globE, x.st.loc)) (TRun.assignIncDec i o l σ)
      (((Upd.nil.snoc (l.set (l.op o.binOp .one))).snoc
        (.local i (.val (Tm.bumped o p l.cur)))).applyV σ) := by
  have hk : ∀ x : Out C σ.H Γ × p.Denote, TRes.Agrees (fun x : Out C σ.H Γ => (x.st.globE, x.st.loc))
      (pure (⟨x.1.st.setLocal i x.2, x.1.ext⟩ : Out C σ.H Γ))
      (pure (((x.1.st.globE, x.1.st.loc), PrimTy.erase x.2).1.1,
        ((x.1.st.globE, x.1.st.loc), PrimTy.erase x.2).1.2.set i
          ((x.1.st.globE, x.1.st.loc), PrimTy.erase x.2).2)) :=
    fun x => TRes.Agrees.of_eq (congrArg Except.ok (pair_setLocal x.1.st i x.2).symm)
  show TRes.Agrees _ (l.bumpT σ o >>= fun x =>
    pure (⟨x.1.st.setLocal i x.2, x.1.ext⟩ : Out C σ.H Γ)) _
  cases l with
  | «local» j =>
    refine TRes.Agrees.of_eq_right (TRes.Agrees.bind
      (k' := fun y : (Semantics.State × Locs C Γ) × Value => pure (y.1.1, y.1.2.set i y.2))
      (bumpLocal_agrees σ o hp j) hk) ?_
    rw [upd2_applyV]
    simp only [UpdElem.applyV, Rhs.eval, OpLoc.set, OpLoc.op, OpLoc.cur, Tm.bumped, Tm.eval,
      Op2.eval, Op0.eval, bind_assoc, pure_bind]
    cases hb : evalBinop o.binOp p (σ.getE j) (pure (.int 1)) with
    | error => rfl
    | ok new =>
      cases o.isPre <;> simp only [Bool.false_eq_true, ↓reduceIte, Tm.eval, Op2.eval, Op0.eval,
        pure_bind, hb] <;> rfl
  | root r h =>
    exact (TRes.Agrees.bind (bumpLoc_agrees σ o hp (.root r h)) hk).of_eq_right
      (save_bump_assign σ o p _ i).symm
  | field b f h =>
    exact (TRes.Agrees.bind (bumpLoc_agrees σ o hp (.field b f h)) hk).of_eq_right
      (save_bump_assign σ o p _ i).symm
  | index it b ie =>
    exact (TRes.Agrees.bind (bumpLoc_agrees σ o hp (.index it b (.simple ie))) hk).of_eq_right
      (save_bump_assign σ o p _ i).symm
  | mfield b f h =>
    exact (TRes.Agrees.bind (bumpMem_agrees σ o hp (.field b f h)) hk).of_eq_right
      (write_bump_assign σ o p _ i).symm
  | mindex a b ie =>
    exact (TRes.Agrees.bind (bumpMem_agrees σ o hp (.index a b (.simple ie))) hk).of_eq_right
      (write_bump_assign σ o p _ i).symm

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

/-- `b.push()` against the slot pushed on the erased global part. -/
theorem pushNone_agrees {E : Ty} (b : SPath C Γ (.array E)) :
    TRes.Agrees (fun o : Out C σ.H Γ => (o.st.globE, o.st.loc)) (TRun.push b none σ) (do
      let (root, segs) ← b.lower.eval σ
      (·, σ.loc) <$> pushAt σ.globE E root segs pure) := by
  refine TRes.Agrees.bind (SPath.lower_resolveT σ b) fun ref => ?_
  show TRes.Agrees _ (if σ.storage.full ref then .error .exhausted else do
      let st ← TRes.ofOpt (σ.storage.push ref fun slot => some slot)
      pure (⟨σ.withStorage st, List.prefix_refl _⟩ : Out C σ.H Γ))
    ((·, σ.loc) <$> pushAt σ.globE E ref.root ref.path.erase pure)
  cases hfull : σ.storage.full ref
  · rw [if_neg Bool.false_ne_true]
    rw [Storage.pushAt_erase (σ := σ.globE) rfl ref pure (fun slot => some slot)
      (fun _ => rfl) (.inl hfull)]
    cases σ.storage.push ref (fun slot => some slot) <;> rfl
  · trivial

theorem pushSlot_agrees {E : Ty} (b : SPath C Γ (.array E)) :
    TRes.Agrees (fun o : Out C σ.H Γ => (o.st.globE, o.st.loc)) (TRun.push b none σ)
      ((Upd.nil.snoc (.storage (.app2 (.pushSlot E) .storage b.lower))).applyV σ) := by
  refine (pushNone_agrees σ b).of_eq_right ?_
  rw [upd1_applyV, storage_applyV]
  show _ = (do
    let st ← Op2.eval σ.globE (.pushSlot E) (pure σ.globE) (b.lower.eval σ)
    pure (({ σ.globE with storage := st.storage }, σ.loc)))
  simp only [Op2.eval, bind_assoc, pure_bind]
  congr 1; funext q
  exact (storage_glob σ _ (Solidity.pushAt_with _ _ _ _ _)).symm

theorem extend_agrees {E : Ty} (b : SPath C Γ (.array E)) :
    TRes.Agrees (fun o : Out C σ.H Γ => (o.st.globE, o.st.loc)) (TRun.push b none σ)
      ((Upd.nil.snoc (.storage (.app2 (.extend E) .storage b.lower))).applyV σ) := by
  refine (pushNone_agrees σ b).of_eq_right ?_
  rw [upd1_applyV, storage_applyV]
  show _ = (do
    let st ← Op2.eval σ.globE (.extend E) (pure σ.globE) (b.lower.eval σ)
    pure (({ σ.globE with storage := st.storage }, σ.loc)))
  simp only [Op2.eval, pushPlaceAt, pushAt, SemanticsProperties.State.saveStorage_eq, bind_assoc,
    pure_bind]
  simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  cases b.lower.eval σ with
  | error => rfl
  | ok q =>
    simp only
    cases σ.globE.findStorage q.1 q.2 with
    | error => rfl
    | ok v =>
      cases v with
      | array elems shadow fx =>
        simp only
        cases σ.globE.storeRes q.1 q.2 _ <;> rfl
      | _ => rfl

theorem pushSome_agrees {E : Ty} (b : SPath C Γ (.array E)) (r : Src C Γ E) :
    TRes.Agrees (fun o : Out C σ.H Γ => (o.st.globE, o.st.loc)) (TRun.push b (some r) σ)
      ((Upd.nil.snoc (.storage (.app3 .push .storage b.lower r.lower))).applyV σ) := by
  have e : (Upd.nil.snoc (.storage (.app3 .push .storage b.lower r.lower))).applyV σ = (do
      let (root, segs) ← b.lower.eval σ
      (·, σ.loc) <$> pushAt σ.globE E root segs
        fun _ => do pure (← r.lower.eval σ).strip) := by
    rw [upd1_applyV, storage_applyV]
    show (do
      let st ← Op3.eval σ.globE .push (pure σ.globE) (b.lower.eval σ)
        (r.lower.eval σ)
      pure (({ σ.globE with storage := st.storage }, σ.loc))) = _
    simp only [Op3.eval, bind_assoc, pure_bind]
    congr 1; funext q
    rw [Solidity.pushAt_const σ.globE .uint E]
    exact storage_glob σ _ (Solidity.pushAt_with _ _ _ _ _)
  rw [e]
  refine TRes.Agrees.bind (SPath.lower_resolveT σ b) fun ref => ?_
  show TRes.Agrees _ (do
      let sv ← r.valueT σ
      if σ.storage.full ref then .error .exhausted else do
      let st ← TRes.ofOpt (σ.storage.push ref fun _ => some sv.strip)
      pure (⟨σ.withStorage st, List.prefix_refl _⟩ : Out C σ.H Γ))
    ((·, σ.loc) <$> pushAt σ.globE E ref.root ref.path.erase
      fun _ => do pure (← r.lower.eval σ).strip)
  have ha := Src.lower_valueT σ r
  have hn := Src.valueT_noPanic σ r
  revert ha hn
  cases r.valueT σ with
  | ok sv =>
    intro ha _
    have hval : ∀ x : SVal E, (fun _ => do pure (← r.lower.eval σ).strip) x.erase =
        toRes SVal.erase ((fun _ => some sv.strip) x) := fun _ => by
      show (do pure (← r.lower.eval σ).strip) = _
      rw [show r.lower.eval σ = .ok sv.erase from ha, ok_bind, ← SVal.strip_erase]
      rfl
    show TRes.Agrees _ (if σ.storage.full ref then .error .exhausted else do
        let st ← TRes.ofOpt (σ.storage.push ref fun _ => some sv.strip)
        pure (⟨σ.withStorage st, List.prefix_refl _⟩ : Out C σ.H Γ)) _
    cases hfull : σ.storage.full ref
    · rw [if_neg Bool.false_ne_true]
      rw [Storage.pushAt_erase (σ := σ.globE) rfl ref _ _ hval (.inl hfull)]
      cases σ.storage.push ref (fun _ => some sv.strip) <;> rfl
    · trivial
  | error e =>
    intro ha hn
    cases e with
    | diverge => trivial
    | exhausted => trivial
    | panic => exact absurd rfl hn
    | revert =>
      have hval : ∀ x : SVal E, (fun _ => do pure (← r.lower.eval σ).strip) x.erase =
          toRes SVal.erase ((fun _ => (none : Option (SVal E))) x) := fun _ => by
        show (do pure (← r.lower.eval σ).strip) = _
        rw [show r.lower.eval σ = .error .revert from ha]
        rfl
      rw [Storage.pushAt_erase (σ := σ.globE) rfl ref _ _ hval (.inr fun _ => rfl)]
      have hnone : σ.storage.push ref (fun _ => (none : Option (SVal E))) = none := by
        simp only [Storage.push]
        cases σ.storage.find ref <;> rfl
      rw [hnone]
      rfl

theorem pop_agrees {E : Ty} (b : SPath C Γ (.array E)) :
    TRes.Agrees (fun o : Out C σ.H Γ => (o.st.globE, o.st.loc)) (TRun.pop b σ)
      ((Upd.nil.snoc (.storage (.app2 (if E.isMapping then .shrink else .pop)
        .storage b.lower))).applyV σ) := by
  have e : (Upd.nil.snoc (.storage (.app2 (if E.isMapping then .shrink else .pop)
      .storage b.lower))).applyV σ = (do
      let (root, segs) ← b.lower.eval σ
      (·, σ.loc) <$> popAt σ.globE E.isMapping root segs) := by
    rw [upd1_applyV, storage_applyV]
    by_cases hE : E.isMapping = true
    · rw [if_pos hE]
      show (do
        let st ← Op2.eval σ.globE .shrink (pure σ.globE) (b.lower.eval σ)
        pure (({ σ.globE with storage := st.storage }, σ.loc))) = _
      simp only [Op2.eval, hE, bind_assoc, pure_bind]
      congr 1; funext q
      exact storage_glob σ _ (Solidity.popAt_with _ _ _ _)
    · have hE' : E.isMapping = false := by simpa only [Bool.not_eq_true] using hE
      rw [if_neg hE]
      show (do
        let st ← Op2.eval σ.globE .pop (pure σ.globE) (b.lower.eval σ)
        pure (({ σ.globE with storage := st.storage }, σ.loc))) = _
      simp only [Op2.eval, hE', bind_assoc, pure_bind]
      congr 1; funext q
      exact storage_glob σ _ (Solidity.popAt_with _ _ _ _)
  rw [e]
  refine TRes.Agrees.bind (SPath.lower_resolveT σ b) fun ref => ?_
  show TRes.Agrees _ (do
      let st ← TRes.ofOpt (σ.storage.pop E.isMapping ref)
      pure (⟨σ.withStorage st, List.prefix_refl _⟩ : Out C σ.H Γ))
    ((·, σ.loc) <$> popAt σ.globE E.isMapping ref.root ref.path.erase)
  rw [Storage.popAt_erase (σ := σ.globE) rfl E.isMapping ref]
  cases σ.storage.pop E.isMapping ref <;> rfl

theorem rebindPush_agrees {R : RefTy} (i : Idx Γ (.alias R)) (b : SPath C Γ (.array (.ref R)))
    (hd : (Ty.ref R).defaultOkS = true) :
    TRes.Agrees (fun o : Out C σ.H Γ => (o.st.globE, o.st.loc)) (TRun.rebind i (.push b hd) σ)
      (((Upd.nil.snoc (.storage (.app2 (.extend (.ref R)) .storage b.lower))).snoc
        (.local i (.path (.app1 .next rfl b.lower)))).applyV σ) := by
  have e : ((Upd.nil.snoc (.storage (.app2 (.extend (.ref R)) .storage b.lower))).snoc
      (.local i (.path (.app1 .next rfl b.lower)))).applyV σ = (do
      let (root, segs) ← b.lower.eval σ
      let (τ, n) ← pushPlaceAt σ.globE (.ref R) root segs
      pure (τ, σ.loc.set i (some (root, segs ++ [.at n])))) := by
    rw [upd2_applyV, storage_applyV]
    simp only [local_applyV, Rhs.eval, Tm.eval, Op2.eval, Op1.eval, Op0.eval, pushPlaceAt,
      SemanticsProperties.State.saveStorage_eq, bind_assoc, pure_bind]
    simp only [bind, Except.bind, pure, Except.pure]
    cases b.lower.eval σ with
    | error => rfl
    | ok q =>
      simp only
      cases σ.globE.findStorage q.1 q.2 with
      | error => rfl
      | ok v =>
        cases v with
        | array elems shadow fx =>
          simp only
          cases σ.globE.storeRes q.1 q.2 _ <;> rfl
        | _ => rfl
  rw [e]
  simp only [TRun.rebind, ARhs.evalT, bind_assoc]
  refine TRes.Agrees.bind (SPath.lower_resolveT σ b) fun r => ?_
  show TRes.Agrees _ ((if σ.storage.full r then .error .exhausted else do
        let (st, n) ← TRes.ofOpt (σ.storage.pushPlace r)
        pure (st, r.index (.arr .dyn) n)) >>= fun x =>
      pure (⟨(σ.withStorage x.1).setLocal i (some x.2), List.prefix_refl _⟩ : Out C σ.H Γ))
    (do
      let (τ, n) ← pushPlaceAt σ.globE (.ref R) r.root r.path.erase
      pure (τ, σ.loc.set i (some (r.root, r.path.erase ++ [.at n]))))
  cases hfull : σ.storage.full r
  · rw [if_neg Bool.false_ne_true]
    rw [Storage.pushPlaceAt_erase (σ := σ.globE) rfl r hfull]
    cases σ.storage.pushPlace r with
    | none => rfl
    | some x =>
      refine TRes.Agrees.of_eq (congrArg Except.ok ?_)
      rw [pair_setLocal]
      show (_, σ.loc.set i (some (r.root, r.path.erase ++ [.at (x.2 : Int)]))) =
        (_, σ.loc.set i (some (r.index (.arr .dyn) x.2).erase))
      rw [SRef.erase_index]
      rfl
  · trivial

theorem transferBox_agrees (sadr se : Simple C Γ .uint) :
    TRes.Agrees (fun o : Out C σ.H Γ => (o.st.globE, o.st.loc)) (TRun.transfer (.simple sadr) (.simple se) σ)
      ((Upd.nil.snoc (.payTo sadr se)).applyV σ) := by
  show TRes.Agrees _
    (.ok (⟨σ.pay (sadr.evalT σ).1 (se.evalT σ).1, List.prefix_refl _⟩ : Out C σ.H Γ)) _
  refine TRes.Agrees.of_eq ?_
  rw [upd1_applyV]
  simp only [UpdElem.applyV, UpdElem.globT, Simple.lower_evalT, PrimTy.asInt_erase_uint, Res.bind_ok,
    if_neg (Int.not_lt.mpr (PrimTy.uint_nonneg (se.evalT σ)))]
  rfl

/-- `pv = a.send(v);`'s outcome, by the updates of `sendNoCallback*`. -/
theorem send_sim (pv : Idx Γ (.val .bool)) (sadr se : Simple C Γ .uint) :
    ∃ U ∈ [(Upd.nil.snoc (.payTo sadr se)).snoc (.local pv (.val (Tm.lit (.bool true)))),
        Upd.nil.snoc (.local pv (.val (Tm.lit (.bool false))))],
      Res.Sim (U.applyV σ)
        (.ok ((sendT σ pv (sadr.evalT σ).1 (se.evalT σ).1).st.globE,
          (sendT σ pv (sadr.evalT σ).1 (se.evalT σ).1).st.loc)) := by
  have hk := PrimTy.uint_nonneg (se.evalT σ)
  have e₁ : ((Upd.nil.snoc (.payTo sadr se)).snoc
      (.local pv (.val (Tm.lit (.bool true))))).applyV σ =
        .ok (((σ.pay (sadr.evalT σ).1 (se.evalT σ).1).setLocal pv (true : Bool)).globE,
          ((σ.pay (sadr.evalT σ).1 (se.evalT σ).1).setLocal pv (true : Bool)).loc) := by
    rw [upd2_applyV, pair_setLocal]
    simp only [UpdElem.applyV, UpdElem.globT, Rhs.eval, Tm.eval, Op0.eval, Simple.lower_evalT,
      PrimTy.asInt_erase_uint, Res.bind_ok, if_neg (Int.not_lt.mpr hk)]
    rfl
  have e₂ : (Upd.nil.snoc (.local pv (.val (Tm.lit (C := C) (Γ := Γ) (.bool false))))).applyV
      σ = .ok ((σ.setLocal pv (false : Bool)).globE, (σ.setLocal pv (false : Bool)).loc) := by
    rw [pair_setLocal]; rfl
  unfold sendT
  cases Semantics.lookupBy (sendKey (sadr.evalT σ).1 (se.evalT σ).1) σ.tx.ext with
  | none => exact ⟨_, List.mem_cons_self .., by rw [e₁]; exact Res.Sim.refl _⟩
  | some x =>
    cases x with
    | ok => exact ⟨_, List.mem_cons_self .., by rw [e₁]; exact Res.Sim.refl _⟩
    | _ =>
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by rw [e₂]; exact Res.Sim.refl _⟩

theorem declMemFresh_agrees (R : RefTy) (x : Var) (hm : (Ty.ref R).mapFree = true) :
    TRes.Agrees (fun o : Out C σ.H (.mem R :: Γ) => (o.st.globE, o.st.loc)) (TRun.declMem R none hm σ)
      (((Upd.nil.decl x (.mref (.app1 (.alloc R) rfl .memory))).snoc
        (.memory (.app1 (.addM R) rfl .memory))).applyV σ) := by
  have e : ((Upd.nil.decl x (.mref (.app1 (.alloc R) rfl .memory))).snoc
      (.memory (.app1 (.addM R) rfl .memory))).applyV σ = (do
      let (τ', id) ← Semantics.allocDefault σ.globE R
      pure (τ', σ.loc.push (t := .mem R) (some id))) := by
    show (do
      let q ← (Upd.nil.decl x (.mref (.app1 (.alloc R) rfl .memory))).applyV σ
      UpdElem.applyV σ (.memory (.app1 (.addM R) rfl .memory)) q.1 q.2) = _
    simp only [Upd.applyV, memory_applyV, Rhs.eval, Tm.eval, Op1.eval, Op0.eval,
      Solidity.allocDefault_eq, bind_assoc, pure_bind]
    simp only [bind, Except.bind, pure, Except.pure]
    cases Solidity.allocHN σ.globE R <;> rfl
  rw [e, State.allocDefault_erase σ R hm, ok_bind]
  refine TRes.Agrees.of_eq (congrArg Except.ok ?_)
  rw [State.loc_push]
  show (_, σ.loc.push _) = (_, (σ.allocDefault R hm).1.loc.push _)
  rw [show (σ.allocDefault R hm).1.loc = σ.loc from State.adopt_loc σ _]
  rfl

theorem deleteMemVar_agrees {R : RefTy} (i : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true) :
    TRes.Agrees (fun o : Out C σ.H Γ => (o.st.globE, o.st.loc)) (TRun.deleteMem (.var i hm) σ)
      (((Upd.nil.snoc (.local i (.mref (.app1 (.alloc R) rfl .memory)))).snoc
        (.memory (.app1 (.addM R) rfl .memory))).applyV σ) := by
  have e : ((Upd.nil.snoc (.local i (.mref (.app1 (.alloc R) rfl .memory)))).snoc
      (.memory (.app1 (.addM R) rfl .memory))).applyV σ = (do
      let (τ', id) ← Semantics.allocDefault σ.globE R
      pure (τ', σ.loc.set i (some id))) := by
    rw [upd2_applyV]
    simp only [memory_applyV, local_applyV, Rhs.eval, Tm.eval, Op1.eval, Op0.eval,
      Solidity.allocDefault_eq, bind_assoc, pure_bind]
    simp only [bind, Except.bind, pure, Except.pure]
    cases Solidity.allocHN σ.globE R <;> rfl
  rw [e, State.allocDefault_erase σ _ hm, ok_bind]
  refine TRes.Agrees.of_eq (congrArg Except.ok ?_)
  rw [pair_setLocal]
  show (_, σ.loc.set i _) = (_, (σ.allocDefault _ hm).1.loc.set i _)
  rw [show (σ.allocDefault _ hm).1.loc = σ.loc from State.adopt_loc σ _]
  rfl

theorem allocCopy_agrees {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) (v : Tm C Γ .sv)
    (hr : TRes.Agrees (fun g : Grew C Γ σ.H (HRef · R) => ((g.st.globE, g.st.loc), (g.val : HRef _ R).id))
      (r.evalT σ) (do
        let (τ, mv) ← Semantics.copyStToM σ.globE (← v.eval σ)
        pure ((τ, σ.loc), ← mv.asRef))) :
    TRes.Agrees (fun o : Out C σ.H Γ => (o.st.globE, o.st.loc)) (TRun.rebindMem i r σ)
      (((Upd.nil.snoc (.local i (.mref (.app2 .copy .memory v)))).snoc
        (.memory (.app2 .copySt .memory v))).applyV σ) := by
  have e : ((Upd.nil.snoc (.local i (.mref (.app2 .copy .memory v)))).snoc
      (.memory (.app2 .copySt .memory v))).applyV σ = (do
      let (τ', id) ← (do
        let (τ, mv) ← Semantics.copyStToM σ.globE (← v.eval σ)
        pure ((τ, σ.loc), ← mv.asRef))
      pure (τ'.1, τ'.2.set i (some id))) := by
    rw [upd2_applyV]
    simp only [memory_applyV, local_applyV, Rhs.eval, Tm.eval, Op2.eval, Op0.eval,
      Solidity.copyStToM_eq, bind_assoc, pure_bind]
    simp only [bind, Except.bind, pure, Except.pure]
    cases v.eval σ with
    | error => rfl
    | ok sv =>
      simp only
      cases Solidity.copyHN σ.globE sv with
      | error => rfl
      | ok q =>
        simp only
  rw [e]
  exact TRes.Agrees.bind hr fun g =>
    TRes.Agrees.of_eq (congrArg Except.ok (pair_setLocal g.st i (some g.val)).symm)

/-- `memoryStorageCopy`'s right-hand side: a deep copy of `sfind(storage, p)`. -/
theorem allocCopy_copy {R : RefTy} (p : SPath C Γ (.ref R)) (hm : (Ty.ref R).mapFree = true) :
    TRes.Agrees (fun g : Grew C Γ σ.H (HRef · R) => ((g.st.globE, g.st.loc), (g.val : HRef _ R).id))
      ((MRhs.copy p hm).evalT σ) (do
        let (τ, mv) ← Semantics.copyStToM σ.globE
          (← (Tm.app2 .sfind .storage p.lower : Tm C Γ .sv).eval σ)
        pure ((τ, σ.loc), ← mv.asRef)) := by
  show TRes.Agrees _ _ (do
    let sv ← (do
      let τ ← pure σ.globE
      let (r, segs) ← p.lower.eval σ
      τ.findStorage r segs)
    let (τ, mv) ← Semantics.copyStToM σ.globE sv
    pure ((τ, σ.loc), ← mv.asRef))
  simp only [pure_bind, bind_assoc]
  refine TRes.Agrees.bind (SPath.lower_resolveT σ p) fun r => ?_
  show TRes.Agrees _ (do
      let sv ← TRes.ofOpt (σ.storage.find r)
      let g := σ.copyStToMG sv hm
      pure (⟨g.st, g.ext, g.val⟩ : Grew C Γ σ.H (HRef · R)))
    (do
      let sv ← σ.globE.findStorage r.root r.path.erase
      let (τ, mv) ← Semantics.copyStToM σ.globE sv
      pure ((τ, σ.loc), ← mv.asRef))
  rw [Storage.findStorage_erase (σ := σ.globE) rfl r]
  refine TRes.Agrees.bind (TRes.Agrees.ofOpt _) fun sv => ?_
  rw [State.copyStToM_erase σ sv hm]
  exact TRes.Agrees.of_eq (by
    show Except.ok (((σ.copyStToM sv hm).1.globE, σ.loc), _) = _
    rw [← State.adopt_loc σ (SVal.copyStToM σ.heap sv hm)]
    rfl)

/-- `memoryArrayFreshAlloc`'s right-hand side: `newArr(R, n)` copied. -/
theorem allocCopy_newArr {R : RefTy} (n : Simple C Γ .uint) (h : R.newArrOk = true) :
    TRes.Agrees (fun g : Grew C Γ σ.H (HRef · R) => ((g.st.globE, g.st.loc), (g.val : HRef _ R).id))
      ((MRhs.newArr n h).evalT σ) (do
        let (τ, mv) ← Semantics.copyStToM σ.globE
          (← (Tm.app1 (.newArr R) rfl n.lower : Tm C Γ .sv).eval σ)
        pure ((τ, σ.loc), ← mv.asRef)) := by
  show TRes.Agrees _ _ (do
    let sv ← (do pure (newArrVal R (← (← n.lower.eval σ).asInt)))
    let (τ, mv) ← Semantics.copyStToM σ.globE sv
    pure ((τ, σ.loc), ← mv.asRef))
  rw [Simple.lower_evalT σ n, ok_bind, PrimTy.asInt_erase_uint, ok_bind, pure_bind,
    ← newArrT_erase R _ h]
  rw [State.copyStToM_erase σ _ (RefTy.mapFree_of_newArrOk h)]
  exact TRes.Agrees.of_eq (by
    show Except.ok (((σ.copyStToM _ _).1.globE, σ.loc), _) = _
    rw [← State.adopt_loc σ (SVal.copyStToM σ.heap _ _)]
    rfl)

/-- `delete l` at a memory location: the slot reset to its default, or
written a fresh default object, up to the halt (the update allocates before
it reads the address). -/
theorem clearMem_sim {T : Ty} (l : MLoc C Γ T) (hd : T.defaultOkS = true) :
    ∃ U, Premise.clearMem l.lower T = .update U ∧
      Res.Sim (U.applyV σ)
        (do (·, σ.loc) <$> memClear σ.globE (← l.lower.eval σ) T) := by
  cases T with
  | prim p =>
    refine ⟨_, rfl, Res.Sim.of_eq ?_⟩
    rw [upd1_applyV, memory_applyV]
    show _ = _
    simp only [Tm.eval, Op3.eval, Op1.eval, Op0.eval, memClear, bind_assoc,
      pure_bind, writeAddr_glob]
  | ref R =>
    refine ⟨_, rfl, ?_⟩
    rw [upd1_applyV, memory_applyV]
    simp only [Tm.eval, Op3.eval, Op1.eval, Op0.eval, memClear,
      Solidity.allocDefault_eq, bind_assoc, pure_bind]
    simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
    have ha : NoPanic (l.lower.eval σ) := Tm.eval_noPanic σ l.lower
    have hal : NoPanic (Solidity.allocHN σ.globE R) := Solidity.allocHN_noPanic σ.globE R
    revert ha hal
    cases l.lower.eval σ with
    | error e =>
      cases Solidity.allocHN σ.globE R with
      | error e' => exact fun ha hal => ⟨fun h => absurd (congrArg Except.error h) hal,
          fun h => absurd (congrArg Except.error h) ha⟩
      | ok q => intro _ _; exact Res.Sim.refl _
    | ok a =>
      cases Solidity.allocHN σ.globE R with
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
side's typed evaluation against the copy on the erased global part (`allocCopy_copy`,
`allocCopy_newArr`). -/
theorem sound_allocCopy {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) (v : Tm C Γ .sv)
    (hr : TRes.Agrees (fun g : Grew C Γ σ.H (HRef · R) => ((g.st.globE, g.st.loc), (g.val : HRef _ R).id))
      (r.evalT σ) (do
        let (τ, mv) ← Semantics.copyStToM σ.globE (← v.eval σ)
        pure ((τ, σ.loc), ← mv.asRef))) :
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
      show (σ.globE, σ.loc.push (PrimTy.default p)) =
        ((σ.push (t := .val p) (PrimTy.dflt p)).globE, (σ.push (t := .val p) (PrimTy.dflt p)).loc)
      rw [State.loc_push, ← PrimTy.erase_dflt]; rfl)))
    fun _ => TRes.NoDiv.ok _

/-- `storageLocalDeclSkip`: `{lsv := unset}`. -/
theorem sound_storageLocalDeclSkip (R : RefTy) (x : Var) :
    Premise.Runs m (.declStorage R x none) (.update (Upd.nil.decl (t := .alias R) x .unset)) σ :=
  Premise.sound_update_typed (s := .declStorage R x none) (t := TRun.declStorage R none) σ
    (TRes.Agrees.of_eq (congrArg Except.ok (by rw [State.loc_push]; rfl))) fun _ => TRes.NoDiv.ok _

/-- `revertBox`, `revertDiamond`. -/
theorem sound_revert :
    Premise.Sound m (.revert : Stmt C Γ Γ) (.done (m == .box)) σ :=
  Premise.sound_done σ _ fun h =>
    ⟨by cases m <;> first | rfl | exact absurd h (by decide), .revert, rfl, by decide⟩

end Arms2

end Solidity
