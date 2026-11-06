import Solidity.Source.Horizon.Grow

/-!
# Horizons: helpers that keep the events

Part of `Solidity/Source/Horizon.lean` (S05 item 2), split from it to keep each
module under the 8 GiB pre-gate bound: `Const` lemmas for the helpers and the
`const_go` tactic.
-/

namespace Solidity.Source

open EM
open Solidity.Roadmap (Address Word Bytes Request Outcome Event)

variable {E : Env}

/-! ## Helpers keep the events -/

/-- A computation leaves the events as they are. -/
def Const {Γ : RCtx} {α : Type} (m : EM E Γ α) : Prop :=
  ∀ x, (m.run x).2.2.events = x.2.events

theorem Const.pure {Γ : RCtx} {α : Type} (a : α) : Const (pure a : EM E Γ α) := fun _ => rfl
theorem Const.halt {Γ : RCtx} {α : Type} (h : Halt) : Const (halt h : EM E Γ α) := fun _ => rfl
theorem Const.bind {Γ : RCtx} {α β : Type} {m : EM E Γ α} {k : α → EM E Γ β} (hm : Const m)
    (hk : ∀ a, Const (k a)) : Const (m >>= k) := by
  intro x
  rw [run_bind]
  have h1 := hm x
  rcases hr : m.run x with ⟨r, y⟩
  rw [hr] at h1
  cases r with
  | ok a => exact (hk a y).trans h1
  | error e => exact h1

/-- A computation that keeps the events approximates itself at a larger
horizon exactly when it is below it. -/
theorem Approx.of_below {Γ : RCtx} {α : Type} {m m' : EM E Γ α} (hb : Below m m') (hc : Const m)
    (hc' : Const m') : Approx m m' := by
  refine ⟨fun x => (hc x).symm ▸ List.prefix_refl _, fun x => (hc' x).symm ▸ List.prefix_refl _, fun x => ?_⟩
  rcases hb x with ht | he
  · exact .inl ⟨ht, by rw [hc, hc']; exact List.prefix_refl _⟩
  · exact .inr he


theorem Const.st {Γ : RCtx} : Const (st : EM E Γ (St E)) := fun _ => rfl
theorem Const.locals {Γ : RCtx} : Const (locals : EM E Γ (Locals E.layout Γ)) := fun _ => rfl
theorem Const.setLocals {Γ : RCtx} (l : Locals E.layout Γ) : Const (setLocals l : EM E Γ Unit) :=
  fun _ => rfl
theorem Const.modSt {Γ : RCtx} (f : St E → St E) (hf : ∀ s, (f s).events = s.events) :
    Const (modSt f : EM E Γ Unit) := fun x => hf x.2
theorem Const.lift {Γ : RCtx} {α : Type} (r : R α) : Const (lift r : EM E Γ α) := by
  cases r <;> exact fun _ => rfl
theorem Const.sub {Γ Γ' : RCtx} {α : Type} (l' : Locals E.layout Γ') {m : EM E Γ' α} (h : Const m) :
    Const (EM.sub (Γ := Γ) l' m) := by
  intro x
  rcases x with ⟨l, s⟩
  rw [run_sub]
  have := h (l', s)
  rcases hr : m.run (l', s) with ⟨r, l'', s'⟩
  rw [hr] at this
  cases r <;> exact this
theorem Const.attempt {Γ : RCtx} {α : Type} {m : EM E Γ α} (h : Const m) : Const (EM.attempt m) := by
  intro x
  rw [run_attempt]
  exact h x

theorem heapPut_const {Γ : RCtx} (a : Nat) (x : Σ τ, Data E.layout τ) : Const (heapPut (Γ := Γ) a x) := by
  intro y
  unfold heapPut
  rw [run_bind, run_st]
  dsimp only
  split
  · exact rfl
  · exact rfl

theorem alloc_const {Γ : RCtx} {τ : STy} (x : Data E.layout τ) : Const (alloc (Γ := Γ) x) := by
  intro y
  unfold alloc
  rw [run_bind, run_st]
  exact rfl

/-- Close `Const body`: through binds, `match`es and `if`s, by the given
lemmas at the calls; a `modSt` keeps or appends events. -/
syntax "const_go" "[" ident,* "]" : tactic
macro_rules
  | `(tactic| const_go [$ls,*]) => `(tactic| repeat' (first
      | (with_reducible exact Const.pure _)
      | (with_reducible exact Const.halt _)
      | (with_reducible exact Const.st)
      | (with_reducible exact Const.locals)
      | (with_reducible exact Const.setLocals _)
      | (with_reducible exact Const.lift _)
      | (with_reducible apply Const.modSt; intro _; rfl)
      | (first $[| with_reducible apply $ls:ident]*)
      | (with_reducible apply Const.sub)
      | (with_reducible apply Const.attempt)
      | (with_reducible apply Const.map)
      | (refine Const.bind ?_ ?_)
      | (with_reducible intro _)
      | split
      | (intro _; exact rfl)
      | (dsimp only)))

section
variable {Γ : RCtx}

theorem getV_const {τ : STy} (v : RVal E.layout τ) : Const (getV (Γ := Γ) v) := Const.lift _
theorem readCell_const (F : Fr) (p : SPath) : Const (readCell (E := E) (Γ := Γ) F p) := by
  unfold readCell; const_go []
theorem readAt_const (F : Fr) (p : SPath) (τ : STy) : Const (readAt (E := E) (Γ := Γ) F p τ) := by
  unfold readAt; const_go [readCell_const]
theorem applyOp_const (F : Fr) (o : Op E.layout E.lay E.lay) : Const (applyOp (Γ := Γ) F o) := by
  unfold applyOp; const_go []
theorem setCell_const (F : Fr) (p : SPath) (o : Option (Val E.layout (E.cellTy p))) :
    Const (setCell (Γ := Γ) F p o) := by
  unfold setCell; const_go [applyOp_const]
theorem writeAt_const {τ : STy} (F : Fr) (p : SPath) (v : Val E.layout τ) : Const (writeAt (Γ := Γ) F p v) := by
  unfold writeAt; const_go [setCell_const]
theorem readLen_const (F : Fr) (p : SPath) : Const (readLen (E := E) (Γ := Γ) F p) := by
  unfold readLen; const_go [readAt_const]
theorem writeLen_const (F : Fr) (p : SPath) (k : Nat) : Const (writeLen (E := E) (Γ := Γ) F p k) := by
  unfold writeLen; const_go [writeAt_const]
theorem heapObj_const (a : Nat) : Const (heapObj (E := E) (Γ := Γ) a) := by
  unfold heapObj; const_go []
theorem heapAt_const (a : Nat) (τ : STy) : Const (heapAt (E := E) (Γ := Γ) a τ) := by
  unfold heapAt; const_go [heapObj_const]
theorem heapBytes_const (a : Nat) : Const (heapBytes (E := E) (Γ := Γ) a) := by
  unfold heapBytes; const_go [heapObj_const]
theorem allocRef_const {τ : STy} (x : Data E.layout τ) : Const (allocRef (Γ := Γ) x) := by
  unfold allocRef; const_go [alloc_const]
theorem storRef_const (τ : STy) (p : SPath) : Const (storRef (E := E) (Γ := Γ) τ p) := by
  unfold storRef; const_go []

end

section
variable {Γ : RCtx}

mutual
theorem zeroData_const : ∀ (n : Nat) (τ : STy), Const (zeroData (E := E) (Γ := Γ) n τ)
  | 0, _ => Const.halt _
  | n + 1, τ => by
    simp only [zeroData]
    const_go [zeroElems_const, zeroFields_const, zeroVal_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const]
theorem zeroVal_const : ∀ (n : Nat) (τ : STy), Const (zeroVal (E := E) (Γ := Γ) n τ)
  | 0, _ => Const.halt _
  | n + 1, τ => by
    simp only [zeroVal]
    const_go [zeroData_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const]
theorem zeroElems_const : ∀ (n : Nat) (σ : STy) (m : Nat), Const (zeroElems (E := E) (Γ := Γ) n σ m)
  | 0, _, m => by cases m <;> exact Const.halt _
  | n + 1, _, 0 => Const.pure _
  | n + 1, σ, m + 1 => Const.bind (zeroVal_const n σ) fun _ => Const.bind (zeroElems_const n σ m) fun _ => Const.pure _
theorem zeroFields_const : ∀ (n : Nat) (τs : List STy), Const (zeroFields (E := E) (Γ := Γ) n τs)
  | 0, τs => by cases τs <;> exact Const.halt _
  | n + 1, [] => Const.pure _
  | n + 1, τ :: τs => Const.bind (zeroVal_const n τ) fun _ => Const.bind (zeroFields_const n τs) fun _ => Const.pure _
end

mutual
theorem loadMem_const (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath), Const (loadMem (E := E) (Γ := Γ) F n τ p)
  | 0, _, _ => Const.halt _
  | n + 1, τ, p => by
    simp only [loadMem]
    const_go [loadBytes_const, loadElems_const, loadFields_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const]
theorem loadElem_const (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath), Const (loadElem (E := E) (Γ := Γ) F n τ p)
  | 0, _, _ => Const.halt _
  | n + 1, τ, p => by
    simp only [loadElem]
    const_go [loadMem_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const]
theorem loadElems_const (F : Fr) : ∀ (n : Nat) (σ : STy) (p : SPath) (i m : Nat),
    Const (loadElems (E := E) (Γ := Γ) F n σ p i m)
  | 0, _, _, _, m => by cases m <;> exact Const.halt _
  | n + 1, _, _, _, 0 => Const.pure _
  | n + 1, σ, p, i, m + 1 => Const.bind (loadElem_const F n σ _) fun _ =>
      Const.bind (loadElems_const F n σ p (i + 1) m) fun _ => Const.pure _
theorem loadFields_const (F : Fr) : ∀ (n : Nat) (τs : List STy) (p : SPath) (i : Nat),
    Const (loadFields (E := E) (Γ := Γ) F n τs p i)
  | 0, τs, _, _ => by cases τs <;> exact Const.halt _
  | n + 1, [], _, _ => Const.pure _
  | n + 1, τ :: τs, p, i => Const.bind (loadElem_const F n τ _) fun _ =>
      Const.bind (loadFields_const F n τs p (i + 1)) fun _ => Const.pure _
theorem loadBytes_const (F : Fr) : ∀ (n : Nat) (p : SPath) (i k : Nat), Const (loadBytes (E := E) (Γ := Γ) F n p i k)
  | 0, _, _, k => by cases k <;> exact Const.halt _
  | n + 1, _, _, 0 => Const.pure _
  | n + 1, p, i, k + 1 => by
    refine Const.bind (readAt_const F _ _) fun v => ?_
    cases v <;> first
      | exact Const.bind (loadBytes_const F n p (i + 1) k) fun _ => Const.pure _
      | (rename_i h; cases h)
end

mutual
theorem deleteStor_const (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath), Const (deleteStor (E := E) (Γ := Γ) F n τ p)
  | 0, _, _ => Const.halt _
  | n + 1, τ, p => by
    simp only [deleteStor]
    const_go [deleteRange_const, deleteFields_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const]
theorem deleteRange_const (F : Fr) : ∀ (n : Nat) (σ : STy) (p : SPath) (i k : Nat),
    Const (deleteRange (E := E) (Γ := Γ) F n σ p i k)
  | 0, _, _, _, k => by cases k <;> exact Const.halt _
  | n + 1, _, _, _, 0 => Const.pure _
  | n + 1, σ, p, i, k + 1 => Const.bind (deleteStor_const F n σ _) fun _ => deleteRange_const F n σ p (i + 1) k
theorem deleteFields_const (F : Fr) : ∀ (n : Nat) (τs : List STy) (p : SPath) (i : Nat),
    Const (deleteFields (E := E) (Γ := Γ) F n τs p i)
  | 0, τs, _, _ => by cases τs <;> exact Const.halt _
  | n + 1, [], _, _ => Const.pure _
  | n + 1, τ :: τs, p, i => Const.bind (deleteStor_const F n τ _) fun _ => deleteFields_const F n τs p (i + 1)
end

mutual
theorem storeData_const (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath) {σ : STy} (x : Data E.layout σ),
    Const (storeData (Γ := Γ) F n τ p x)
  | 0, _, _, _, _ => Const.halt _
  | n + 1, τ, p, _, x => by
    simp only [storeData]
    const_go [storeBytes_const, deleteRange_const, storeElems_const, storeFields_const, storeVal_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const]
theorem storeVal_const (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath) {σ : STy} (v : Val E.layout σ),
    Const (storeVal (Γ := Γ) F n τ p v)
  | 0, _, _, _, _ => Const.halt _
  | n + 1, τ, p, _, v => by
    simp only [storeVal]
    const_go [storeData_const, loadMem_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const]
theorem storeElems_const (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath) (i len : Nat) {σ : STy}
    (xs : Fin len → Data E.layout σ), Const (storeElems (Γ := Γ) F n τ p i len xs)
  | 0, _, _, _, len, _, _ => by cases len <;> exact Const.halt _
  | n + 1, _, _, _, 0, _, _ => Const.pure _
  | n + 1, τ, p, i, len + 1, _, xs =>
    Const.bind (storeData_const F n τ _ _) fun _ => storeElems_const F n τ p (i + 1) len _
theorem storeFields_const (F : Fr) : ∀ (n : Nat) (τs : List STy) (p : SPath) (i : Nat) {σs : List STy}
    (xs : DataList E.layout σs), Const (storeFields (Γ := Γ) F n τs p i xs)
  | 0, τs, _, _, _, xs => by cases τs <;> cases xs <;> exact Const.halt _
  | n + 1, [], _, _, _, _ => Const.pure _
  | n + 1, _ :: _, _, _, _, .nil => Const.pure _
  | n + 1, τ :: τs, p, i, _, .cons x xs =>
    Const.bind (storeData_const F n τ _ x) fun _ => storeFields_const F n τs p (i + 1) xs
theorem storeBytes_const (F : Fr) : ∀ (n : Nat) (p : SPath) (i : Nat) (bs : List UInt8),
    Const (storeBytes (E := E) (Γ := Γ) F n p i bs)
  | 0, _, _, bs => by cases bs <;> exact Const.halt _
  | n + 1, _, _, [] => Const.pure _
  | n + 1, p, i, b :: bs => Const.bind (writeAt_const F _ _) fun _ => storeBytes_const F n p (i + 1) bs
end

end

section
variable {Γ : RCtx}

theorem List.mapM_const {Γ : RCtx} {α β : Type} (f : α → EM E Γ β) (hf : ∀ a, Const (f a)) :
    ∀ (l : List α), Const (l.mapM f) := by
  intro l
  suffices h : ∀ (acc : List β), Const (List.mapM.loop f l acc) from h []
  induction l with
  | nil => intro acc; exact Const.pure _
  | cons a as ih => intro acc; exact Const.bind (hf a) fun b => ih (b :: acc)

theorem panicM_const {α : Type} : Const (memElem.panicM (E := E) (Γ := Γ) (α := α)) := Const.lift _
theorem memElem_const (a i : Nat) (τ : STy) : Const (memElem (E := E) (Γ := Γ) a i τ) := by
  unfold memElem; const_go [panicM_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const]
theorem readLoc_const (F : Fr) {τ : STy} (loc : Loc E.layout Γ τ) : Const (readLoc F loc) := by
  cases loc <;> simp only [readLoc] <;> const_go [memElem_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const]
theorem memSet_const (a i : Nat) {τ : STy} (v : Val E.layout τ) : Const (memSet (Γ := Γ) a i v) := by
  unfold memSet; const_go [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const]
theorem lengthOf_const (F : Fr) {τ : STy} (v : Val E.layout τ) : Const (lengthOf (Γ := Γ) F v) := by
  unfold lengthOf; const_go [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const]
theorem indexLoc_const (F : Fr) {l : DataLoc} {σ : STy} {k : Option Nat} (a : Val E.layout (.array l σ k))
    (i : Nat) : Const (indexLoc (Γ := Γ) F a i) := by
  unfold indexLoc; const_go [lengthOf_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const]
theorem indexNat_const {σ : STy} (v : RVal E.layout σ) : Const (indexNat (Γ := Γ) v) := Const.lift _
theorem instanceAt_const (G : Glob E) (a : Address) : Const (instanceAt (Γ := Γ) G a) := by
  unfold instanceAt; const_go []
theorem credit_const (a : Address) (v : Word) : Const (credit (E := E) (Γ := Γ) a v) := by
  unfold credit; const_go []
theorem debit_const (a : Address) (v : Word) : Const (debit (E := E) (Γ := Γ) a v) := by
  unfold debit; const_go []
theorem mark_const : Const (mark (E := E) (Γ := Γ)) := by
  unfold mark; const_go []
theorem rollbackTo_const (m : Nat × Nat × Heap E.layout) : Const (rollbackTo (Γ := Γ) m) := by
  unfold rollbackTo; const_go []
theorem reraise_const (o : Outcome) : Const (reraise (E := E) (Γ := Γ) o) := by
  unfold reraise; const_go []
theorem fieldsOf_const : ∀ {ps : List STy} (vs : Vals E.layout ps) (τs : List STy),
    Const (fieldsOf (E := E) (Γ := Γ) vs τs)
  | _, .nil, [] => Const.pure _
  | _, .nil, _ :: _ => Const.halt _
  | _, .cons _ _, [] => Const.halt _
  | _, .cons (τ := σ) v vs, τ :: τs => by
    simp only [fieldsOf]
    split
    · exact Const.bind (fieldsOf_const vs τs) fun _ => Const.pure _
    · exact Const.halt _
theorem ret32_const (τ : STy) (bs : Bytes) : Const (ret32 (E := E) (Γ := Γ) τ bs) := by
  unfold ret32; const_go []
theorem tailBytes_const (data : Bytes) (i : Nat) : Const (tailBytes (E := E) (Γ := Γ) data i) := by
  unfold tailBytes
  dsimp only
  split
  · exact Const.halt _
  · split
    · exact Const.lift _
    · split
      · exact Const.pure _
      · exact Const.halt _
theorem decodeArg_const (data : Bytes) (i : Nat) (τ : STy) : Const (decodeArg (E := E) (Γ := Γ) data i τ) := by
  unfold decodeArg
  split
  · split
    · exact Const.bind (tailBytes_const data i) fun _ => allocRef_const _
    · exact Const.lift _
    · exact Const.lift _
  · split
    · exact Const.bind (tailBytes_const data i) fun _ => allocRef_const _
    · exact Const.lift _
    · exact Const.lift _
  · split
    · split
      · dsimp only
        split
        · exact Const.halt _
        · split
          · exact Const.lift _
          · split
            · exact Const.bind (List.mapM_const _ (fun _ => Const.lift _) _) fun _ => allocRef_const _
            · exact Const.halt _
      · exact Const.halt _
    · split
      · exact Const.lift _
      · exact Const.halt _
    · exact Const.lift _
  · exact Const.lift _
theorem decodeArgs_const (data : Bytes) : ∀ (τs : List STy) (i : Nat), Const (decodeArgs (E := E) (Γ := Γ) data τs i)
  | [], _ => Const.pure _
  | τ :: τs, i => Const.bind (decodeArg_const data i τ) fun _ =>
      Const.bind (decodeArgs_const data τs (i + 1)) fun _ => Const.pure _

end

section
variable {Γ : RCtx}

theorem bytesOfRV_const (F : Fr) (n : Nat) {τ : STy} (v : RVal E.layout τ) : Const (bytesOfRV (Γ := Γ) F n v) := by
  unfold bytesOfRV; const_go [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const]
theorem encodeOne_const (F : Fr) (n : Nat) (packed : Bool) {τ : STy} (v : RVal E.layout τ) :
    Const (encodeOne (Γ := Γ) F n packed v) := by
  unfold encodeOne; const_go [bytesOfRV_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const]
theorem encodeParts_const (F : Fr) (n : Nat) (packed : Bool) :
    ∀ {τs : List STy} (vs : RVals E.layout τs), Const (encodeParts (Γ := Γ) F n packed vs)
  | _, .nil => Const.pure _
  | _, .cons v vs => Const.bind (encodeOne_const F n packed v) fun _ =>
      Const.bind (encodeParts_const F n packed vs) fun _ => Const.pure _
theorem encodeVals_const (F : Fr) (n : Nat) (packed : Bool) {τs : List STy} (vs : RVals E.layout τs) :
    Const (encodeVals (Γ := Γ) F n packed vs) := by
  unfold encodeVals; const_go [encodeParts_const]
theorem cdToMem_const (F : Fr) (τ : STy) (off len : Nat) : Const (cdToMem (E := E) (Γ := Γ) F τ off len) := by
  unfold cdToMem
  split
  · exact Const.pure _
  · split
    · exact Const.bind (allocRef_const _) fun _ => Const.pure _
    · exact Const.bind (allocRef_const _) fun _ => Const.pure _
    · exact Const.bind (List.mapM_const _ (fun _ => Const.lift _) _) fun _ =>
        Const.bind (allocRef_const _) fun _ => Const.pure _
    · exact Const.halt _
theorem convRV_const (F : Fr) (n : Nat) {σ : STy} (τ : STy) (v : RVal E.layout σ) :
    Const (convRV (Γ := Γ) F n τ v) := by
  unfold convRV; const_go [cdToMem_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const]
theorem pushVals_const {Γ' : RCtx} (F : Fr) (n : Nat) : ∀ (slots : List (Option STy)) {σs : List STy}
    (vs : RVals E.layout σs) {Γ : RCtx} (l : Locals E.layout Γ), Const (pushVals (Γ' := Γ') F n slots vs l)
  | [], _, .nil, _, _ => Const.pure _
  | [], _, .cons _ _, _, _ => Const.halt _
  | Option.none :: _, _, .nil, _, _ => Const.halt _
  | Option.none :: ss, _, .cons _ vs, _, l => pushVals_const F n ss vs l
  | Option.some _ :: _, _, .nil, _, _ => Const.halt _
  | Option.some τ :: ss, _, .cons v vs, _, l =>
    Const.bind (convRV_const F n τ v) fun w => Const.bind (getV_const w) fun _ => pushVals_const F n ss vs _

theorem convExplicitRV_const (F : Fr) (n : Nat) {σ : STy} (τ : STy) (v : RVal E.layout σ) :
    Const (convExplicitRV (Γ := Γ) F n τ v) := by
  unfold convExplicitRV; const_go [convRV_const, pushVals_const, bytesOfRV_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const]
theorem writeLoc_const (F : Fr) (n : Nat) {τ : STy} (loc : Loc E.layout Γ τ) (v : Val E.layout τ) :
    Const (writeLoc F n loc v) := by
  unfold writeLoc; const_go [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const]
theorem deleteLoc_const (F : Fr) (n : Nat) {τ : STy} (loc : Loc E.layout Γ τ) : Const (deleteLoc F n loc) := by
  unfold deleteLoc; const_go [writeLoc_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const]
theorem keyStep_const (F : Fr) (n : Nat) {τ : STy} (k : RVal E.layout τ) : Const (keyStep (Γ := Γ) F n k) := by
  unfold keyStep; const_go [bytesOfRV_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const]
theorem zeroVals_const (n : Nat) : ∀ (τs : List STy), Const (zeroVals (E := E) (Γ := Γ) n τs)
  | [] => Const.pure _
  | τ :: τs => Const.bind (zeroVal_const n τ) fun _ => Const.bind (zeroVals_const n τs) fun _ => Const.pure _
theorem zeroInner_const (n : Nat) : ∀ (k : Nat) {Γ' : RCtx} (l : Locals E.layout Γ'),
    Const (zeroInner (Γ' := Γ) n k l)
  | 0, _, _ => Const.pure _
  | _ + 1, _, .nil => Const.pure _
  | k + 1, _, .cons _ r => Const.bind (zeroVal_const n _) fun _ => Const.bind (zeroInner_const n k r) fun _ => Const.pure _
theorem copyInto_const (F : Fr) (n : Nat) (τ : STy) (p : SPath) {σ : STy} (v : RVal E.layout σ) :
    Const (copyInto (Γ := Γ) F n τ p v) := by
  unfold copyInto; const_go [cdToMem_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const]
theorem extReturn_const (rs : List STy) (o : Outcome) : Const (extReturn (E := E) (Γ := Γ) rs o) := by
  unfold extReturn; const_go [reraise_const]
theorem getterPath_const (F : Fr) (n : Nat) (data : Solidity.Roadmap.Bytes) : ∀ (τ : STy) (p : SPath) (i : Nat),
    Const (getterPath (E := E) (Γ := Γ) F n data τ p i)
  | .mapping k v, p, i => by
    simp only [getterPath]
    const_go [keyStep_const, getterPath_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const]
  | .array _ τ len, p, i => by
    simp only [getterPath]
    const_go [getterPath_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const]
  | .int _, _, _ | .bool, _, _ | .address _, _, _ | .fixedBytes _ _, _, _ | .fixed _, _, _ | .enum _, _, _
  | .udvt _, _, _ | .contract _, _, _ | .bytes _, _, _ | .string _, _, _ | .struct _ _, _, _
  | .fn _ _ _ _, _, _ | .rational _, _, _ | .hexConst _ _, _, _ | .stringLit _, _, _ | .tuple _, _, _ =>
    Const.pure _

end

theorem Const.map {Γ : RCtx} {α β : Type} (f : α → β) {m : EM E Γ α} (h : Const m) : Const (f <$> m) := by
  intro x
  show ((m >>= fun a => (Pure.pure (f a) : EM E Γ β)).run x).2.2.events = x.2.events
  exact Const.bind h (fun _ => Const.pure _) x

end Solidity.Source
