import Solidity.Source.Horizon.Below

/-!
# Horizons: every interpreter function only appends events

Part of `Solidity/Source/Horizon.lean` (S05 item 2), split from it to keep each
module under the 8 GiB pre-gate bound: `Grow` lemmas for the helpers, the
`grow_go` tactic and `growAt`.
-/

namespace Solidity.Source

open EM
open Solidity.Roadmap (Address Word Bytes Request Outcome Event)

variable {E : Env}

/-! ## Events only grow -/

theorem run_st {Γ : RCtx} (x : Locals E.layout Γ × St E) : (st : EM E Γ (St E)).run x = (.ok x.2, x) := rfl

theorem Grow.get {Γ : RCtx} : Grow (get : EM E Γ (Locals E.layout Γ × St E)) := fun _ => List.prefix_refl _
theorem Grow.st {Γ : RCtx} : Grow (st : EM E Γ (St E)) := fun _ => List.prefix_refl _
theorem Grow.locals {Γ : RCtx} : Grow (locals : EM E Γ (Locals E.layout Γ)) := fun _ => List.prefix_refl _
theorem Grow.setLocals {Γ : RCtx} (l : Locals E.layout Γ) : Grow (setLocals l : EM E Γ Unit) :=
  fun _ => List.prefix_refl _
theorem Grow.modSt {Γ : RCtx} (f : St E → St E) (hf : ∀ s, s.events <+: (f s).events) :
    Grow (modSt f : EM E Γ Unit) := fun x => hf x.2
theorem Grow.lift {Γ : RCtx} {α : Type} (r : R α) : Grow (lift r : EM E Γ α) := by
  cases r <;> exact fun _ => List.prefix_refl _
theorem Grow.sub {Γ Γ' : RCtx} {α : Type} (l' : Locals E.layout Γ') {m : EM E Γ' α} (h : Grow m) :
    Grow (EM.sub (Γ := Γ) l' m) := by
  intro x
  rcases x with ⟨l, s⟩
  rw [run_sub]
  have := h (l', s)
  rcases hr : m.run (l', s) with ⟨r, l'', s'⟩
  rw [hr] at this
  cases r <;> exact this
theorem Grow.attempt {Γ : RCtx} {α : Type} {m : EM E Γ α} (h : Grow m) : Grow (EM.attempt m) := by
  intro x
  rw [run_attempt]
  exact h x

theorem heapPut_grow {Γ : RCtx} (a : Nat) (x : Σ τ, Data E.layout τ) : Grow (heapPut (Γ := Γ) a x) := by
  intro y
  unfold heapPut
  rw [run_bind, run_st]
  dsimp only
  split
  · exact List.prefix_refl _
  · exact List.prefix_refl _

theorem alloc_grow {Γ : RCtx} {τ : STy} (x : Data E.layout τ) : Grow (alloc (Γ := Γ) x) := by
  intro y
  unfold alloc
  rw [run_bind, run_st]
  exact List.prefix_refl _

/-- Close `Grow body`: through binds, `match`es and `if`s, by the given
lemmas at the calls; a `modSt` keeps or appends events. -/
syntax "grow_go" "[" ident,* "]" : tactic
macro_rules
  | `(tactic| grow_go [$ls,*]) => `(tactic| repeat' (first
      | (with_reducible exact Grow.pure _)
      | (with_reducible exact Grow.halt _)
      | (with_reducible exact Grow.st)
      | (with_reducible exact Grow.get)
      | (with_reducible exact Grow.locals)
      | (with_reducible exact Grow.setLocals _)
      | (with_reducible exact Grow.lift _)
      | (with_reducible apply Grow.modSt; intro _; first | exact List.prefix_refl _ | exact List.prefix_append _ _)
      | (first $[| with_reducible apply $ls:ident]*)
      | (with_reducible apply Grow.sub)
      | (with_reducible apply Grow.attempt)
      | (with_reducible apply Grow.map)
      | (refine Grow.bind ?_ ?_)
      | (with_reducible intro _)
      | split
      | (intro _; exact List.prefix_refl _)
      | (dsimp only)))

section
variable {Γ : RCtx}

theorem getV_grow {τ : STy} (v : RVal E.layout τ) : Grow (getV (Γ := Γ) v) := Grow.lift _
theorem readCell_grow (F : Fr) (p : SPath) : Grow (readCell (E := E) (Γ := Γ) F p) := by
  unfold readCell; grow_go []
theorem readAt_grow (F : Fr) (p : SPath) (τ : STy) : Grow (readAt (E := E) (Γ := Γ) F p τ) := by
  unfold readAt; grow_go [readCell_grow]
theorem applyOp_grow (F : Fr) (o : Op E.layout E.lay E.lay) : Grow (applyOp (Γ := Γ) F o) := by
  unfold applyOp; grow_go []
theorem setCell_grow (F : Fr) (p : SPath) (o : Option (Val E.layout (E.cellTy p))) :
    Grow (setCell (Γ := Γ) F p o) := by
  unfold setCell; grow_go [applyOp_grow]
theorem writeAt_grow {τ : STy} (F : Fr) (p : SPath) (v : Val E.layout τ) : Grow (writeAt (Γ := Γ) F p v) := by
  unfold writeAt; grow_go [setCell_grow]
theorem readLen_grow (F : Fr) (p : SPath) : Grow (readLen (E := E) (Γ := Γ) F p) := by
  unfold readLen; grow_go [readAt_grow]
theorem writeLen_grow (F : Fr) (p : SPath) (k : Nat) : Grow (writeLen (E := E) (Γ := Γ) F p k) := by
  unfold writeLen; grow_go [writeAt_grow]
theorem heapObj_grow (a : Nat) : Grow (heapObj (E := E) (Γ := Γ) a) := by
  unfold heapObj; grow_go []
theorem heapAt_grow (a : Nat) (τ : STy) : Grow (heapAt (E := E) (Γ := Γ) a τ) := by
  unfold heapAt; grow_go [heapObj_grow]
theorem heapBytes_grow (a : Nat) : Grow (heapBytes (E := E) (Γ := Γ) a) := by
  unfold heapBytes; grow_go [heapObj_grow]
theorem allocRef_grow {τ : STy} (x : Data E.layout τ) : Grow (allocRef (Γ := Γ) x) := by
  unfold allocRef; grow_go [alloc_grow]
theorem storRef_grow (τ : STy) (p : SPath) : Grow (storRef (E := E) (Γ := Γ) τ p) := by
  unfold storRef; grow_go []

end

section
variable {Γ : RCtx}

mutual
theorem zeroData_grow : ∀ (n : Nat) (τ : STy), Grow (zeroData (E := E) (Γ := Γ) n τ)
  | 0, _ => Grow.halt _
  | n + 1, τ => by
    simp only [zeroData]
    grow_go [zeroElems_grow, zeroFields_grow, zeroVal_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow]
theorem zeroVal_grow : ∀ (n : Nat) (τ : STy), Grow (zeroVal (E := E) (Γ := Γ) n τ)
  | 0, _ => Grow.halt _
  | n + 1, τ => by
    simp only [zeroVal]
    grow_go [zeroData_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow]
theorem zeroElems_grow : ∀ (n : Nat) (σ : STy) (m : Nat), Grow (zeroElems (E := E) (Γ := Γ) n σ m)
  | 0, _, m => by cases m <;> exact Grow.halt _
  | n + 1, _, 0 => Grow.pure _
  | n + 1, σ, m + 1 => Grow.bind (zeroVal_grow n σ) fun _ => Grow.bind (zeroElems_grow n σ m) fun _ => Grow.pure _
theorem zeroFields_grow : ∀ (n : Nat) (τs : List STy), Grow (zeroFields (E := E) (Γ := Γ) n τs)
  | 0, τs => by cases τs <;> exact Grow.halt _
  | n + 1, [] => Grow.pure _
  | n + 1, τ :: τs => Grow.bind (zeroVal_grow n τ) fun _ => Grow.bind (zeroFields_grow n τs) fun _ => Grow.pure _
end

mutual
theorem loadMem_grow (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath), Grow (loadMem (E := E) (Γ := Γ) F n τ p)
  | 0, _, _ => Grow.halt _
  | n + 1, τ, p => by
    simp only [loadMem]
    grow_go [loadBytes_grow, loadElems_grow, loadFields_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow]
theorem loadElem_grow (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath), Grow (loadElem (E := E) (Γ := Γ) F n τ p)
  | 0, _, _ => Grow.halt _
  | n + 1, τ, p => by
    simp only [loadElem]
    grow_go [loadMem_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow]
theorem loadElems_grow (F : Fr) : ∀ (n : Nat) (σ : STy) (p : SPath) (i m : Nat),
    Grow (loadElems (E := E) (Γ := Γ) F n σ p i m)
  | 0, _, _, _, m => by cases m <;> exact Grow.halt _
  | n + 1, _, _, _, 0 => Grow.pure _
  | n + 1, σ, p, i, m + 1 => Grow.bind (loadElem_grow F n σ _) fun _ =>
      Grow.bind (loadElems_grow F n σ p (i + 1) m) fun _ => Grow.pure _
theorem loadFields_grow (F : Fr) : ∀ (n : Nat) (τs : List STy) (p : SPath) (i : Nat),
    Grow (loadFields (E := E) (Γ := Γ) F n τs p i)
  | 0, τs, _, _ => by cases τs <;> exact Grow.halt _
  | n + 1, [], _, _ => Grow.pure _
  | n + 1, τ :: τs, p, i => Grow.bind (loadElem_grow F n τ _) fun _ =>
      Grow.bind (loadFields_grow F n τs p (i + 1)) fun _ => Grow.pure _
theorem loadBytes_grow (F : Fr) : ∀ (n : Nat) (p : SPath) (i k : Nat), Grow (loadBytes (E := E) (Γ := Γ) F n p i k)
  | 0, _, _, k => by cases k <;> exact Grow.halt _
  | n + 1, _, _, 0 => Grow.pure _
  | n + 1, p, i, k + 1 => by
    refine Grow.bind (readAt_grow F _ _) fun v => ?_
    cases v <;> first
      | exact Grow.bind (loadBytes_grow F n p (i + 1) k) fun _ => Grow.pure _
      | (rename_i h; cases h)
end

mutual
theorem deleteStor_grow (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath), Grow (deleteStor (E := E) (Γ := Γ) F n τ p)
  | 0, _, _ => Grow.halt _
  | n + 1, τ, p => by
    simp only [deleteStor]
    grow_go [deleteRange_grow, deleteFields_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow]
theorem deleteRange_grow (F : Fr) : ∀ (n : Nat) (σ : STy) (p : SPath) (i k : Nat),
    Grow (deleteRange (E := E) (Γ := Γ) F n σ p i k)
  | 0, _, _, _, k => by cases k <;> exact Grow.halt _
  | n + 1, _, _, _, 0 => Grow.pure _
  | n + 1, σ, p, i, k + 1 => Grow.bind (deleteStor_grow F n σ _) fun _ => deleteRange_grow F n σ p (i + 1) k
theorem deleteFields_grow (F : Fr) : ∀ (n : Nat) (τs : List STy) (p : SPath) (i : Nat),
    Grow (deleteFields (E := E) (Γ := Γ) F n τs p i)
  | 0, τs, _, _ => by cases τs <;> exact Grow.halt _
  | n + 1, [], _, _ => Grow.pure _
  | n + 1, τ :: τs, p, i => Grow.bind (deleteStor_grow F n τ _) fun _ => deleteFields_grow F n τs p (i + 1)
end

mutual
theorem storeData_grow (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath) {σ : STy} (x : Data E.layout σ),
    Grow (storeData (Γ := Γ) F n τ p x)
  | 0, _, _, _, _ => Grow.halt _
  | n + 1, τ, p, _, x => by
    simp only [storeData]
    grow_go [storeBytes_grow, deleteRange_grow, storeElems_grow, storeFields_grow, storeVal_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow]
theorem storeVal_grow (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath) {σ : STy} (v : Val E.layout σ),
    Grow (storeVal (Γ := Γ) F n τ p v)
  | 0, _, _, _, _ => Grow.halt _
  | n + 1, τ, p, _, v => by
    simp only [storeVal]
    grow_go [storeData_grow, loadMem_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow]
theorem storeElems_grow (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath) (i len : Nat) {σ : STy}
    (xs : Fin len → Data E.layout σ), Grow (storeElems (Γ := Γ) F n τ p i len xs)
  | 0, _, _, _, len, _, _ => by cases len <;> exact Grow.halt _
  | n + 1, _, _, _, 0, _, _ => Grow.pure _
  | n + 1, τ, p, i, len + 1, _, xs =>
    Grow.bind (storeData_grow F n τ _ _) fun _ => storeElems_grow F n τ p (i + 1) len _
theorem storeFields_grow (F : Fr) : ∀ (n : Nat) (τs : List STy) (p : SPath) (i : Nat) {σs : List STy}
    (xs : DataList E.layout σs), Grow (storeFields (Γ := Γ) F n τs p i xs)
  | 0, τs, _, _, _, xs => by cases τs <;> cases xs <;> exact Grow.halt _
  | n + 1, [], _, _, _, _ => Grow.pure _
  | n + 1, _ :: _, _, _, _, .nil => Grow.pure _
  | n + 1, τ :: τs, p, i, _, .cons x xs =>
    Grow.bind (storeData_grow F n τ _ x) fun _ => storeFields_grow F n τs p (i + 1) xs
theorem storeBytes_grow (F : Fr) : ∀ (n : Nat) (p : SPath) (i : Nat) (bs : List UInt8),
    Grow (storeBytes (E := E) (Γ := Γ) F n p i bs)
  | 0, _, _, bs => by cases bs <;> exact Grow.halt _
  | n + 1, _, _, [] => Grow.pure _
  | n + 1, p, i, b :: bs => Grow.bind (writeAt_grow F _ _) fun _ => storeBytes_grow F n p (i + 1) bs
end

end

section
variable {Γ : RCtx}

theorem List.mapM_grow {Γ : RCtx} {α β : Type} (f : α → EM E Γ β) (hf : ∀ a, Grow (f a)) :
    ∀ (l : List α), Grow (l.mapM f) := by
  intro l
  suffices h : ∀ (acc : List β), Grow (List.mapM.loop f l acc) from h []
  induction l with
  | nil => intro acc; exact Grow.pure _
  | cons a as ih => intro acc; exact Grow.bind (hf a) fun b => ih (b :: acc)

theorem panicM_grow {α : Type} : Grow (memElem.panicM (E := E) (Γ := Γ) (α := α)) := Grow.lift _
theorem memElem_grow (a i : Nat) (τ : STy) : Grow (memElem (E := E) (Γ := Γ) a i τ) := by
  unfold memElem; grow_go [panicM_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow]
theorem readLoc_grow (F : Fr) {τ : STy} (loc : Loc E.layout Γ τ) : Grow (readLoc F loc) := by
  cases loc <;> simp only [readLoc] <;> grow_go [memElem_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow]
theorem memSet_grow (a i : Nat) {τ : STy} (v : Val E.layout τ) : Grow (memSet (Γ := Γ) a i v) := by
  unfold memSet; grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow]
theorem lengthOf_grow (F : Fr) {τ : STy} (v : Val E.layout τ) : Grow (lengthOf (Γ := Γ) F v) := by
  unfold lengthOf; grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow]
theorem indexLoc_grow (F : Fr) {l : DataLoc} {σ : STy} {k : Option Nat} (a : Val E.layout (.array l σ k))
    (i : Nat) : Grow (indexLoc (Γ := Γ) F a i) := by
  unfold indexLoc; grow_go [lengthOf_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow]
theorem indexNat_grow {σ : STy} (v : RVal E.layout σ) : Grow (indexNat (Γ := Γ) v) := Grow.lift _
theorem instanceAt_grow (G : Glob E) (a : Address) : Grow (instanceAt (Γ := Γ) G a) := by
  unfold instanceAt; grow_go []
theorem emitEvent_grow (e : Event) : Grow (emitEvent (E := E) (Γ := Γ) e) := by
  unfold emitEvent; grow_go []
theorem credit_grow (a : Address) (v : Word) : Grow (credit (E := E) (Γ := Γ) a v) := by
  unfold credit; grow_go []
theorem debit_grow (a : Address) (v : Word) : Grow (debit (E := E) (Γ := Γ) a v) := by
  unfold debit; grow_go []
theorem mark_grow : Grow (mark (E := E) (Γ := Γ)) := by
  unfold mark; grow_go []
theorem rollbackTo_grow (m : Nat × Nat × Heap E.layout) : Grow (rollbackTo (Γ := Γ) m) := by
  unfold rollbackTo; grow_go []
theorem reraise_grow (o : Outcome) : Grow (reraise (E := E) (Γ := Γ) o) := by
  unfold reraise; grow_go []
theorem fieldsOf_grow : ∀ {ps : List STy} (vs : Vals E.layout ps) (τs : List STy),
    Grow (fieldsOf (E := E) (Γ := Γ) vs τs)
  | _, .nil, [] => Grow.pure _
  | _, .nil, _ :: _ => Grow.halt _
  | _, .cons _ _, [] => Grow.halt _
  | _, .cons (τ := σ) v vs, τ :: τs => by
    simp only [fieldsOf]
    split
    · exact Grow.bind (fieldsOf_grow vs τs) fun _ => Grow.pure _
    · exact Grow.halt _
theorem ret32_grow (τ : STy) (bs : Bytes) : Grow (ret32 (E := E) (Γ := Γ) τ bs) := by
  unfold ret32; grow_go []
theorem tailBytes_grow (data : Bytes) (i : Nat) : Grow (tailBytes (E := E) (Γ := Γ) data i) := by
  unfold tailBytes
  dsimp only
  split
  · exact Grow.halt _
  · split
    · exact Grow.lift _
    · split
      · exact Grow.pure _
      · exact Grow.halt _
theorem decodeArg_grow (data : Bytes) (i : Nat) (τ : STy) : Grow (decodeArg (E := E) (Γ := Γ) data i τ) := by
  unfold decodeArg
  split
  · split
    · exact Grow.bind (tailBytes_grow data i) fun _ => allocRef_grow _
    · exact Grow.lift _
    · exact Grow.lift _
  · split
    · exact Grow.bind (tailBytes_grow data i) fun _ => allocRef_grow _
    · exact Grow.lift _
    · exact Grow.lift _
  · split
    · split
      · dsimp only
        split
        · exact Grow.halt _
        · split
          · exact Grow.lift _
          · split
            · exact Grow.bind (List.mapM_grow _ (fun _ => Grow.lift _) _) fun _ => allocRef_grow _
            · exact Grow.halt _
      · exact Grow.halt _
    · split
      · exact Grow.lift _
      · exact Grow.halt _
    · exact Grow.lift _
  · exact Grow.lift _
theorem decodeArgs_grow (data : Bytes) : ∀ (τs : List STy) (i : Nat), Grow (decodeArgs (E := E) (Γ := Γ) data τs i)
  | [], _ => Grow.pure _
  | τ :: τs, i => Grow.bind (decodeArg_grow data i τ) fun _ =>
      Grow.bind (decodeArgs_grow data τs (i + 1)) fun _ => Grow.pure _

end

theorem abiDecodeData_grow (data : Bytes) (τs : List STy) : Grow (abiDecodeData (E := E) (Γ := Γ) data τs) := by
  unfold abiDecodeData
  split
  · exact Grow.halt _
  · exact Grow.bind (decodeArgs_grow data τs 0) fun _ => Grow.pure _

section
variable {Γ : RCtx}

theorem bytesOfRV_grow (F : Fr) (n : Nat) {τ : STy} (v : RVal E.layout τ) : Grow (bytesOfRV (Γ := Γ) F n v) := by
  unfold bytesOfRV; grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow]
theorem encodeOne_grow (F : Fr) (n : Nat) (packed : Bool) {τ : STy} (v : RVal E.layout τ) :
    Grow (encodeOne (Γ := Γ) F n packed v) := by
  unfold encodeOne; grow_go [bytesOfRV_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow]
theorem encodeParts_grow (F : Fr) (n : Nat) (packed : Bool) :
    ∀ {τs : List STy} (vs : RVals E.layout τs), Grow (encodeParts (Γ := Γ) F n packed vs)
  | _, .nil => Grow.pure _
  | _, .cons v vs => Grow.bind (encodeOne_grow F n packed v) fun _ =>
      Grow.bind (encodeParts_grow F n packed vs) fun _ => Grow.pure _
theorem encodeVals_grow (F : Fr) (n : Nat) (packed : Bool) {τs : List STy} (vs : RVals E.layout τs) :
    Grow (encodeVals (Γ := Γ) F n packed vs) := by
  unfold encodeVals; grow_go [encodeParts_grow]
theorem cdToMem_grow (F : Fr) (τ : STy) (off len : Nat) : Grow (cdToMem (E := E) (Γ := Γ) F τ off len) := by
  unfold cdToMem
  split
  · exact Grow.pure _
  · split
    · exact Grow.bind (allocRef_grow _) fun _ => Grow.pure _
    · exact Grow.bind (allocRef_grow _) fun _ => Grow.pure _
    · exact Grow.bind (List.mapM_grow _ (fun _ => Grow.lift _) _) fun _ =>
        Grow.bind (allocRef_grow _) fun _ => Grow.pure _
    · exact Grow.halt _
theorem convRV_grow (F : Fr) (n : Nat) {σ : STy} (τ : STy) (v : RVal E.layout σ) :
    Grow (convRV (Γ := Γ) F n τ v) := by
  unfold convRV; grow_go [cdToMem_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow]
theorem pushVals_grow {Γ' : RCtx} (F : Fr) (n : Nat) : ∀ (slots : List (Option STy)) {σs : List STy}
    (vs : RVals E.layout σs) {Γ : RCtx} (l : Locals E.layout Γ), Grow (pushVals (Γ' := Γ') F n slots vs l)
  | [], _, .nil, _, _ => Grow.pure _
  | [], _, .cons _ _, _, _ => Grow.halt _
  | Option.none :: _, _, .nil, _, _ => Grow.halt _
  | Option.none :: ss, _, .cons _ vs, _, l => pushVals_grow F n ss vs l
  | Option.some _ :: _, _, .nil, _, _ => Grow.halt _
  | Option.some τ :: ss, _, .cons v vs, _, l =>
    Grow.bind (convRV_grow F n τ v) fun w => Grow.bind (getV_grow w) fun _ => pushVals_grow F n ss vs _

theorem convExplicitRV_grow (F : Fr) (n : Nat) {σ : STy} (τ : STy) (v : RVal E.layout σ) :
    Grow (convExplicitRV (Γ := Γ) F n τ v) := by
  unfold convExplicitRV; grow_go [convRV_grow, pushVals_grow, bytesOfRV_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow]
theorem writeLoc_grow (F : Fr) (n : Nat) {τ : STy} (loc : Loc E.layout Γ τ) (v : Val E.layout τ) :
    Grow (writeLoc F n loc v) := by
  unfold writeLoc; grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow]
theorem deleteLoc_grow (F : Fr) (n : Nat) {τ : STy} (loc : Loc E.layout Γ τ) : Grow (deleteLoc F n loc) := by
  unfold deleteLoc; grow_go [writeLoc_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow]
theorem keyStep_grow (F : Fr) (n : Nat) {τ : STy} (k : RVal E.layout τ) : Grow (keyStep (Γ := Γ) F n k) := by
  unfold keyStep; grow_go [bytesOfRV_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow]
theorem zeroVals_grow (n : Nat) : ∀ (τs : List STy), Grow (zeroVals (E := E) (Γ := Γ) n τs)
  | [] => Grow.pure _
  | τ :: τs => Grow.bind (zeroVal_grow n τ) fun _ => Grow.bind (zeroVals_grow n τs) fun _ => Grow.pure _
theorem zeroInner_grow (n : Nat) : ∀ (k : Nat) {Γ' : RCtx} (l : Locals E.layout Γ'),
    Grow (zeroInner (Γ' := Γ) n k l)
  | 0, _, _ => Grow.pure _
  | _ + 1, _, .nil => Grow.pure _
  | k + 1, _, .cons _ r => Grow.bind (zeroVal_grow n _) fun _ => Grow.bind (zeroInner_grow n k r) fun _ => Grow.pure _
theorem copyInto_grow (F : Fr) (n : Nat) (τ : STy) (p : SPath) {σ : STy} (v : RVal E.layout σ) :
    Grow (copyInto (Γ := Γ) F n τ p v) := by
  unfold copyInto; grow_go [cdToMem_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow]
theorem extReturn_grow (rs : List STy) (o : Outcome) : Grow (extReturn (E := E) (Γ := Γ) rs o) := by
  unfold extReturn; grow_go [reraise_grow]
theorem getterPath_grow (F : Fr) (n : Nat) (data : Solidity.Roadmap.Bytes) : ∀ (τ : STy) (p : SPath) (i : Nat),
    Grow (getterPath (E := E) (Γ := Γ) F n data τ p i)
  | .mapping k v, p, i => by
    simp only [getterPath]
    grow_go [keyStep_grow, getterPath_grow, extReturn_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow]
  | .array _ τ len, p, i => by
    simp only [getterPath]
    grow_go [getterPath_grow, extReturn_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow]
  | .int _, _, _ | .bool, _, _ | .address _, _, _ | .fixedBytes _ _, _, _ | .fixed _, _, _ | .enum _, _, _
  | .udvt _, _, _ | .contract _, _, _ | .bytes _, _, _ | .string _, _, _ | .struct _ _, _, _
  | .fn _ _ _ _, _, _ | .rational _, _, _ | .hexConst _ _, _, _ | .stringLit _, _, _ | .tuple _, _, _ =>
    Grow.pure _

end

theorem Grow.map {Γ : RCtx} {α β : Type} (f : α → β) {m : EM E Γ α} (h : Grow m) : Grow (f <$> m) := by
  intro x
  show x.2.events <+: ((m >>= fun a => (Pure.pure (f a) : EM E Γ β)).run x).2.2.events
  exact Grow.bind h (fun _ => Grow.pure _) x

/-! ### Every interpreter function only appends events -/

structure GrowAt (G : Glob E) (n : Nat) : Prop where
  evalE : ∀ (F : Fr) ⦃Γ : RCtx⦄ ⦃τ : STy⦄ (e : RExpr E Γ τ), Grow (evalE G F n e)
  evalPair : ∀ (F : Fr) ⦃Γ : RCtx⦄ ⦃σ τ : STy⦄ (a : RExpr E Γ σ) (b : RExpr E Γ τ), Grow (evalPair G F n a b)
  evalArgs : ∀ (F : Fr) ⦃Γ : RCtx⦄ ⦃τs : List STy⦄ (es : RArgs E Γ τs), Grow (evalArgs G F n es)
  evalConvArgs : ∀ (F : Fr) ⦃Γ : RCtx⦄ ⦃τs : List STy⦄ (es : RConvArgs E Γ τs), Grow (evalConvArgs G F n es)
  evalLoc : ∀ (F : Fr) ⦃Γ : RCtx⦄ ⦃τ : STy⦄ (l : RLVal E Γ τ), Grow (evalLoc G F n l)
  evalBuiltin : ∀ (F : Fr) ⦃Γ : RCtx⦄ ⦃σs : List STy⦄ (b : Builtin) (args : RArgs E Γ σs) (τ : STy), Grow (evalBuiltin G F n b args τ)
  evalArgsRev : ∀ (F : Fr) ⦃Γ : RCtx⦄ ⦃τs : List STy⦄ (es : RArgs E Γ τs), Grow (evalArgsRev G F n es)
  pay : ∀ (F : Fr) ⦃Γ : RCtx⦄ (a : RExpr E Γ (.address true)) (v : RExpr E Γ (.int IntTy.u256)), Grow (pay G F n a v)
  execS : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) ⦃R : List STy⦄ ⦃M : Bool⦄ ⦃k : SCtx⦄ ⦃Γ Γ' : RCtx⦄ (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ), Grow (execS G F n nps ph s l)
  forIter : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) ⦃R : List STy⦄ ⦃M u : Bool⦄ ⦃Γ₁ Γ₂ : RCtx⦄ (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂) (l : Locals E.layout Γ₁), Grow (forIter G F n nps ph c post body l)
  execItems : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) ⦃R : List STy⦄ ⦃M : Bool⦄ ⦃k : SCtx⦄ ⦃Γ Γ' : RCtx⦄ (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ), Grow (execItems G F n nps ph b l)
  runMods : ∀ (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals)) (l : Locals E.layout b.locals), Grow (runMods G F n b mods l)
  callInternal : ∀ (F : Fr) (d : Decl) ⦃ps : List STy⦄ (vs : Vals E.layout ps) (rs : List STy), Grow (callInternal G F n d vs rs)
  callAddr : ∀ (F : Fr) (a : Address) (v : Word) (input : Bytes) (static : Bool), Grow (callAddr G F n a v input static)
  enterInstance : ∀ (a sender : Address) (v : Word) (input : Bytes) (static : Bool) (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout), Grow (enterInstance G n a sender v input static c depth m)
  envLoop : ∀ (depth : Nat) (pstatic : Bool), Grow (envLoop G n depth pstatic)
  dispatch : ∀ (F : Fr) (input : Bytes), Grow (dispatch G F n input)

theorem growAt_zero (G : Glob E) : GrowAt G 0 where
  evalE := by intros; rw [evalE.eq_1]; exact Grow.halt _
  evalPair := by intros; rw [evalPair.eq_1]; exact Grow.halt _
  evalArgs := by intros; rw [evalArgs.eq_1]; exact Grow.halt _
  evalConvArgs := by intros; rw [evalConvArgs.eq_1]; exact Grow.halt _
  evalLoc := by intros; rw [evalLoc.eq_1]; exact Grow.halt _
  evalBuiltin := by intros; rw [evalBuiltin.eq_1]; exact Grow.halt _
  evalArgsRev := by intros; rw [evalArgsRev.eq_1]; exact Grow.halt _
  pay := by intros; rw [pay.eq_1]; exact Grow.halt _
  execS := by intros; rw [execS.eq_1]; exact Grow.halt _
  forIter := by intros; rw [forIter.eq_1]; exact Grow.halt _
  execItems := by intros; rw [execItems.eq_1]; exact Grow.halt _
  runMods := by intros; rw [runMods.eq_1]; exact Grow.halt _
  callInternal := by intros; rw [callInternal.eq_1]; exact Grow.halt _
  callAddr := by intros; rw [callAddr.eq_1]; exact Grow.halt _
  enterInstance := by intros; rw [enterInstance.eq_1]; exact Grow.halt _
  envLoop := by intros; rw [envLoop.eq_1]; exact Grow.halt _
  dispatch := by intros; rw [dispatch.eq_1]; exact Grow.halt _

theorem evalE_grow_0 {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 0 ≤ e.ctorIdx ∧ e.ctorIdx < 12) : Grow (evalE G F (n + 1) e) := by
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (simp only [evalE]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow])
theorem evalE_grow_1 {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 12 ≤ e.ctorIdx ∧ e.ctorIdx < 24) : Grow (evalE G F (n + 1) e) := by
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (simp only [evalE]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow])
theorem evalE_grow_2 {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 24 ≤ e.ctorIdx ∧ e.ctorIdx < 36) : Grow (evalE G F (n + 1) e) := by
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (simp only [evalE]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow])
theorem evalE_grow_3 {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 36 ≤ e.ctorIdx ∧ e.ctorIdx < 60) : Grow (evalE G F (n + 1) e) := by
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (simp only [evalE]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow])
theorem evalE_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) :
    Grow (evalE G F (n + 1) e) := by
  by_cases h0 : e.ctorIdx < 12
  · exact evalE_grow_0 ih F e ⟨Nat.zero_le _, h0⟩
  by_cases h1 : e.ctorIdx < 24
  · exact evalE_grow_1 ih F e ⟨by omega, h1⟩
  by_cases h2 : e.ctorIdx < 36
  · exact evalE_grow_2 ih F e ⟨by omega, h2⟩
  have h3 : e.ctorIdx < 60 := by cases e <;> simp only [RExpr.ctorIdx] <;> omega
  exact evalE_grow_3 ih F e ⟨by omega, h3⟩
theorem evalPair_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {σ τ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ τ) :
    Grow (evalPair G F (n + 1) a b) := by
  simp only [evalPair]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem evalArgs_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Grow (evalArgs G F (n + 1) es) := by
  cases es <;> simp only [evalArgs] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem evalConvArgs_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs) :
    Grow (evalConvArgs G F (n + 1) es) := by
  cases es <;> simp only [evalConvArgs] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem evalLoc_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ) :
    Grow (evalLoc G F (n + 1) l) := by
  cases l <;> simp only [evalLoc] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem evalBuiltin_grow_0 {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .require ∨ b = .assert ∨ b = .revert) :
    Grow (evalBuiltin G F (n + 1) b args τ) := by
  rcases hb with rfl | rfl | rfl <;> simp only [evalBuiltin] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem evalBuiltin_grow_1 {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .keccak256 ∨ b = .sha256 ∨ b = .ripemd160) :
    Grow (evalBuiltin G F (n + 1) b args τ) := by
  rcases hb with rfl | rfl | rfl <;> simp only [evalBuiltin] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem evalBuiltin_grow_2 {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .addmod) :
    Grow (evalBuiltin G F (n + 1) b args τ) := by
  rcases hb with rfl <;> simp only [evalBuiltin] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem evalBuiltin_grow_3 {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .mulmod) :
    Grow (evalBuiltin G F (n + 1) b args τ) := by
  rcases hb with rfl <;> simp only [evalBuiltin] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem evalBuiltin_grow_4 {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .ecrecover) :
    Grow (evalBuiltin G F (n + 1) b args τ) := by
  rcases hb with rfl <;> simp only [evalBuiltin] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem evalBuiltin_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) : Grow (evalBuiltin G F (n + 1) b args τ) := by
  cases b
  all_goals first
    | exact evalBuiltin_grow_0 ih F _ args τ (by decide)
    | exact evalBuiltin_grow_1 ih F _ args τ (by decide)
    | exact evalBuiltin_grow_2 ih F _ args τ (by decide)
    | exact evalBuiltin_grow_3 ih F _ args τ (by decide)
    | exact evalBuiltin_grow_4 ih F _ args τ (by decide)
    | (simp only [evalBuiltin]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow])
theorem evalArgsRev_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Grow (evalArgsRev G F (n + 1) es) := by
  cases es <;> simp only [evalArgsRev] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem pay_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} (a : RExpr E Γ (.address true)) (v : RExpr E Γ (.int IntTy.u256)) :
    Grow (pay G F (n + 1) a v) := by
  simp only [pay]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem execS_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ) :
    Grow (execS G F (n + 1) nps ph s l) := by
  cases s <;> simp only [execS] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem forIter_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool} {Γ₁ Γ₂ : RCtx} (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂) (l : Locals E.layout Γ₁) :
    Grow (forIter G F (n + 1) nps ph c post body l) := by
  cases c <;> simp only [forIter] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem execItems_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx} (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ) :
    Grow (execItems G F (n + 1) nps ph b l) := by
  cases b <;> simp only [execItems] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem runMods_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals)) (l : Locals E.layout b.locals) :
    Grow (runMods G F (n + 1) b mods l) := by
  cases mods <;> simp only [runMods] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem callInternal_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps) (rs : List STy) :
    Grow (callInternal G F (n + 1) d vs rs) := by
  simp only [callInternal]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem callAddr_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (a : Address) (v : Word) (input : Bytes) (static : Bool) :
    Grow (callAddr G F (n + 1) a v input static) := by
  simp only [callAddr]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem enterInstance_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (a sender : Address) (v : Word) (input : Bytes) (static : Bool) (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout) :
    Grow (enterInstance G (n + 1) a sender v input static c depth m) := by
  simp only [enterInstance]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem envLoop_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (depth : Nat) (pstatic : Bool) :
    Grow (envLoop G (n + 1) depth pstatic) := by
  rw [envLoop.eq_2 G depth pstatic n]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem dispatch_grow_fn {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (input : Bytes) {d : Decl}
    (hp : G.pickFn F input = some d) (he : input.isEmpty = false) : Grow (dispatch G F (n + 1) input) := by
  simp only [dispatch, hp, he]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem dispatch_grow_getter_none_c {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy} {ri : RInit E}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = some ri) :
    Grow (dispatch G F (n + 1) input) := by
  simp only [dispatch, hp, hc, hg]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem dispatch_grow_getter_none_v {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy} {τ : STy}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = none) (hv : d.varTy E = some τ) :
    Grow (dispatch G F (n + 1) input) := by
  simp only [dispatch, hp, hc, hv, hg]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem dispatch_grow_getter_none_x {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy} 
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = none) (hv : d.varTy E = none) :
    Grow (dispatch G F (n + 1) input) := by
  simp only [dispatch, hp, hc, hv, hg]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem dispatch_grow_getter_none {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {r : Decl × List STy × STy} (hg : G.pickGetter F input = some r) :
    Grow (dispatch G F (n + 1) input) := by
  obtain ⟨d, ps, ρ⟩ := r
  cases hc : G.prog.consts d with
  | some ri => exact dispatch_grow_getter_none_c ih F input hp hg hc
  | none =>
    cases hv : d.varTy E with
    | some τ => exact dispatch_grow_getter_none_v ih F input hp hg hc hv
    | none => exact dispatch_grow_getter_none_x ih F input hp hg hc hv
theorem dispatch_grow_getter_some_c {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy} {ri : RInit E}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = some ri) :
    Grow (dispatch G F (n + 1) input) := by
  simp only [dispatch, hp, he, hc, hg]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem dispatch_grow_getter_some_v {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy} {τ : STy}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = none) (hv : d.varTy E = some τ) :
    Grow (dispatch G F (n + 1) input) := by
  simp only [dispatch, hp, he, hc, hv, hg]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem dispatch_grow_getter_some_x {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy} 
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = none) (hv : d.varTy E = none) :
    Grow (dispatch G F (n + 1) input) := by
  simp only [dispatch, hp, he, hc, hv, hg]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem dispatch_grow_getter_some {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {r : Decl × List STy × STy} (hg : G.pickGetter F input = some r) :
    Grow (dispatch G F (n + 1) input) := by
  obtain ⟨d, ps, ρ⟩ := r
  cases hc : G.prog.consts d with
  | some ri => exact dispatch_grow_getter_some_c ih F input hp he hg hc
  | none =>
    cases hv : d.varTy E with
    | some τ => exact dispatch_grow_getter_some_v ih F input hp he hg hc hv
    | none => exact dispatch_grow_getter_some_x ih F input hp he hg hc hv
theorem dispatch_grow_getter {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (input : Bytes) (b : Bool) {r : Decl × List STy × STy}
    (hm : (G.pickFn F input, input.isEmpty) = (none, b) ∨ ∃ d, (G.pickFn F input, input.isEmpty) = (some d, true))
    (hg : G.pickGetter F input = some r) : Grow (dispatch G F (n + 1) input) := by
  rcases hm with hm | ⟨d, hm⟩ <;> simp only [Prod.mk.injEq] at hm
  · exact dispatch_grow_getter_none ih F input hm.1 hg
  · exact dispatch_grow_getter_some ih F input hm.1 hm.2 hg
theorem dispatch_grow_special {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (input : Bytes) (b : Bool)
    (hm : (G.pickFn F input, input.isEmpty) = (none, b) ∨ ∃ d, (G.pickFn F input, input.isEmpty) = (some d, true))
    (hg : G.pickGetter F input = none) : Grow (dispatch G F (n + 1) input) := by
  rcases hm with hm | ⟨d, hm⟩ <;> simp only [Prod.mk.injEq] at hm <;> simp only [dispatch, hm.1, hm.2, hg] <;>
    grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem dispatch_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (input : Bytes) : Grow (dispatch G F (n + 1) input) := by
  cases hp : G.pickFn F input with
  | some d =>
    cases he : input.isEmpty with
    | false => exact dispatch_grow_fn ih F input hp he
    | true =>
      cases hg : G.pickGetter F input with
      | some r => exact dispatch_grow_getter ih F input true (.inr ⟨d, by rw [hp, he]⟩) hg
      | none => exact dispatch_grow_special ih F input true (.inr ⟨d, by rw [hp, he]⟩) hg
  | none =>
    cases hg : G.pickGetter F input with
    | some r => exact dispatch_grow_getter ih F input _ (.inl (by rw [hp])) hg
    | none => exact dispatch_grow_special ih F input _ (.inl (by rw [hp])) hg

theorem growAt (G : Glob E) : ∀ n, GrowAt G n
  | 0 => growAt_zero G
  | n + 1 =>
    have ih := growAt G n
    ⟨evalE_grow_step ih, evalPair_grow_step ih, evalArgs_grow_step ih, evalConvArgs_grow_step ih, evalLoc_grow_step ih, evalBuiltin_grow_step ih, evalArgsRev_grow_step ih, pay_grow_step ih, execS_grow_step ih, forIter_grow_step ih, execItems_grow_step ih, runMods_grow_step ih, callInternal_grow_step ih, callAddr_grow_step ih, enterInstance_grow_step ih, envLoop_grow_step ih, dispatch_grow_step ih⟩

end Solidity.Source
