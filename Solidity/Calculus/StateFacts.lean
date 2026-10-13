import Solidity.Update
import Solidity.Semantics.Properties
import Solidity.Theory.Bridge.Denote
import Solidity.Calculus.ReadWrite

/-!
# Facts about the interpreter's states and the typed symbols

Two kinds of facts.  Of the untyped interpreter (`Semantics.State`), which
the decision procedure and the Theory bridge still read: a result refining
another (`Res.Le`), two results returning alike (`Res.OkEq`), the parts of a
state a write reads (`State.HeapEq`, `StPartEq`, `MemPartEq`), a root read
member-wise (`State.selectRoot`, `State.frameOf`), and the shapes of the
paths a law's side condition reads (`SegT`).  Of the typed signature
(`Signature.lean`): its symbols are monotone in their arguments (`OLe`,
`Op1.eval_le` …), what a rewrite of an update's right-hand sides reads
(`Calculus/SeqRewrite.lean`).

The facts about the untyped symbols (`Srt.Le`, `Srt.DEquiv`,
`Srt.AgreePart`, `OpN.eval_part`, `State.Keeps`, …) went with those symbols
(W9.8.3c): a typed term reads the typed state, and the facts a law needs are
stated on it where the law is.
-/

namespace Solidity

/-! ## From `Solidity.Calculus.TermRules` -/

section
open Semantics SemanticsProperties Theory
variable {C : Contract}

theorem Theory.StValue.Equiv.eq_or_st {v w : StValue} (h : StValue.Equiv v w) :
    v = w ∨ ∃ s t, v = .st s ∧ w = .st t := by
  cases v with
  | prim p => exact Or.inl (StValue.Equiv.prim_iff.1 h.symm).symm
  | st s => cases w with
    | prim p => cases StValue.Equiv.prim_iff.1 h
    | st t => exact Or.inr ⟨s, t, rfl, rfl⟩

/-- Equivalent values are one interpreter result. -/
theorem Theory.StValue.Equiv.toRes {v w : StValue} (h : StValue.Equiv v w) :
    v.toRes = w.toRes := by
  rcases h.eq_or_st with rfl | ⟨s, t, rfl, rfl⟩ <;> rfl

end


section
open Semantics
variable {C : Contract}
section RwEval

/-- Where `a` returns a value, `b` returns it too. -/
def Semantics.Res.Le {α : Type} (a b : Res α) : Prop := ∀ x, a = .ok x → b = .ok x

theorem Semantics.Res.Le.refl {α : Type} (a : Res α) : Res.Le a a := fun _ h => h

theorem Semantics.Res.Le.bind {α β : Type} {a a' : Res α} {f f' : α → Res β} (ha : Res.Le a a')
    (hf : ∀ x, Res.Le (f x) (f' x)) : Res.Le (a >>= f) (a' >>= f') := fun y h => by
  obtain ⟨x, hx, hy⟩ := bind_ok_inv h
  rw [ha x hx]
  exact hf x y hy

theorem evalBinop_le {op : BinOp} {p : PrimTy} {v : Value} {b b' : Res Value} (hb : Res.Le b b') :
    Res.Le (evalBinop op p v b) (evalBinop op p v b') := by
  unfold evalBinop
  split
  · exact Res.Le.refl _
  · exact Res.Le.refl _
  · exact Res.Le.bind hb fun _ => Res.Le.refl _

theorem pickBranch_le {c : Value} {a a' b b' : Res Value} (ha : Res.Le a a') (hb : Res.Le b b') :
    Res.Le (pickBranch c a b) (pickBranch c a' b') := by
  unfold pickBranch
  split
  · exact ha
  · exact hb
  · exact Res.Le.refl _

end RwEval
end


/-! ## From `Solidity.Calculus.StateParts` -/

section
open Semantics SemanticsProperties
variable {C : Contract}

/-- The parts of a state neither a storage or memory term nor a local
writes: the ledger, the funds and the transaction. -/
structure Semantics.State.Rest (σ τ : Semantics.State) : Prop where
  net : σ.net = τ.net
  selfBalance : σ.selfBalance = τ.selfBalance
  tx : σ.tx = τ.tx

/-- Two states of one storage, and of one heap and next identity. -/
def Semantics.State.HeapEq (σ τ : Semantics.State) : Prop := σ.heap = τ.heap ∧ σ.nextId = τ.nextId

/-- What a storage write takes of a storage reading. -/
def Semantics.Res.stPart (a : Res Semantics.State) : Res (List (Name × Semantics.SVal)) := a.map (·.storage)

/-- What a memory write takes of a memory reading. -/
def Semantics.Res.memPart (a : Res Semantics.State) : Res (List (Nat × MObj) × Nat) := a.map fun ρ => (ρ.heap, ρ.nextId)

/-- Two storage readings of one storage (a structure, so that a match on a
reading does not split it). -/
structure StPartEq (a b : Res Semantics.State) : Prop where
  eq : Res.stPart a = Res.stPart b

/-- Two memory readings of one heap and next identity. -/
structure MemPartEq (a b : Res Semantics.State) : Prop where
  eq : Res.memPart a = Res.memPart b

theorem Semantics.Res.stPart_cases {a b : Res Semantics.State} (h : Res.stPart a = Res.stPart b) :
    (∃ e, a = .error e ∧ b = .error e) ∨
      ∃ τ₁ τ₂, a = .ok τ₁ ∧ b = .ok τ₂ ∧ τ₁.storage = τ₂.storage := by
  cases a with
  | error e =>
    cases b with
    | error e' =>
      simp only [Res.stPart, Except.map, Except.error.injEq] at h
      exact Or.inl ⟨e, rfl, by rw [h]⟩
    | ok _ => simp [Res.stPart, Except.map] at h
  | ok τ₁ =>
    cases b with
    | error _ => simp [Res.stPart, Except.map] at h
    | ok τ₂ =>
      simp only [Res.stPart, Except.map, Except.ok.injEq] at h
      exact Or.inr ⟨τ₁, τ₂, rfl, rfl, h⟩

theorem Semantics.Res.memPart_cases {a b : Res Semantics.State} (h : Res.memPart a = Res.memPart b) :
    (∃ e, a = .error e ∧ b = .error e) ∨
      ∃ τ₁ τ₂, a = .ok τ₁ ∧ b = .ok τ₂ ∧ τ₁.HeapEq τ₂ := by
  cases a with
  | error e =>
    cases b with
    | error e' =>
      simp only [Res.memPart, Except.map, Except.error.injEq] at h
      exact Or.inl ⟨e, rfl, by rw [h]⟩
    | ok _ => simp [Res.memPart, Except.map] at h
  | ok τ₁ =>
    cases b with
    | error _ => simp [Res.memPart, Except.map] at h
    | ok τ₂ =>
      simp only [Res.memPart, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
      exact Or.inr ⟨τ₁, τ₂, rfl, rfl, h⟩

end

section
open Semantics SemanticsProperties
variable {C : Contract}
section StorageOnly
variable {σ τ : Semantics.State} (hst : σ.storage = τ.storage)
include hst

theorem Semantics.State.findStorage_of_storage (r : Name) (q : List Seg) :
    σ.findStorage r q = τ.findStorage r q := by
  unfold Semantics.State.findStorage; rw [hst]

theorem Semantics.State.checkIndex_of_storage (r : Name) (q : List Seg) (i : Int) :
    σ.checkIndex r q i = τ.checkIndex r q i := by
  unfold Semantics.State.checkIndex; rw [Semantics.State.findStorage_of_storage hst]

theorem arrayLen_of_storage (r : Name) (q : List Seg) : arrayLen σ r q = arrayLen τ r q := by
  unfold arrayLen; rw [Semantics.State.findStorage_of_storage hst]

theorem Semantics.State.saveStorage_of_storage (r : Name) (q : List Seg) (v : Semantics.SVal) :
    Res.stPart (σ.saveStorage r q v) = Res.stPart (τ.saveStorage r q v) := by
  unfold Semantics.State.saveStorage
  rw [hst]
  cases lookupBy r τ.storage with
  | none => rfl
  | some w =>
    simp only [bind, Except.bind]
    cases w.save q v <;> rfl

theorem pushPlaceAt_of_storage (E : Ty) (r : Name) (q : List Seg) :
    Res.stPart (pushPlaceAt σ E r q >>= fun x => pure x.1) =
      Res.stPart (pushPlaceAt τ E r q >>= fun x => pure x.1) := by
  unfold pushPlaceAt
  rw [Semantics.State.findStorage_of_storage hst]
  cases τ.findStorage r q with
  | error _ => rfl
  | ok cur =>
    cases cur with
    | array elems shadow fx =>
      simp only [bind, Except.bind]
      have h := Semantics.State.saveStorage_of_storage hst r q
        (.array (elems ++ [(Semantics.pushSlot E shadow).1]) (Semantics.pushSlot E shadow).2 fx)
      rcases Res.stPart_cases h with ⟨e, h1, h2⟩ | ⟨τ₁, τ₂, h1, h2, h3⟩
      · simp only [h1, h2]
      · simp only [h1, h2, pure, Except.pure, Res.stPart, Except.map, h3]
    | prim _ | struct _ | map _ _ => rfl

theorem popAt_of_storage (keep : Bool) (r : Name) (q : List Seg) :
    Res.stPart (popAt σ keep r q) = Res.stPart (popAt τ keep r q) := by
  unfold popAt
  rw [Semantics.State.findStorage_of_storage hst]
  cases τ.findStorage r q with
  | error _ => rfl
  | ok cur =>
    cases cur with
    | array elems shadow fx =>
      simp only [bind, Except.bind]
      cases elems.reverse with
      | nil => rfl
      | cons last rest => exact Semantics.State.saveStorage_of_storage hst r q _
    | prim _ | struct _ | map _ _ => rfl

end StorageOnly
end

section
open Semantics SemanticsProperties
variable {C : Contract}
section HeapOnly
variable {σ τ : Semantics.State}

theorem Semantics.State.getObj_of_heap (hh : σ.heap = τ.heap) (id : Nat) : σ.getObj id = τ.getObj id := by
  unfold Semantics.State.getObj; rw [hh]

theorem readAddr_of_heap (hh : σ.heap = τ.heap) (a : Addr) : readAddr σ a = readAddr τ a := by
  cases a <;> simp only [readAddr, Semantics.State.getObj_of_heap hh]

theorem memArrayLen_of_heap (hh : σ.heap = τ.heap) (id : Nat) :
    memArrayLen σ id = memArrayLen τ id := by
  unfold memArrayLen; rw [Semantics.State.getObj_of_heap hh]

theorem writeAddr_of_heap (h : σ.HeapEq τ) (mv : Semantics.MVal) (a : Addr) :
    Res.memPart (writeAddr σ mv a) = Res.memPart (writeAddr τ mv a) := by
  cases a with
  | memoryField id f =>
    simp only [writeAddr, memWriteField, bind, Except.bind, Semantics.State.getObj_of_heap h.1]
    cases τ.getObj id with
    | error _ => rfl
    | ok obj =>
      cases obj with
      | struct fields => simp only [Res.memPart, Except.map, Semantics.State.setObj, h.1, h.2]
      | array _ _ => rfl
  | memoryIndex id i =>
    simp only [writeAddr, memWriteIndex, bind, Except.bind, Semantics.State.getObj_of_heap h.1]
    cases τ.getObj id with
    | error _ => rfl
    | ok obj =>
      cases obj with
      | struct _ => rfl
      | array elems fx =>
        by_cases hc : 0 ≤ i ∧ i.toNat < elems.length <;>
          simp [hc, Res.memPart, Except.map, Semantics.State.setObj, h.1, h.2]

/-- Two copies that halt alike, or return one value into states of one heap. -/
def ResHeap {α : Type} : Res (Semantics.State × α) → Res (Semantics.State × α) → Prop
  | .error e₁, .error e₂ => e₁ = e₂
  | .ok (s₁, a₁), .ok (s₂, a₂) => a₁ = a₂ ∧ s₁.HeapEq s₂
  | _, _ => False

theorem ResHeap.bind {α β : Type} {x₁ x₂ : Res (Semantics.State × α)} (hx : ResHeap x₁ x₂)
    {f₁ f₂ : Semantics.State × α → Res (Semantics.State × β)}
    (hf : ∀ s₁ s₂ a, s₁.HeapEq s₂ → ResHeap (f₁ (s₁, a)) (f₂ (s₂, a))) :
    ResHeap (x₁ >>= f₁) (x₂ >>= f₂) := by
  match x₁, x₂, hx with
  | .error _, .error _, hx => subst hx; exact rfl
  | .ok (s₁, a), .ok (s₂, a'), ⟨ha, hs⟩ => subst ha; exact hf s₁ s₂ a hs

theorem ResHeap.cases {α : Type} {x₁ x₂ : Res (Semantics.State × α)} (hx : ResHeap x₁ x₂) :
    (∃ e, x₁ = .error e ∧ x₂ = .error e) ∨
      ∃ s₁ s₂ a, x₁ = .ok (s₁, a) ∧ x₂ = .ok (s₂, a) ∧ s₁.HeapEq s₂ := by
  match x₁, x₂, hx with
  | .error e, .error _, hx => exact Or.inl ⟨e, rfl, by rw [hx]⟩
  | .ok (s₁, a), .ok (s₂, _), ⟨rfl, hs⟩ => exact Or.inr ⟨s₁, s₂, a, rfl, rfl, hs⟩

mutual
theorem copyStToM_heap {σ τ : Semantics.State} (h : σ.HeapEq τ) (v : Semantics.SVal) : ResHeap (copyStToM σ v) (copyStToM τ v) := by
  match v with
  | .int v => rw [copyStToM, copyStToM]; exact ⟨rfl, h⟩
  | .bool b => rw [copyStToM, copyStToM]; exact ⟨rfl, h⟩
  | .struct fields =>
    rw [copyStToM, copyStToM]
    refine ResHeap.bind (copyStFields_heap h fields) ?_
    intro t₁ t₂ mfields ht
    exact ⟨by simp [ht.2], by simp [Semantics.State.HeapEq, ht.1, ht.2]⟩
  | .array elems _ _ =>
    rw [copyStToM, copyStToM]
    refine ResHeap.bind (copyStElems_heap h elems) ?_
    intro t₁ t₂ melems ht
    exact ⟨by simp [ht.2], by simp [Semantics.State.HeapEq, ht.1, ht.2]⟩
  | .map _ _ => rw [copyStToM, copyStToM]; exact rfl

theorem copyStFields_heap {σ τ : Semantics.State} (h : σ.HeapEq τ) (fields : List (Name × Semantics.SVal)) :
    ResHeap (copyStFields σ fields) (copyStFields τ fields) := by
  match fields with
  | [] => rw [copyStFields, copyStFields]; exact ⟨rfl, h⟩
  | (name, v) :: rest =>
    rw [copyStFields, copyStFields]
    refine ResHeap.bind (copyStToM_heap h v) ?_
    intro t₁ t₂ mv ht
    refine ResHeap.bind (copyStFields_heap ht rest) ?_
    intro u₁ u₂ mrest hu
    exact ⟨rfl, hu⟩

theorem copyStElems_heap {σ τ : Semantics.State} (h : σ.HeapEq τ) (elems : List Semantics.SVal) :
    ResHeap (copyStElems σ elems) (copyStElems τ elems) := by
  match elems with
  | [] => rw [copyStElems, copyStElems]; exact ⟨rfl, h⟩
  | v :: rest =>
    rw [copyStElems, copyStElems]
    refine ResHeap.bind (copyStToM_heap h v) ?_
    intro t₁ t₂ mv ht
    refine ResHeap.bind (copyStElems_heap ht rest) ?_
    intro u₁ u₂ mrest hu
    exact ⟨rfl, hu⟩
end

theorem allocDefault_heap (h : σ.HeapEq τ) (R : RefTy) :
    ResHeap (allocDefault σ R) (allocDefault τ R) := by
  unfold allocDefault
  rcases (copyStToM_heap h (defaultForRef R)).cases with ⟨e, h₁, h₂⟩ | ⟨t₁, t₂, mv, h₁, h₂, ht⟩
  · rw [h₁, h₂]; exact rfl
  · rw [h₁, h₂]
    cases mv with
    | prim p => cases p <;> exact rfl
    | ref id => exact ⟨rfl, ht⟩

mutual
theorem copyMToSt_of_heap {σ τ : Semantics.State} (hh : σ.heap = τ.heap) (rem : List Nat) (v : Semantics.MVal) :
    copyMToSt σ rem v = copyMToSt τ rem v := by
  match v with
  | .int v => rw [copyMToSt.eq_def, copyMToSt.eq_def]
  | .bool b => rw [copyMToSt.eq_def, copyMToSt.eq_def]
  | .ref id =>
    rw [copyMToSt.eq_def, copyMToSt.eq_def]
    by_cases hmem : id ∈ rem
    · simp only [hmem, dif_pos, Semantics.State.getObj_of_heap hh, copyMFields_of_heap hh (rem.erase id),
        copyMElems_of_heap hh (rem.erase id)]
    · simp only [hmem, dif_neg, not_false_iff]
termination_by (rem.length, 0)
decreasing_by all_goals
  (apply Prod.Lex.left
   have h1 := List.length_erase_of_mem hmem
   have h2 := List.length_pos_of_mem hmem
   omega)

theorem copyMFields_of_heap {σ τ : Semantics.State} (hh : σ.heap = τ.heap) (rem : List Nat) (fields : List (Name × Semantics.MVal)) :
    copyMFields σ rem fields = copyMFields τ rem fields := by
  match fields with
  | [] => rw [copyMFields, copyMFields]
  | (name, v) :: rest =>
    rw [copyMFields, copyMFields, copyMToSt_of_heap hh rem v, copyMFields_of_heap hh rem rest]
termination_by (rem.length, fields.length + 1)

theorem copyMElems_of_heap {σ τ : Semantics.State} (hh : σ.heap = τ.heap) (rem : List Nat) (elems : List Semantics.MVal) :
    copyMElems σ rem elems = copyMElems τ rem elems := by
  match elems with
  | [] => rw [copyMElems, copyMElems]
  | v :: rest =>
    rw [copyMElems, copyMElems, copyMToSt_of_heap hh rem v, copyMElems_of_heap hh rem rest]
termination_by (rem.length, elems.length + 1)
end

theorem copyMem_of_heap (hh : σ.heap = τ.heap) (v : Semantics.MVal) :
    Semantics.copyMem σ v = Semantics.copyMem τ v := by
  unfold Semantics.copyMem
  rw [hh, copyMToSt_of_heap hh]

end HeapOnly
end


/-! ## From `Solidity.Calculus.ChainRewrites` -/

section
open Semantics SemanticsProperties
variable {C : Contract}

/-- A member path is a field segment or more. -/
def Seg.isField : Seg → Bool
  | .field _ => true
  | .at _ => false

/-- The Theory's `diverges` gives the interpreter's `Diverge`. -/
theorem Diverge_of_diverges : (a b : List Seg) → Theory.StValue.diverges a b = true → Close.Diverge a b
  | [], _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | x :: p, y :: q, h => by
    simp only [Theory.StValue.diverges] at h
    split at h
    · exact Or.inr (Diverge_of_diverges p q h)
    · exact Or.inl ‹_›

/-- A reset struct keeps its members, each reset: a word read below the node
reads a word after the reset. -/
theorem Semantics.SVal.find_defaultOf_prim : (tail : List Seg) → tail.all Seg.isField = true → (v : Semantics.SVal) →
    ∀ {x : PrimVal}, v.find tail = .ok (.prim x) → ∃ y, v.defaultOf.find tail = .ok (.prim y)
  | [], _, v, x, h => by
    rw [SemanticsProperties.SVal.find_nil] at h
    cases h
    cases x <;> exact ⟨_, rfl⟩
  | .field n :: rest, hf, v, x, h => by
    simp only [List.all_cons, Seg.isField, Bool.true_and] at hf
    cases v with
    | prim _ => nomatch h
    | map _ _ => nomatch h
    | struct fields =>
      simp only [Semantics.SVal.find] at h
      split at h
      · rename_i u hu
        obtain ⟨y, hy⟩ := Semantics.SVal.find_defaultOf_prim rest hf u h
        refine ⟨y, ?_⟩
        simp only [Semantics.SVal.defaultOf, Semantics.SVal.find, lookupBy_defaultOfFields, hu, Option.map_some]
        exact hy
      · nomatch h
    | array elems sh fx =>
      by_cases hn : n = "length"
      · subst hn
        cases fx with
        | true => nomatch h
        | false =>
          cases rest with
          | nil =>
            exact ⟨.int 0, rfl⟩
          | cons _ _ => nomatch h
      · exact absurd h (by cases rest <;> simp [Semantics.SVal.find])
  | .at _ :: _, hf, _, _, _ => by
    simp only [List.all_cons, Seg.isField, Bool.false_and, Bool.false_eq_true] at hf

/-- A write that returned saved, with the value it wrote laid over the old one
where it is not a word. -/
theorem Semantics.State.writeStorage_ok {σ τ : Semantics.State} {r : Name} {segs : List Seg} {v : Semantics.SVal}
    (h : σ.writeStorage r segs v = .ok τ) : ∃ x, σ.saveStorage r segs x = .ok τ := by
  cases v with
  | prim _ => exact ⟨_, h⟩
  | struct _ =>
    simp only [Semantics.State.writeStorage] at h
    obtain ⟨cur, -, h⟩ := bind_ok_inv h
    exact ⟨_, h⟩
  | array _ _ _ =>
    simp only [Semantics.State.writeStorage] at h
    obtain ⟨cur, -, h⟩ := bind_ok_inv h
    exact ⟨_, h⟩
  | map _ _ =>
    simp only [Semantics.State.writeStorage] at h
    obtain ⟨cur, -, h⟩ := bind_ok_inv h
    exact ⟨_, h⟩

/-- `select(s, r)`'s run on the state `s` leaves: that state with the struct
at the root `r` for its storage (`Op1.eval`). -/
def Semantics.State.selectRoot (r : Name) (τ : Semantics.State) : Res Semantics.State := do
  match ← τ.findStorage r [] with
  | .struct fields => pure { τ with storage := fields }
  | .prim _ | .array .. | .map .. => .error .undef

/-- The frame `F`: the state with the struct at `r₁.r₂…` for its storage. -/
def Semantics.State.frameOf : List Name → Semantics.State → Res Semantics.State
  | [], τ => .ok τ
  | r :: F, τ => Semantics.State.selectRoot r τ >>= Semantics.State.frameOf F

/-- In the frame at `r`, a read at `g.segs` is the read at `r.g.segs` outside it. -/
theorem Semantics.State.findStorage_selectRoot {r : Name} {τ τ' : Semantics.State} (h : Semantics.State.selectRoot r τ = .ok τ')
    (g : Name) (segs : List Seg) : τ'.findStorage g segs = τ.findStorage r (.field g :: segs) := by
  unfold Semantics.State.selectRoot at h
  simp only [Semantics.State.findStorage] at h
  cases hv : lookupBy r τ.storage with
  | none =>
    rw [hv] at h
    simp [bind, Except.bind] at h
  | some V =>
    rw [hv] at h
    cases V with
    | struct fields =>
      simp only [Semantics.SVal.find, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [Semantics.State.findStorage, hv, Semantics.SVal.find]
    | prim _ | array _ _ _ | map _ _ => simp [Semantics.SVal.find, bind, Except.bind] at h

/-- In the frame at `r`, a write at `g.rest` is the write at `r.g.rest` outside
it, the frame taken after: the two runs end alike. -/
theorem Semantics.State.saveStorage_selectRoot (r : Name) (τ : Semantics.State) (g : Name) (rest : List Seg) (new : Semantics.SVal) :
    (τ.saveStorage r (.field g :: rest) new >>= Semantics.State.selectRoot r) =
      (Semantics.State.selectRoot r τ >>= fun τ' => τ'.saveStorage g rest new) := by
  unfold Semantics.State.selectRoot Semantics.State.saveStorage
  simp only [Semantics.State.findStorage]
  cases hv : lookupBy r τ.storage with
  | none => simp [bind, Except.bind]
  | some V =>
    cases V with
    | prim _ | array _ _ _ | map _ _ => simp [Semantics.SVal.save, Semantics.SVal.find, bind, Except.bind]
    | struct fields =>
      cases hg : lookupBy g fields with
      | none => simp [Semantics.SVal.save, Semantics.SVal.find, hg, bind, Except.bind, pure, Except.pure]
      | some old =>
        cases hs : old.save rest new with
        | error e => simp [Semantics.SVal.save, Semantics.SVal.find, hg, hs, bind, Except.bind, pure, Except.pure]
        | ok upd =>
          simp [Semantics.SVal.save, Semantics.SVal.find, hg, hs, bind, Except.bind, pure, Except.pure, lookupBy_setBy_self]

/-- Where a run returns, the other returns the same: the two agree but for
how they halt. -/
def Semantics.Res.OkEq {α : Type} (a b : Res α) : Prop := ∀ x, a = .ok x ↔ b = .ok x

theorem Semantics.Res.OkEq.refl {α : Type} (a : Res α) : Res.OkEq a a := fun _ => Iff.rfl

theorem Semantics.Res.OkEq.symm {α : Type} {a b : Res α} (h : Res.OkEq a b) : Res.OkEq b a :=
  fun x => (h x).symm

theorem Semantics.Res.OkEq.trans {α : Type} {a b c : Res α} (h : Res.OkEq a b) (h' : Res.OkEq b c) :
    Res.OkEq a c := fun x => (h x).trans (h' x)

theorem Semantics.Res.OkEq.of_eq {α : Type} {a b : Res α} (h : a = b) : Res.OkEq a b := h ▸ Res.OkEq.refl a

theorem Semantics.Res.OkEq.le {α : Type} {a b : Res α} (h : Res.OkEq a b) : Res.Le a b := fun x => (h x).1

theorem Semantics.Res.OkEq.ge {α : Type} {a b : Res α} (h : Res.OkEq a b) : Res.Le b a := fun x => (h x).2

theorem Semantics.Res.OkEq.bind {α β : Type} {a a' : Res α} {f f' : α → Res β} (ha : Res.OkEq a a')
    (hf : ∀ x, Res.OkEq (f x) (f' x)) : Res.OkEq (a >>= f) (a' >>= f') := fun y => by
  constructor
  · intro h
    obtain ⟨x, hx, hy⟩ := bind_ok_inv h
    rw [(ha x).1 hx]
    exact (hf x y).1 hy
  · intro h
    obtain ⟨x, hx, hy⟩ := bind_ok_inv h
    rw [(ha x).2 hx]
    exact (hf x y).2 hy

/-- In the frame at `r`, a write of a value at `g.rest` is the write at
`r.g.rest` outside it, the frame taken after. -/
theorem Semantics.State.writeStorage_selectRoot (r : Name) (τ : Semantics.State) (g : Name) (rest : List Seg) (new : Semantics.SVal) :
    Res.OkEq (τ.writeStorage r (.field g :: rest) new >>= Semantics.State.selectRoot r)
      (Semantics.State.selectRoot r τ >>= fun τ' => τ'.writeStorage g rest new) := by
  have key : ∀ x : Semantics.SVal, Res.OkEq
      ((τ.findStorage r (.field g :: rest) >>= fun cur =>
        τ.saveStorage r (.field g :: rest) (cur.overlay x)) >>= Semantics.State.selectRoot r)
      (Semantics.State.selectRoot r τ >>= fun τ' => τ'.findStorage g rest >>= fun cur =>
        τ'.saveStorage g rest (cur.overlay x)) := by
    intro x
    cases hs : Semantics.State.selectRoot r τ with
    | ok τ' =>
      simp only [bind, Except.bind]
      rw [Semantics.State.findStorage_selectRoot hs]
      cases τ.findStorage r (.field g :: rest) with
      | error e => exact Res.OkEq.refl _
      | ok cur =>
        have e := Semantics.State.saveStorage_selectRoot r τ g rest (cur.overlay x)
        rw [hs] at e
        simp only [bind, Except.bind] at e
        exact Res.OkEq.of_eq e
    | error e =>
      -- the root is no struct: the write outside halts too
      intro y
      constructor
      · intro h
        obtain ⟨τ₁, h₁, h₂⟩ := bind_ok_inv h
        obtain ⟨cur, -, h₁⟩ := bind_ok_inv h₁
        have e' := Semantics.State.saveStorage_selectRoot r τ g rest (cur.overlay x)
        rw [hs, h₁] at e'
        simp only [bind, Except.bind] at e'
        rw [e'] at h₂
        cases h₂
      · intro h
        simp [bind, Except.bind] at h
  cases new with
  | prim _ => exact Res.OkEq.of_eq (Semantics.State.saveStorage_selectRoot r τ g rest _)
  | struct fs => exact key (.struct fs)
  | array a b c => exact key (.array a b c)
  | map a b => exact key (.map a b)

/-- `delete` at `g.segs`: the slot read, then written to its default. -/
def _root_.Solidity.Semantics.State.delAtAt (τ : Semantics.State) (g : Name) (segs : List Seg) : Res Semantics.State :=
  τ.findStorage g segs >>= fun cur => τ.saveStorage g segs cur.defaultOf

/-- A write below an array keeps its length. -/
theorem Close.arrLen_save_cons {a : Seg} {rest : List Seg} {old new upd : Semantics.SVal}
    (h : old.save (a :: rest) new = .ok upd) : Close.arrLen upd = Close.arrLen old := by
  cases old with
  | prim _ => cases a <;> simp [Semantics.SVal.save] at h
  | struct fields =>
    cases a with
    | «at» _ => simp [Semantics.SVal.save] at h
    | field n =>
      simp only [Semantics.SVal.save] at h
      split at h
      · obtain ⟨u, _, h⟩ := bind_ok_inv h
        cases h
        rfl
      · simp at h
  | array elems shadow fx =>
    cases a with
    | field _ => simp [Semantics.SVal.save] at h
    | «at» i =>
      simp only [Semantics.SVal.save] at h
      split at h
      · obtain ⟨u, _, h⟩ := bind_ok_inv h
        cases h
        have hlen : (((elems ++ shadow).set i.toNat u).take elems.length).length =
            elems.length := by simp
        simp only [Close.arrLen, hlen]
      · simp at h
  | map entries dflt =>
    cases a with
    | field _ => simp [Semantics.SVal.save] at h
    | «at» i =>
      simp only [Semantics.SVal.save] at h
      split at h <;> (obtain ⟨u, _, h⟩ := bind_ok_inv h; cases h; rfl)

/-- Reading an array length above or apart from a write gives its old
length. -/
theorem Close.find_save_arrLen : ∀ {p q : List Seg} {old new upd : Semantics.SVal},
    old.save p new = .ok upd → ¬ Close.Prefix p q →
      (upd.find q >>= Close.arrLen) = (old.find q >>= Close.arrLen)
  | [], _, _, _, _, _, hq => (hq trivial).elim
  | _ :: _, [], _, _, _, hs, _ => by
      simp only [SemanticsProperties.SVal.find_nil, bind, Except.bind]
      exact Close.arrLen_save_cons hs
  | a :: p, b :: q, old, upd, new, hs, hq => by
      by_cases hab : a = b
      · subst hab
        have hq' : ¬ Close.Prefix p q := fun h => hq ⟨rfl, h⟩
        obtain ⟨c, u, hu, hf⟩ := Close.save_cons_find hs
        rw [(hf q).1, (hf q).2]
        exact Close.find_save_arrLen hu hq'
      · rw [Close.find_save_diverge (show Close.Diverge (a :: p) (b :: q) from Or.inl hab) hs]

/-- A divergent path is not a prefix of the path it diverges from. -/
theorem Close.Diverge.not_prefix : ∀ {p q : List Seg}, Close.Diverge p q → ¬ Close.Prefix p q
  | _ :: _, _ :: _, h => fun hp => by
      rcases h with h | h
      · exact h hp.1
      · exact h.not_prefix hp.2

/-- A prefix remains a prefix when the path on the right is extended. -/
theorem Close.Prefix.right_append : ∀ {p q : List Seg}, Close.Prefix p q → (tail : List Seg) →
    Close.Prefix p (q ++ tail)
  | [], _, _, _ => trivial
  | _ :: _, _ :: _, h, tail => ⟨h.1, h.2.right_append tail⟩

/-- In the frame at `r`, a delete at `g.rest` is the delete at `r.g.rest`
outside it, the frame taken after. -/
theorem Semantics.State.delAtAt_selectRoot (r : Name) (τ : Semantics.State) (g : Name) (rest : List Seg) :
    Res.OkEq (τ.delAtAt r (.field g :: rest) >>= Semantics.State.selectRoot r)
      (Semantics.State.selectRoot r τ >>= fun τ' => τ'.delAtAt g rest) := by
  unfold Semantics.State.delAtAt
  cases hs : Semantics.State.selectRoot r τ with
  | ok τ' =>
    simp only [bind, Except.bind]
    rw [Semantics.State.findStorage_selectRoot hs]
    cases τ.findStorage r (.field g :: rest) with
    | error e => exact Res.OkEq.refl _
    | ok cur =>
      have e := Semantics.State.saveStorage_selectRoot r τ g rest cur.defaultOf
      rw [hs] at e
      simp only [bind, Except.bind] at e
      exact Res.OkEq.of_eq e
  | error e =>
    intro x
    constructor
    · intro h
      obtain ⟨τ₁, h₁, h₂⟩ := bind_ok_inv h
      obtain ⟨cur, -, h₁⟩ := bind_ok_inv h₁
      have e' := Semantics.State.saveStorage_selectRoot r τ g rest cur.defaultOf
      rw [hs, h₁] at e'
      simp only [bind, Except.bind] at e'
      rw [e'] at h₂
      cases h₂
    · intro h
      simp [bind, Except.bind] at h

theorem Semantics.Res.bind_assoc {α β γ : Type} (x : Res α) (f : α → Res β) (g : β → Res γ) :
    ((x >>= f) >>= g) = (x >>= fun a => f a >>= g) := by cases x <;> rfl

/-- A read of a word through a node that is no struct halts, but at the
`length` of an array with nothing after it. -/
theorem Semantics.SVal.find_field_of_nonStruct {V : Semantics.SVal} (hV : ∀ fields, V ≠ .struct fields) {g : Name}
    {segs : List Seg} (hg : g = "length" → segs ≠ []) {x : Semantics.SVal} :
    V.find (.field g :: segs) ≠ .ok x := by
  cases V with
  | struct fields => exact absurd rfl (hV fields)
  | prim _ => simp [Semantics.SVal.find]
  | map _ _ => simp [Semantics.SVal.find]
  | array elems sh fx =>
    by_cases h : g = "length"
    · subst h
      cases fx with
      | true => simp [Semantics.SVal.find]
      | false =>
        cases segs with
        | nil => exact absurd rfl (hg rfl)
        | cons _ _ => simp [Semantics.SVal.find]
    · simp [Semantics.SVal.find]

theorem Semantics.Res.bind_pure_ok {α : Type} (x : Res α) : (x >>= fun a => (Except.ok a : Res α)) = x := by
  cases x <;> rfl

/-- A read in the frame `F` is the read outside it, at `F`'s members then the
path, where the path's root is not an array's `length`. -/
theorem Semantics.State.frameOf_findStorage (r₁ : Name) (g : Name) (segs : List Seg) (hg : g ≠ "length") :
    (F' : List Name) → (τ : Semantics.State) →
      Res.OkEq (Semantics.State.frameOf (r₁ :: F') τ >>= fun τ' => τ'.findStorage g segs)
        (τ.findStorage r₁ (F'.map Seg.field ++ (.field g :: segs)))
  | [], τ => by
    show Res.OkEq ((Semantics.State.selectRoot r₁ τ >>= fun x => (Except.ok x : Res Semantics.State)) >>= fun τ' =>
      τ'.findStorage g segs) _
    rw [Res.bind_pure_ok]
    simp only [List.map_nil, List.nil_append]
    cases hs : Semantics.State.selectRoot r₁ τ with
    | ok τ' =>
      rw [Res.ok_bind']
      exact Res.OkEq.of_eq (Semantics.State.findStorage_selectRoot hs g segs)
    | error e =>
      intro x
      constructor
      · intro h; simp [bind, Except.bind] at h
      · intro h
        exfalso
        unfold Semantics.State.selectRoot at hs
        simp only [Semantics.State.findStorage] at hs h
        cases hv : lookupBy r₁ τ.storage with
        | none => rw [hv] at h; cases h
        | some V =>
          rw [hv] at hs h
          cases V with
          | struct fields => simp [Semantics.SVal.find, bind, Except.bind, pure, Except.pure] at hs
          | prim _ | map _ _ | array _ _ _ =>
            exact Semantics.SVal.find_field_of_nonStruct (by intro _ h; cases h) (fun h' _ => hg h') h
  | r₂ :: F'', τ => by
    show Res.OkEq ((Semantics.State.selectRoot r₁ τ >>= Semantics.State.frameOf (r₂ :: F'')) >>= fun τ' =>
      τ'.findStorage g segs) _
    simp only [List.map_cons, List.cons_append]
    cases hs : Semantics.State.selectRoot r₁ τ with
    | ok τ' =>
      rw [Res.ok_bind']
      exact (Semantics.State.frameOf_findStorage r₂ g segs hg F'' τ').trans
        (Res.OkEq.of_eq (Semantics.State.findStorage_selectRoot hs _ _))
    | error e =>
      intro x
      constructor
      · intro h; simp [bind, Except.bind] at h
      · intro h
        exfalso
        unfold Semantics.State.selectRoot at hs
        simp only [Semantics.State.findStorage] at hs h
        cases hv : lookupBy r₁ τ.storage with
        | none => rw [hv] at h; cases h
        | some V =>
          rw [hv] at hs h
          cases V with
          | struct fields => simp [Semantics.SVal.find, bind, Except.bind, pure, Except.pure] at hs
          | prim _ | map _ _ | array _ _ _ =>
            exact Semantics.SVal.find_field_of_nonStruct (by intro _ h; cases h)
              (fun _ h' => by simp at h') h

/-- A write in the frame `F` is the write outside it, the frame taken after. -/
theorem Semantics.State.frameOf_writeStorage (r₁ : Name) (g : Name) (segs : List Seg) (sv : Semantics.SVal) :
    (F' : List Name) → (τ : Semantics.State) →
      Res.OkEq (τ.writeStorage r₁ (F'.map Seg.field ++ (.field g :: segs)) sv >>= Semantics.State.frameOf (r₁ :: F'))
        (Semantics.State.frameOf (r₁ :: F') τ >>= fun τ' => τ'.writeStorage g segs sv)
  | [], τ => by
    show Res.OkEq (τ.writeStorage r₁ ([].map Seg.field ++ (.field g :: segs)) sv >>= fun x =>
        Semantics.State.selectRoot r₁ x >>= fun x => (Except.ok x : Res Semantics.State))
      ((Semantics.State.selectRoot r₁ τ >>= fun x => (Except.ok x : Res Semantics.State)) >>= fun τ' =>
        τ'.writeStorage g segs sv)
    simp only [Res.bind_pure_ok, List.map_nil, List.nil_append]
    exact Semantics.State.writeStorage_selectRoot r₁ τ g segs sv
  | r₂ :: F'', τ => by
    show Res.OkEq (τ.writeStorage r₁ ((r₂ :: F'').map Seg.field ++ (.field g :: segs)) sv >>= fun x =>
        Semantics.State.selectRoot r₁ x >>= Semantics.State.frameOf (r₂ :: F''))
      ((Semantics.State.selectRoot r₁ τ >>= Semantics.State.frameOf (r₂ :: F'')) >>= fun τ' => τ'.writeStorage g segs sv)
    simp only [List.map_cons, List.cons_append]
    rw [← Res.bind_assoc, Res.bind_assoc (Semantics.State.selectRoot r₁ τ)]
    refine Res.OkEq.trans (Res.OkEq.bind (Semantics.State.writeStorage_selectRoot r₁ τ r₂ _ sv)
      fun _ => Res.OkEq.refl _) ?_
    rw [Res.bind_assoc]
    exact Res.OkEq.bind (Res.OkEq.refl _) fun τ' => Semantics.State.frameOf_writeStorage r₂ g segs sv F'' τ'

/-- A delete in the frame `F` is the delete outside it, the frame taken after. -/
theorem Semantics.State.frameOf_delAtAt (r₁ : Name) (g : Name) (segs : List Seg) :
    (F' : List Name) → (τ : Semantics.State) →
      Res.OkEq (τ.delAtAt r₁ (F'.map Seg.field ++ (.field g :: segs)) >>= Semantics.State.frameOf (r₁ :: F'))
        (Semantics.State.frameOf (r₁ :: F') τ >>= fun τ' => τ'.delAtAt g segs)
  | [], τ => by
    show Res.OkEq (τ.delAtAt r₁ ([].map Seg.field ++ (.field g :: segs)) >>= fun x =>
        Semantics.State.selectRoot r₁ x >>= fun x => (Except.ok x : Res Semantics.State))
      ((Semantics.State.selectRoot r₁ τ >>= fun x => (Except.ok x : Res Semantics.State)) >>= fun τ' => τ'.delAtAt g segs)
    simp only [Res.bind_pure_ok, List.map_nil, List.nil_append]
    exact Semantics.State.delAtAt_selectRoot r₁ τ g segs
  | r₂ :: F'', τ => by
    show Res.OkEq (τ.delAtAt r₁ ((r₂ :: F'').map Seg.field ++ (.field g :: segs)) >>= fun x =>
        Semantics.State.selectRoot r₁ x >>= Semantics.State.frameOf (r₂ :: F''))
      ((Semantics.State.selectRoot r₁ τ >>= Semantics.State.frameOf (r₂ :: F'')) >>= fun τ' => τ'.delAtAt g segs)
    simp only [List.map_cons, List.cons_append]
    rw [← Res.bind_assoc, Res.bind_assoc (Semantics.State.selectRoot r₁ τ)]
    refine Res.OkEq.trans (Res.OkEq.bind (Semantics.State.delAtAt_selectRoot r₁ τ r₂ _)
      fun _ => Res.OkEq.refl _) ?_
    rw [Res.bind_assoc]
    exact Res.OkEq.bind (Res.OkEq.refl _) fun τ' => Semantics.State.frameOf_delAtAt r₂ g segs F'' τ'

/-- A save at `r.g.rest` that returned went through the struct at `r`, before
and after: the save at `g.rest` in that frame. -/
theorem Semantics.State.saveStorage_field_ok {r g : Name} {rest : List Seg} {new : Semantics.SVal} {τ τ₁ : Semantics.State}
    (h : τ.saveStorage r (.field g :: rest) new = .ok τ₁) :
    ∃ τ' τ₁', Semantics.State.selectRoot r τ = .ok τ' ∧ Semantics.State.selectRoot r τ₁ = .ok τ₁' ∧
      τ'.saveStorage g rest new = .ok τ₁' := by
  have e := Semantics.State.saveStorage_selectRoot r τ g rest new
  rw [h, Res.ok_bind'] at e
  obtain ⟨V, up, hV, hs, rfl⟩ := SemanticsProperties.State.saveStorage_ok_inv h
  cases V with
  | prim _ | array _ _ _ | map _ _ => simp [Semantics.SVal.save] at hs
  | struct fields =>
    have hsel : Semantics.State.selectRoot r τ = .ok { τ with storage := fields } := by
      unfold Semantics.State.selectRoot
      simp [Semantics.State.findStorage, hV, Semantics.SVal.find, bind, Except.bind, pure, Except.pure]
    rw [hsel, Res.ok_bind'] at e
    simp only [Semantics.SVal.save] at hs
    cases hg : lookupBy g fields with
    | none => simp [hg] at hs
    | some old =>
      simp only [hg] at hs
      cases hs' : old.save rest new with
      | error _ => simp [hs', bind, Except.bind] at hs
      | ok u' =>
        simp only [hs', bind, Except.bind, Except.ok.injEq] at hs
        subst hs
        have inner : Semantics.State.saveStorage { τ with storage := fields } g rest new =
            .ok { τ with storage := setBy g u' fields } := by
          unfold Semantics.State.saveStorage
          simp [hg, hs', bind, Except.bind]
        exact ⟨_, _, hsel, by rw [e]; exact inner, inner⟩

/-- The frame `F` of a save at `F.g.segs` that returned exists, before and after it. -/
theorem Semantics.State.frameOf_of_saveStorage (r₁ g : Name) (segs : List Seg) (new : Semantics.SVal) :
    (F' : List Name) → (τ τ₁ : Semantics.State) →
      τ.saveStorage r₁ (F'.map Seg.field ++ (.field g :: segs)) new = .ok τ₁ →
      (∃ τ', Semantics.State.frameOf (r₁ :: F') τ = .ok τ') ∧ ∃ τ₁', Semantics.State.frameOf (r₁ :: F') τ₁ = .ok τ₁'
  | [], τ, τ₁, h => by
    obtain ⟨τ', τ₁', hs, hs₁, -⟩ := Semantics.State.saveStorage_field_ok h
    refine ⟨⟨τ', ?_⟩, ⟨τ₁', ?_⟩⟩
    · show (Semantics.State.selectRoot r₁ τ >>= Semantics.State.frameOf []) = _
      rw [hs]; rfl
    · show (Semantics.State.selectRoot r₁ τ₁ >>= Semantics.State.frameOf []) = _
      rw [hs₁]; rfl
  | r₂ :: F'', τ, τ₁, h => by
    obtain ⟨τ', τ₁', hs, hs₁, h'⟩ := Semantics.State.saveStorage_field_ok h
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := Semantics.State.frameOf_of_saveStorage r₂ g segs new F'' τ' τ₁' h'
    refine ⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩
    · show (Semantics.State.selectRoot r₁ τ >>= Semantics.State.frameOf (r₂ :: F'')) = _
      rw [hs, Res.ok_bind']; exact ha
    · show (Semantics.State.selectRoot r₁ τ₁ >>= Semantics.State.frameOf (r₂ :: F'')) = _
      rw [hs₁, Res.ok_bind']; exact hb

theorem Semantics.Value.toMVal_asValue (v : Value) : v.toMVal.asValue = .ok v := by cases v <;> rfl

theorem PrimVal.asValue_eq (p : PrimVal) : (Semantics.SVal.prim p).asValue = (MVal.prim p).asValue := by
  cases p <;> rfl

theorem Semantics.SVal.strip_asValue (v : Semantics.SVal) : v.strip.asValue = v.asValue := by cases v <;> rfl

theorem Semantics.SVal.overlay_asValue (old new : Semantics.SVal) : (old.overlay new).asValue = new.asValue := by
  cases old <;> cases new <;> first | rfl | exact Semantics.SVal.strip_asValue _

theorem Close.layAt_asValue (old : Semantics.SVal) (q : List Seg) (v : Semantics.SVal) :
    (Close.layAt old q v).asValue = v.asValue := by
  induction q generalizing old with
  | nil => simp only [Close.layAt]; exact Semantics.SVal.overlay_asValue old v
  | cons sg q ih =>
    cases sg with
    | «at» _ => cases old <;> simp only [Close.layAt] <;> exact Semantics.SVal.strip_asValue v
    | field f =>
      cases old with
      | struct ofs =>
        simp only [Close.layAt]
        cases lookupBy f ofs with
        | none => exact Semantics.SVal.strip_asValue v
        | some o => exact ih o
      | prim _ | array _ _ _ | map _ _ => simp only [Close.layAt]; exact Semantics.SVal.strip_asValue v

theorem Ty.memberTy_snoc_some {T T' : Ty} {p : List Seg} {s : Seg}
    (h : T.memberTy (p ++ [s]) = some T') : ∃ R', T.memberTy p = some (.ref R') := by
  rw [Ty.memberTy_append] at h
  cases hp : T.memberTy p with
  | none => simp [hp] at h
  | some T'' =>
    cases T'' with
    | prim q => simp [hp, Ty.memberTy, Ty.at_prim] at h
    | ref R' => exact ⟨R', rfl⟩

end

/-! ## From `Solidity.Calculus.TermTaclets` -/

section
open Semantics Theory Theory.StValue
variable {C : Contract}

/-- The shape of a path's segment: a member, or an element at a literal
index (`some k`) or at an index the syntax does not decide (`none`: a
local, a length, the slot past the end). -/
inductive SegT where
  | field (f : Name)
  | at (k : Option Int)
  deriving DecidableEq, Repr

/-- The segment has the shape. -/
def SegT.fits : SegT → Seg → Bool
  | .field f, .field g => f == g
  | .at (some k), .at i => k == i
  | .at none, .at _ => true
  | _, _ => false

/-- The path has the shape, segment by segment. -/
def SegT.matches : List SegT → List Seg → Bool
  | [], [] => true
  | x :: a, s :: p => x.fits s && SegT.matches a p
  | _, _ => false

/-- Whether two shapes tell their segments apart: `some true` when the
segments differ in every state (a member against an element, two members
or two literal indices by name or value), `some false` when they are one
segment in every state, `none` when a symbolic index decides nothing. -/
def SegT.apart : SegT → SegT → Option Bool
  | .field f, .field g => some (f != g)
  | .field _, .at _ => some true
  | .at _, .field _ => some true
  | .at (some i), .at (some j) => some (i != j)
  | .at none, .at _ => none
  | .at (some _), .at none => none

/-- The two shapes leave each other: at some position both have a segment
and the segments differ, the ones before being the same — the syntactic
form of the Theory's `diverges`.  A symbolic index decides nothing. -/
def SegT.diverges : List SegT → List SegT → Bool
  | x :: a, y :: b => match x.apart y with
    | some true => true
    | some false => SegT.diverges a b
    | none => false
  | _, _ => false

/-- Two paths that have the shapes `a ++ b` have the shape of their halves. -/
theorem SegT.matches_append : (a b : List SegT) → (p q : List Seg) → SegT.matches a p = true →
    SegT.matches b q = true → SegT.matches (a ++ b) (p ++ q) = true
  | [], _, [], _, _, hb => hb
  | x :: a, b, s :: p, q, ha, hb => by
    simp only [SegT.matches, Bool.and_eq_true] at ha
    simp only [List.cons_append, SegT.matches, ha.1, SegT.matches_append a b p q ha.2 hb,
      Bool.and_self]
  | [], _, _ :: _, _, ha, _ | _ :: _, _, [], _, ha, _ => nomatch ha

/-- `apart` decides the segments as it says. -/
theorem SegT.apart_sound : {x y : SegT} → {d : Bool} → {s t : Seg} → x.apart y = some d →
    x.fits s = true → y.fits t = true → (d = true → s ≠ t) ∧ (d = false → s = t)
  | .field _, .field _, _, .field _, .field _, h, hs, ht => by
    simp only [SegT.fits, beq_iff_eq] at hs ht
    simp only [SegT.apart, Option.some.injEq] at h
    subst hs ht h
    exact ⟨fun hne e => (bne_iff_ne.1 hne) (Seg.field.inj e),
      fun he => by rw [bne_eq_false_iff_eq.1 he]⟩
  | .at (some _), .at (some _), _, .at _, .at _, h, hs, ht => by
    simp only [SegT.fits, beq_iff_eq] at hs ht
    simp only [SegT.apart, Option.some.injEq] at h
    subst hs ht h
    exact ⟨fun hne e => (bne_iff_ne.1 hne) (Seg.at.inj e),
      fun he => by rw [bne_eq_false_iff_eq.1 he]⟩
  | .field _, .at _, _, .field _, .at _, h, _, _ | .at _, .field _, _, .at _, .field _, h, _, _ => by
    simp only [SegT.apart, Option.some.injEq] at h
    subst h
    exact ⟨fun _ e => Seg.noConfusion e, fun h => nomatch h⟩
  | .at none, .at _, _, _, _, h, _, _ | .at (some _), .at none, _, _, _, h, _, _ => by
    simp only [SegT.apart, reduceCtorEq] at h
  | .field _, _, _, .at _, _, _, hs, _ | .at _, _, _, .field _, _, _, hs, _ => by
    simp only [SegT.fits, Bool.false_eq_true] at hs
  | _, .field _, _, _, .at _, _, _, ht | _, .at _, _, _, .field _, _, _, ht => by
    simp only [SegT.fits, Bool.false_eq_true] at ht

/-- Shapes that diverge have paths that diverge. -/
theorem SegT.diverges_sound : (a b : List SegT) → (p q : List Seg) → SegT.diverges a b = true →
    SegT.matches a p = true → SegT.matches b q = true → Theory.StValue.diverges p q = true
  | x :: a, y :: b, s :: p, t :: q, hd, ha, hb => by
    simp only [SegT.matches, Bool.and_eq_true] at ha hb
    simp only [SegT.diverges] at hd
    simp only [Theory.StValue.diverges]
    cases hx : x.apart y with
    | none => rw [hx] at hd; cases hd
    | some d =>
      rw [hx] at hd
      have hst := SegT.apart_sound hx ha.1 hb.1
      cases d with
      | true => rw [if_neg (hst.1 rfl)]
      | false =>
        rw [if_pos (hst.2 rfl)]
        exact SegT.diverges_sound a b p q hd ha.2 hb.2
  | [], _, _, _, hd, _, _ | _ :: _, [], _, _, hd, _, _ => nomatch hd
  | _ :: _, _ :: _, [], _, _, ha, _ => nomatch ha
  | _ :: _, _ :: _, _ :: _, [], _, _, hb => nomatch hb

end



/-! ## The typed symbols are monotone in their arguments

Where an argument returns, a rewrite of it returns the same value
(`OLe`); a symbol of the typed signature then returns what it returned
(`Op1.eval_le` …), a lazy operand (`&&`, `||`, `c ? a : b`) too. -/

section TypedLe

/-- Where `a` returns a value, `b` returns it too. -/
def OLe {α : Type} (a b : Option α) : Prop := ∀ x, a = some x → b = some x

theorem OLe.refl {α : Type} (a : Option α) : OLe a a := fun _ h => h

theorem OLe.none {α : Type} (b : Option α) : OLe none b := fun _ h => Option.noConfusion h

theorem OLe.trans {α : Type} {a b c : Option α} (h₁ : OLe a b) (h₂ : OLe b c) : OLe a c :=
  fun x h => h₂ x (h₁ x h)

theorem OLe.cases {α : Type} {a b : Option α} (h : OLe a b) : a = Option.none ∨ a = b := by
  cases a with
  | none => exact .inl rfl
  | some x => exact .inr (h x rfl).symm

theorem OLe.bind {α β : Type} {a a' : Option α} {f f' : α → Option β} (ha : OLe a a')
    (hf : ∀ x, OLe (f x) (f' x)) : OLe (a.bind f) (a'.bind f') := fun y h => by
  obtain ⟨x, hx, hy⟩ := Option.bind_eq_some_iff.1 h
  rw [ha x hx, Option.bind_some]
  exact hf x y hy

theorem OLe.map {α β : Type} {a a' : Option α} (f : α → β) (ha : OLe a a') :
    OLe (a.map f) (a'.map f) := fun y h => by
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [ha x hx]
  rfl

variable {C : Contract} {g : State C []}

theorem binopT_le (op : BinOp) {p : PrimTy} (a : p.Denote) {y y' : Option p.Denote}
    (h : OLe y y') : OLe (binopT op a y) (binopT op a y') := by
  unfold binopT
  split
  · exact OLe.refl _
  · exact OLe.bind h fun _ => OLe.refl _

theorem cond_le {α : Type} (c : Bool) {y y' z z' : Option α} (hy : OLe y y') (hz : OLe z z') :
    OLe (cond c y z) (cond c y' z') := by
  cases c
  · exact hz
  · exact hy

theorem _root_.Solidity.Op1.eval_le {a s : Srt} (o : Op1 C a s) {x x' : Option (a.Den C g.H)}
    (h : OLe x x') : OLe (o.eval g x) (o.eval g x') := by
  rcases h.cases with rfl | rfl
  · rw [Op1.eval_eq_evalM]
    cases o <;> exact OLe.none _
  · exact OLe.refl _

theorem _root_.Solidity.Op2.eval_le {a b s : Srt} (o : Op2 C a b s)
    {x x' : Option (a.Den C g.H)} {y y' : Option (b.Den C g.H)} (hx : OLe x x') (hy : OLe y y') :
    OLe (o.eval g x y) (o.eval g x' y') := by
  rcases hx.cases with rfl | rfl
  · rw [Op2.eval_eq_evalM]
    cases o <;> exact OLe.none _
  · rcases hy.cases with rfl | rfl
    · rw [Op2.eval_eq_evalM]
      cases o with
      | binop op h => exact OLe.bind (OLe.refl _) fun a => binopT_le op a (OLe.none _)
      | _ => cases x <;> exact OLe.none _
    · exact OLe.refl _

theorem _root_.Solidity.Op3.eval_le {a b c s : Srt} (o : Op3 C a b c s)
    {x x' : Option (a.Den C g.H)} {y y' : Option (b.Den C g.H)} {z z' : Option (c.Den C g.H)}
    (hx : OLe x x') (hy : OLe y y') (hz : OLe z z') :
    OLe (o.eval g x y z) (o.eval g x' y' z') := by
  rcases hx.cases with rfl | rfl
  · rw [Op3.eval_eq_evalM]
    cases o <;> exact OLe.none _
  · rw [Op3.eval_eq_evalM]
    cases o with
    | ite => exact OLe.bind (OLe.refl _) fun c => cond_le c hy hz
    | _ =>
      rcases hy.cases with rfl | rfl
      · cases x <;> exact OLe.none _
      · rcases hz.cases with rfl | rfl
        · cases x <;> cases y <;>
            first
            | exact OLe.none _
            | (show OLe (Storage.push _ _ fun _ => none) _
               rw [Storage.push_none]; exact OLe.none _)
        · exact OLe.refl _

end TypedLe

end Solidity
