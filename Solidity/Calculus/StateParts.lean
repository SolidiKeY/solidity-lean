import Solidity.Calculus.UpdateRules

/-!
# Readings that agree where a write looks

A storage term reads to a state, of which a storage write takes the storage;
a memory term reads to a state, of which a memory write takes the heap and
the next identity (`UpdElem.write`).  Two readings *agree on the part* a
write looks at (`Srt.AgreePart`) when they halt alike or return states of
one storage (sort `st`), of one heap (sort `mem`), or one value (every other
sort).  Every symbol reads its arguments on that part only, and of the state
it runs in only the locals, the ledger, the funds and the transaction
(`State.Rest`) — but `next` and `at`, which read the storage of the state
they run in, and `storage` and `memory` themselves (`OpN.eval_part`).

That is what the merges of a chain need.  `{memory := M}{V}` is
`{memory := M ‖ V[M/memory]}`: `V`'s terms read after the write, in a state
of the same storage and locals and the heap `M` leaves, and `V[M/memory]`
reads before it (`Tm.withMem_eval`) — the storage terms of `V` read to states
of another heap, which a storage write does not look at.  `{storage := s}{V}`
is `{storage := s ‖ V[s/storage]}` where `V` reads the storage through
`storage` only (`Tm.stExplicitM`: no `next`, no `at`), its memory terms
allowed (`Tm.withStM_eval`): `Calculus/UpdateRules.lean`'s `withSt` keeps
out of memory reads, whose Theory denotation is their run, which a merge
does not need.
-/

namespace Solidity

open Semantics SemanticsProperties

variable {C : Contract}

/-! ## The part a write looks at -/

/-- The parts of a state no storage or memory term writes: the locals, the
ledger, the funds and the transaction. -/
structure Semantics.State.Rest (σ τ : State) : Prop where
  env : σ.env = τ.env
  net : σ.net = τ.net
  selfBalance : σ.selfBalance = τ.selfBalance
  tx : σ.tx = τ.tx

theorem Semantics.State.Rest.refl (σ : State) : σ.Rest σ := ⟨rfl, rfl, rfl, rfl⟩

/-- Two states of one storage, and of one heap and next identity. -/
def Semantics.State.HeapEq (σ τ : State) : Prop := σ.heap = τ.heap ∧ σ.nextId = τ.nextId

/-- What a storage write takes of a storage reading. -/
def Res.stPart (a : Res State) : Res (List (Name × SVal)) := a.map (·.storage)

/-- What a memory write takes of a memory reading. -/
def Res.memPart (a : Res State) : Res (List (Nat × MObj) × Nat) := a.map fun ρ => (ρ.heap, ρ.nextId)

/-- Two storage readings of one storage (a structure, so that a match on a
reading does not split it). -/
structure StPartEq (a b : Res State) : Prop where
  eq : Res.stPart a = Res.stPart b

/-- Two memory readings of one heap and next identity. -/
structure MemPartEq (a b : Res State) : Prop where
  eq : Res.memPart a = Res.memPart b

/-- Two readings agree where a write looks: a storage by its storage, a
memory by its heap and next identity, anything else as it is. -/
def Srt.AgreePart : (s : Srt) → s.Ev → s.Ev → Prop
  | .st => StPartEq
  | .mem => MemPartEq
  | .val | .path | .sv | .ident | .addr | .mv => Eq

theorem Res.stPart_cases {a b : Res State} (h : Res.stPart a = Res.stPart b) :
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

theorem Res.memPart_cases {a b : Res State} (h : Res.memPart a = Res.memPart b) :
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

theorem Res.stPart_ok {τ₁ τ₂ : State} (h : τ₁.storage = τ₂.storage) :
    StPartEq (Except.ok τ₁) (Except.ok τ₂) := ⟨by simp only [Res.stPart, Except.map, h]⟩

theorem Res.memPart_ok {τ₁ τ₂ : State} (h : τ₁.HeapEq τ₂) :
    MemPartEq (Except.ok τ₁) (Except.ok τ₂) := ⟨by simp only [Res.memPart, Except.map, h.1, h.2]⟩

theorem StPartEq.error (e : Halt) : StPartEq (Except.error e) (Except.error e) := ⟨rfl⟩
theorem MemPartEq.error (e : Halt) : MemPartEq (Except.error e) (Except.error e) := ⟨rfl⟩

/-! ## The storage operations read the storage only -/

section StorageOnly

variable {σ τ : State} (hst : σ.storage = τ.storage)
include hst

theorem State.findStorage_of_storage (r : Name) (q : List Seg) :
    σ.findStorage r q = τ.findStorage r q := by
  unfold State.findStorage; rw [hst]

theorem State.checkIndex_of_storage (r : Name) (q : List Seg) (i : Int) :
    σ.checkIndex r q i = τ.checkIndex r q i := by
  unfold State.checkIndex; rw [State.findStorage_of_storage hst]

theorem arrayLen_of_storage (r : Name) (q : List Seg) : arrayLen σ r q = arrayLen τ r q := by
  unfold arrayLen; rw [State.findStorage_of_storage hst]

theorem State.saveStorage_of_storage (r : Name) (q : List Seg) (v : SVal) :
    Res.stPart (σ.saveStorage r q v) = Res.stPart (τ.saveStorage r q v) := by
  unfold State.saveStorage
  rw [hst]
  cases lookupBy r τ.storage with
  | none => rfl
  | some w =>
    simp only [bind, Except.bind]
    cases w.save q v <;> rfl

theorem State.writeStorage_of_storage (r : Name) (q : List Seg) (v : SVal) :
    Res.stPart (σ.writeStorage r q v) = Res.stPart (τ.writeStorage r q v) := by
  unfold State.writeStorage
  cases v with
  | prim p => exact State.saveStorage_of_storage hst r q _
  | struct _ | array _ _ _ | map _ _ =>
    rw [State.findStorage_of_storage hst]
    simp only [bind, Except.bind]
    cases τ.findStorage r q with
    | error _ => rfl
    | ok cur => exact State.saveStorage_of_storage hst r q _

theorem pushAt_of_storage (E : Ty) (r : Name) (q : List Seg) (val : SVal → Res SVal) :
    Res.stPart (pushAt σ E r q val) = Res.stPart (pushAt τ E r q val) := by
  unfold pushAt
  rw [State.findStorage_of_storage hst]
  cases τ.findStorage r q with
  | error _ => rfl
  | ok cur =>
    cases cur with
    | array elems shadow fx =>
      simp only [bind, Except.bind]
      cases val (pushSlot E shadow).1 with
      | error _ => rfl
      | ok w => exact State.saveStorage_of_storage hst r q _
    | prim _ | struct _ | map _ _ => rfl

theorem pushPlaceAt_of_storage (E : Ty) (r : Name) (q : List Seg) :
    Res.stPart (pushPlaceAt σ E r q >>= fun x => pure x.1) =
      Res.stPart (pushPlaceAt τ E r q >>= fun x => pure x.1) := by
  unfold pushPlaceAt
  rw [State.findStorage_of_storage hst]
  cases τ.findStorage r q with
  | error _ => rfl
  | ok cur =>
    cases cur with
    | array elems shadow fx =>
      simp only [bind, Except.bind]
      have h := State.saveStorage_of_storage hst r q
        (.array (elems ++ [(pushSlot E shadow).1]) (pushSlot E shadow).2 fx)
      rcases Res.stPart_cases h with ⟨e, h1, h2⟩ | ⟨τ₁, τ₂, h1, h2, h3⟩
      · simp only [h1, h2]
      · simp only [h1, h2, pure, Except.pure, Res.stPart, Except.map, h3]
    | prim _ | struct _ | map _ _ => rfl

theorem popAt_of_storage (keep : Bool) (r : Name) (q : List Seg) :
    Res.stPart (popAt σ keep r q) = Res.stPart (popAt τ keep r q) := by
  unfold popAt
  rw [State.findStorage_of_storage hst]
  cases τ.findStorage r q with
  | error _ => rfl
  | ok cur =>
    cases cur with
    | array elems shadow fx =>
      simp only [bind, Except.bind]
      cases elems.reverse with
      | nil => rfl
      | cons last rest => exact State.saveStorage_of_storage hst r q _
    | prim _ | struct _ | map _ _ => rfl

end StorageOnly

/-! ## The memory operations read the heap only -/

section HeapOnly

variable {σ τ : State}

theorem State.getObj_of_heap (hh : σ.heap = τ.heap) (id : Nat) : σ.getObj id = τ.getObj id := by
  unfold State.getObj; rw [hh]

theorem readAddr_of_heap (hh : σ.heap = τ.heap) (a : Addr) : readAddr σ a = readAddr τ a := by
  cases a <;> simp only [readAddr, State.getObj_of_heap hh]

theorem memArrayLen_of_heap (hh : σ.heap = τ.heap) (id : Nat) :
    memArrayLen σ id = memArrayLen τ id := by
  unfold memArrayLen; rw [State.getObj_of_heap hh]

theorem writeAddr_of_heap (h : σ.HeapEq τ) (mv : MVal) (a : Addr) :
    Res.memPart (writeAddr σ mv a) = Res.memPart (writeAddr τ mv a) := by
  cases a with
  | memoryField id f =>
    simp only [writeAddr, memWriteField, bind, Except.bind, State.getObj_of_heap h.1]
    cases τ.getObj id with
    | error _ => rfl
    | ok obj =>
      cases obj with
      | struct fields => simp only [Res.memPart, Except.map, State.setObj, h.1, h.2]
      | array _ _ => rfl
  | memoryIndex id i =>
    simp only [writeAddr, memWriteIndex, bind, Except.bind, State.getObj_of_heap h.1]
    cases τ.getObj id with
    | error _ => rfl
    | ok obj =>
      cases obj with
      | struct _ => rfl
      | array elems fx =>
        by_cases hc : 0 ≤ i ∧ i.toNat < elems.length <;>
          simp [hc, Res.memPart, Except.map, State.setObj, h.1, h.2]

/-- Two copies that halt alike, or return one value into states of one heap. -/
def ResHeap {α : Type} : Res (State × α) → Res (State × α) → Prop
  | .error e₁, .error e₂ => e₁ = e₂
  | .ok (s₁, a₁), .ok (s₂, a₂) => a₁ = a₂ ∧ s₁.HeapEq s₂
  | _, _ => False

theorem ResHeap.bind {α β : Type} {x₁ x₂ : Res (State × α)} (hx : ResHeap x₁ x₂)
    {f₁ f₂ : State × α → Res (State × β)}
    (hf : ∀ s₁ s₂ a, s₁.HeapEq s₂ → ResHeap (f₁ (s₁, a)) (f₂ (s₂, a))) :
    ResHeap (x₁ >>= f₁) (x₂ >>= f₂) := by
  match x₁, x₂, hx with
  | .error _, .error _, hx => subst hx; exact rfl
  | .ok (s₁, a), .ok (s₂, a'), ⟨ha, hs⟩ => subst ha; exact hf s₁ s₂ a hs

theorem ResHeap.cases {α : Type} {x₁ x₂ : Res (State × α)} (hx : ResHeap x₁ x₂) :
    (∃ e, x₁ = .error e ∧ x₂ = .error e) ∨
      ∃ s₁ s₂ a, x₁ = .ok (s₁, a) ∧ x₂ = .ok (s₂, a) ∧ s₁.HeapEq s₂ := by
  match x₁, x₂, hx with
  | .error e, .error _, hx => exact Or.inl ⟨e, rfl, by rw [hx]⟩
  | .ok (s₁, a), .ok (s₂, _), ⟨rfl, hs⟩ => exact Or.inr ⟨s₁, s₂, a, rfl, rfl, hs⟩

theorem State.alloc_heapEq (h : σ.HeapEq τ) (obj : MObj) :
    (σ.alloc obj).2 = (τ.alloc obj).2 ∧ (σ.alloc obj).1.HeapEq (τ.alloc obj).1 := by
  simp only [State.alloc, State.HeapEq, h.1, h.2, and_self]

mutual
theorem copyStToM_heap {σ τ : State} (h : σ.HeapEq τ) (v : SVal) : ResHeap (copyStToM σ v) (copyStToM τ v) := by
  match v with
  | .int v => rw [copyStToM, copyStToM]; exact ⟨rfl, h⟩
  | .bool b => rw [copyStToM, copyStToM]; exact ⟨rfl, h⟩
  | .struct fields =>
    rw [copyStToM, copyStToM]
    refine ResHeap.bind (copyStFields_heap h fields) ?_
    intro t₁ t₂ mfields ht
    exact ⟨by simp [ht.2], by simp [State.HeapEq, ht.1, ht.2]⟩
  | .array elems _ _ =>
    rw [copyStToM, copyStToM]
    refine ResHeap.bind (copyStElems_heap h elems) ?_
    intro t₁ t₂ melems ht
    exact ⟨by simp [ht.2], by simp [State.HeapEq, ht.1, ht.2]⟩
  | .map _ _ => rw [copyStToM, copyStToM]; exact rfl

theorem copyStFields_heap {σ τ : State} (h : σ.HeapEq τ) (fields : List (Name × SVal)) :
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

theorem copyStElems_heap {σ τ : State} (h : σ.HeapEq τ) (elems : List SVal) :
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
theorem copyMToSt_of_heap {σ τ : State} (hh : σ.heap = τ.heap) (rem : List Nat) (v : MVal) :
    copyMToSt σ rem v = copyMToSt τ rem v := by
  match v with
  | .int v => rw [copyMToSt.eq_def, copyMToSt.eq_def]
  | .bool b => rw [copyMToSt.eq_def, copyMToSt.eq_def]
  | .ref id =>
    rw [copyMToSt.eq_def, copyMToSt.eq_def]
    by_cases hmem : id ∈ rem
    · simp only [hmem, dif_pos, State.getObj_of_heap hh, copyMFields_of_heap hh (rem.erase id),
        copyMElems_of_heap hh (rem.erase id)]
    · simp only [hmem, dif_neg, not_false_iff]
termination_by (rem.length, 0)
decreasing_by all_goals
  (apply Prod.Lex.left
   have h1 := List.length_erase_of_mem hmem
   have h2 := List.length_pos_of_mem hmem
   omega)

theorem copyMFields_of_heap {σ τ : State} (hh : σ.heap = τ.heap) (rem : List Nat) (fields : List (Name × MVal)) :
    copyMFields σ rem fields = copyMFields τ rem fields := by
  match fields with
  | [] => rw [copyMFields, copyMFields]
  | (name, v) :: rest =>
    rw [copyMFields, copyMFields, copyMToSt_of_heap hh rem v, copyMFields_of_heap hh rem rest]
termination_by (rem.length, fields.length + 1)

theorem copyMElems_of_heap {σ τ : State} (hh : σ.heap = τ.heap) (rem : List Nat) (elems : List MVal) :
    copyMElems σ rem elems = copyMElems τ rem elems := by
  match elems with
  | [] => rw [copyMElems, copyMElems]
  | v :: rest =>
    rw [copyMElems, copyMElems, copyMToSt_of_heap hh rem v, copyMElems_of_heap hh rem rest]
termination_by (rem.length, elems.length + 1)
end

theorem copyMem_of_heap (hh : σ.heap = τ.heap) (v : MVal) :
    Semantics.copyMem σ v = Semantics.copyMem τ v := by
  unfold Semantics.copyMem
  rw [hh, copyMToSt_of_heap hh]

end HeapOnly

/-! ## A symbol reads its arguments where a write looks -/

section OpPart

/-- The symbol reads the storage of the state it runs in: a push slot. -/
def Op1.stDirect : Op1 a s → Bool
  | .next => true
  | _ => false

/-- The symbol reads the storage of the state it runs in: an index check. -/
def Op2.stDirect : Op2 a b s → Bool
  | .at => true
  | _ => false

variable {σ τ : State}

theorem Op1.eval_part (hr : σ.Rest τ) :
    (o : Op1 a s) → (o.stDirect = false ∨ σ.storage = τ.storage) → {x₁ x₂ : a.Ev} →
      Srt.AgreePart a x₁ x₂ → Srt.AgreePart s (o.eval σ x₁) (o.eval τ x₂)
  | .unop .., _, _, _, hx | .field _, _, _, _, hx | .sval, _, _, _, hx | .newArr _, _, _, _, hx
  | .mfield _, _, _, _, hx | .mval, _, _, _, hx | .ref, _, _, _, hx => by
    simp only [Srt.AgreePart] at hx ⊢; subst hx; rfl
  | .net, _, _, _, hx => by
    simp only [Srt.AgreePart] at hx ⊢; subst hx
    simp only [Op1.eval, State.getNet, hr.net]
  | .netOf _, _, _, _, hx => by
    simp only [Srt.AgreePart] at hx ⊢; subst hx
    simp only [Op1.eval, State.getEnv, hr.env]
  | .next, ho, _, _, hx => by
    simp only [Srt.AgreePart] at hx ⊢; subst hx
    have hst := ho.resolve_left (by simp [Op1.stDirect])
    simp only [Op1.eval, State.findStorage_of_storage hst]
  | .select r, _, _, _, hx => by
    simp only [Srt.AgreePart, Op1.eval] at hx ⊢
    rcases Res.stPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · exact ⟨rfl⟩
    · simp only [bind, Except.bind, State.findStorage_of_storage h]
      cases τ₂.findStorage r [] with
      | error e => exact ⟨rfl⟩
      | ok w =>
        cases w with
        | struct fields => exact Res.stPart_ok rfl
        | prim _ | array _ _ _ | map _ _ => exact ⟨rfl⟩
  | .alloc R, _, _, _, hx => by
    simp only [Srt.AgreePart, Op1.eval] at hx ⊢
    rcases Res.memPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · rfl
    · simp only [bind, Except.bind]
      rcases (allocDefault_heap h R).cases with ⟨e, h₁, h₂⟩ | ⟨_, _, a, h₁, h₂, _⟩ <;>
        simp only [h₁, h₂] <;> rfl
  | .addM R, _, _, _, hx => by
    simp only [Srt.AgreePart, Op1.eval] at hx ⊢
    rcases Res.memPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · exact ⟨rfl⟩
    · simp only [bind, Except.bind]
      rcases (allocDefault_heap h R).cases with ⟨e, h₁, h₂⟩ | ⟨_, _, a, h₁, h₂, h₃⟩
      · simp only [h₁, h₂]; exact ⟨rfl⟩
      · simp only [h₁, h₂, pure, Except.pure]; exact Res.memPart_ok h₃

theorem Op2.eval_part :
    (o : Op2 a b s) → (o.stDirect = false ∨ σ.storage = τ.storage) → {x₁ x₂ : a.Ev} →
      {y₁ y₂ : b.Ev} → Srt.AgreePart a x₁ x₂ → Srt.AgreePart b y₁ y₂ →
      Srt.AgreePart s (o.eval σ x₁ y₁) (o.eval τ x₂ y₂)
  | .binop .., _, _, _, _, _, hx, hy | .mat, _, _, _, _, _, hx, hy => by
    simp only [Srt.AgreePart] at hx hy ⊢; subst hx hy; rfl
  | .at, ho, _, _, _, _, hx, hy => by
    simp only [Srt.AgreePart] at hx hy ⊢; subst hx hy
    have hst := ho.resolve_left (by simp [Op2.stDirect])
    simp only [Op2.eval, State.checkIndex_of_storage hst]
  | .find, _, _, _, _, _, hx, hy | .sfind, _, _, _, _, _, hx, hy => by
    simp only [Srt.AgreePart, Op2.eval] at hx hy ⊢; subst hy
    rcases Res.stPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · rfl
    · simp only [bind, Except.bind, State.findStorage_of_storage h]
  | .len, _, _, _, _, _, hx, hy => by
    simp only [Srt.AgreePart, Op2.eval] at hx hy ⊢; subst hy
    rcases Res.stPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · rfl
    · simp only [bind, Except.bind, arrayLen_of_storage h]
  | .read, _, _, _, _, _, hx, hy | .iread, _, _, _, _, _, hx, hy => by
    simp only [Srt.AgreePart, Op2.eval] at hx hy ⊢; subst hy
    rcases Res.memPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · rfl
    · simp only [bind, Except.bind, readAddr_of_heap h.1]
  | .mlen, _, _, _, _, _, hx, hy => by
    simp only [Srt.AgreePart, Op2.eval] at hx hy ⊢; subst hy
    rcases Res.memPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · rfl
    · simp only [bind, Except.bind, memArrayLen_of_heap h.1]
  | .copyMem, _, _, _, _, _, hx, hy => by
    simp only [Srt.AgreePart, Op2.eval] at hx hy ⊢; subst hy
    rcases Res.memPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · rfl
    · simp only [bind, Except.bind, copyMem_of_heap h.1]
  | .delAt, _, _, _, y, _, hx, hy => by
    simp only [Srt.AgreePart, Op2.eval] at hx hy ⊢; subst hy
    rcases Res.stPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · exact ⟨rfl⟩
    · simp only [bind, Except.bind, State.findStorage_of_storage h]
      cases y with
      | error e => exact ⟨rfl⟩
      | ok rs =>
        dsimp only
        cases τ₂.findStorage rs.1 rs.2 with
        | error e => exact ⟨rfl⟩
        | ok cur => exact ⟨State.saveStorage_of_storage h _ _ _⟩
  | .pushSlot E, _, _, _, y, _, hx, hy => by
    simp only [Srt.AgreePart, Op2.eval] at hx hy ⊢; subst hy
    rcases Res.stPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · exact ⟨rfl⟩
    · simp only [bind, Except.bind]
      cases y with
      | error e => exact ⟨rfl⟩
      | ok rs => dsimp only; exact ⟨pushAt_of_storage h E rs.1 rs.2 pure⟩
  | .pop, _, _, _, y, _, hx, hy | .shrink, _, _, _, y, _, hx, hy => by
    simp only [Srt.AgreePart, Op2.eval] at hx hy ⊢; subst hy
    rcases Res.stPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · exact ⟨rfl⟩
    · simp only [bind, Except.bind]
      cases y with
      | error e => exact ⟨rfl⟩
      | ok rs => dsimp only; exact ⟨popAt_of_storage h _ rs.1 rs.2⟩
  | .extend E, _, _, _, y, _, hx, hy => by
    simp only [Srt.AgreePart, Op2.eval] at hx hy ⊢; subst hy
    rcases Res.stPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · exact ⟨rfl⟩
    · simp only [bind, Except.bind]
      cases y with
      | error e => exact ⟨rfl⟩
      | ok rs => dsimp only; exact ⟨pushPlaceAt_of_storage h E rs.1 rs.2⟩
  | .copy, _, _, _, y, _, hx, hy => by
    simp only [Srt.AgreePart, Op2.eval] at hx hy ⊢; subst hy
    cases y with
    | error e => rfl
    | ok sv =>
      rcases Res.memPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
      · rfl
      · simp only [bind, Except.bind]
        rcases (copyStToM_heap h sv).cases with ⟨e, h₁, h₂⟩ | ⟨_, _, a, h₁, h₂, _⟩ <;>
          simp only [h₁, h₂] <;> rfl
  | .copySt, _, _, _, y, _, hx, hy => by
    simp only [Srt.AgreePart, Op2.eval] at hx hy ⊢; subst hy
    cases y with
    | error e => exact ⟨rfl⟩
    | ok sv =>
      rcases Res.memPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
      · exact ⟨rfl⟩
      · simp only [bind, Except.bind]
        rcases (copyStToM_heap h sv).cases with ⟨e, h₁, h₂⟩ | ⟨_, _, a, h₁, h₂, h₃⟩
        · simp only [h₁, h₂]; exact ⟨rfl⟩
        · simp only [h₁, h₂, pure, Except.pure]; exact Res.memPart_ok h₃

theorem Op3.eval_part :
    (o : Op3 a b c s) → {x₁ x₂ : a.Ev} → {y₁ y₂ : b.Ev} → {z₁ z₂ : c.Ev} →
      Srt.AgreePart a x₁ x₂ → Srt.AgreePart b y₁ y₂ → Srt.AgreePart c z₁ z₂ →
      Srt.AgreePart s (o.eval σ x₁ y₁ z₁) (o.eval τ x₂ y₂ z₂)
  | .ite, _, _, _, _, _, _, hx, hy, hz => by
    simp only [Srt.AgreePart] at hx hy hz ⊢; subst hx hy hz; rfl
  | .save, _, _, y, _, z, _, hx, hy, hz => by
    simp only [Srt.AgreePart, Op3.eval] at hx hy hz ⊢; subst hy hz
    cases z with
    | error e => exact ⟨rfl⟩
    | ok sv =>
      rcases Res.stPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
      · exact ⟨rfl⟩
      · simp only [bind, Except.bind]
        cases y with
        | error e => exact ⟨rfl⟩
        | ok rs => dsimp only; exact ⟨State.writeStorage_of_storage h rs.1 rs.2 sv⟩
  | .push, _, _, y, _, _, _, hx, hy, hz => by
    simp only [Srt.AgreePart, Op3.eval] at hx hy hz ⊢; subst hy hz
    rcases Res.stPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · exact ⟨rfl⟩
    · simp only [bind, Except.bind]
      cases y with
      | error e => exact ⟨rfl⟩
      | ok rs => dsimp only; exact ⟨pushAt_of_storage h _ rs.1 rs.2 _⟩
  | .write, _, _, y, _, z, _, hx, hy, hz => by
    simp only [Srt.AgreePart, Op3.eval] at hx hy hz ⊢; subst hy hz
    cases z with
    | error e => exact ⟨rfl⟩
    | ok mv =>
      rcases Res.memPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
      · exact ⟨rfl⟩
      · simp only [bind, Except.bind]
        cases y with
        | error e => exact ⟨rfl⟩
        | ok a => dsimp only; exact ⟨writeAddr_of_heap h mv a⟩

end OpPart

/-! ## `{memory := M}` substituted -/

/-- `{memory := M}e`: `M` for every `memory` in `e`. -/
def Tm.withMem (M : MTerm C) : Tm C u → Tm C u
  | .pvV x => .pvV x
  | .pvP x => .pvP x
  | .pvS x => .pvS x
  | .pvI x => .pvI x
  | .app0 .memory => M
  | .app0 o => .app0 o
  | .app1 o a => .app1 o (Tm.withMem M a)
  | .app2 o a b => .app2 o (Tm.withMem M a) (Tm.withMem M b)
  | .app3 o a b c => .app3 o (Tm.withMem M a) (Tm.withMem M b) (Tm.withMem M c)

/-- A memory term changes the heap and the next identity only. -/
theorem MTerm.eval_setsMem {σ μ : State} :
    (M : MTerm C) → M.eval σ = .ok μ → μ = { σ with heap := μ.heap, nextId := μ.nextId }
  | .app0 .memory, h => by cases h; rfl
  | .app1 (.addM R) m, h => by
    simp only [tm_eval] at h
    obtain ⟨τ, hm, h⟩ := bind_ok_inv h
    obtain ⟨⟨μ', _⟩, ha, h⟩ := bind_ok_inv h
    cases h
    have ih := MTerm.eval_setsMem m hm
    have fr : StateFrame τ μ' := by
      unfold allocDefault at ha
      split at ha
      · rename_i τ'' id' hc
        cases ha
        exact copyStToM_frame τ _ _ _ hc
      all_goals cases ha
    obtain ⟨h1, h2, h3, h4, h5⟩ := fr
    rw [ih] at h1 h2 h3 h4 h5
    cases μ'; cases σ
    simp only at h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5]
  | .app2 .copySt m v, h => by
    simp only [tm_eval] at h
    obtain ⟨sv, -, h⟩ := bind_ok_inv h
    obtain ⟨τ, hm, h⟩ := bind_ok_inv h
    obtain ⟨⟨μ', _⟩, hc, h⟩ := bind_ok_inv h
    cases h
    have ih := MTerm.eval_setsMem m hm
    obtain ⟨h1, h2, h3, h4, h5⟩ := copyStToM_frame τ sv _ _ hc
    rw [ih] at h1 h2 h3 h4 h5
    cases μ'; cases σ
    simp only at h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5]
  | .app3 .write m a v, h => by
    simp only [tm_eval] at h
    obtain ⟨mv, -, h⟩ := bind_ok_inv h
    obtain ⟨τ, hm, h⟩ := bind_ok_inv h
    obtain ⟨ad, -, h⟩ := bind_ok_inv h
    have ih := MTerm.eval_setsMem m hm
    obtain ⟨id, obj, rfl, -⟩ := Close.writeAddr_setObj h
    rw [ih]
    rfl

section WithMem

variable {M : MTerm C} {σ μ : State}

/-- **Read before `{memory := M}`, the substituted term reads as the term
after it**, on the part a write looks at: the state after has the storage
and the locals of the state before, and the heap `M` leaves. -/
theorem Tm.withMem_eval (hM : M.eval σ = .ok μ) (hμ : μ = { σ with heap := μ.heap, nextId := μ.nextId }) :
    (e : Tm C u) → Srt.AgreePart u ((Tm.withMem M e).eval σ) (e.eval μ)
  | .pvV _ | .pvP _ | .pvI _ => by
    rw [hμ]
    rfl
  | .pvS x => by
    show Srt.AgreePart .st _ _
    have hg : μ.getEnv x = σ.getEnv x := by rw [hμ]; rfl
    simp only [Srt.AgreePart, Tm.withMem, Tm.eval, hg, bind, Except.bind]
    cases σ.getEnv x with
    | error e => exact ⟨rfl⟩
    | ok b => cases b <;> first | exact ⟨rfl⟩ | exact Res.stPart_ok rfl
  | .app0 o => by
    cases o with
    | memory =>
      show Srt.AgreePart .mem _ _
      simp only [Srt.AgreePart, Tm.withMem, Tm.eval, Op0.eval, hM]
      exact ⟨rfl⟩
    | storage =>
      show Srt.AgreePart .st _ _
      simp only [Srt.AgreePart, Tm.withMem, Tm.eval, Op0.eval]
      exact Res.stPart_ok (by rw [hμ])
    | lit _ | root _ => rfl
    | env _ => show Srt.AgreePart .val _ _; rw [hμ]; rfl
  | .app1 o a => by
    have hr : σ.Rest μ := by rw [hμ]; exact ⟨rfl, rfl, rfl, rfl⟩
    exact Op1.eval_part hr o (Or.inr (by rw [hμ])) (a.withMem_eval hM hμ)
  | .app2 o a b => by
    have hr : σ.Rest μ := by rw [hμ]; exact ⟨rfl, rfl, rfl, rfl⟩
    exact Op2.eval_part o (Or.inr (by rw [hμ])) (a.withMem_eval hM hμ) (b.withMem_eval hM hμ)
  | .app3 o a b c =>
    Op3.eval_part o (a.withMem_eval hM hμ) (b.withMem_eval hM hμ) (c.withMem_eval hM hμ)

end WithMem

/-! ## `{storage := s}` substituted, memory reads included -/

/-- `{storage := s}e`: `s` for every `storage` in `e`, memory reads included
(`Tm.withSt` keeps out of them). -/
def Tm.withStM (s : STerm C) : Tm C u → Tm C u
  | .pvV x => .pvV x
  | .pvP x => .pvP x
  | .pvS x => .pvS x
  | .pvI x => .pvI x
  | .app0 .storage => s
  | .app0 o => .app0 o
  | .app1 o a => .app1 o (Tm.withStM s a)
  | .app2 o a b => .app2 o (Tm.withStM s a) (Tm.withStM s b)
  | .app3 o a b c => .app3 o (Tm.withStM s a) (Tm.withStM s b) (Tm.withStM s c)

/-- Every storage read of the term is through a storage term: no push slot
(`next`), no index check (`at`), which read the storage of the state they
run in.  Memory terms, which `Tm.stExplicit` keeps out, are allowed. -/
def Tm.stExplicitM : Tm C u → Bool
  | .pvV _ | .pvP _ | .pvS _ | .pvI _ | .app0 _ => true
  | .app1 o a => !o.stDirect && a.stExplicitM
  | .app2 o a b => !o.stDirect && a.stExplicitM && b.stExplicitM
  | .app3 _ a b c => a.stExplicitM && b.stExplicitM && c.stExplicitM

section WithStM

variable {s : STerm C} {σ τ : State}

theorem Semantics.State.Keeps.rest (hk : σ.Keeps τ) : σ.Rest τ := by
  rw [← hk]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem Semantics.State.Keeps.heapEq (hk : σ.Keeps τ) : σ.HeapEq τ := by
  rw [← hk]; exact ⟨rfl, rfl⟩

/-- **Read before `{storage := s}`, the substituted term reads as the term
after it**, on the part a write looks at, where every storage read is a
`storage` term: a memory term reads to a state of another storage, which a
memory write does not look at. -/
theorem Tm.withStM_eval (hs : s.eval σ = .ok τ) (hk : σ.Keeps τ) :
    (e : Tm C u) → e.stExplicitM = true → Srt.AgreePart u ((Tm.withStM s e).eval σ) (e.eval τ)
  | .pvV _, _ | .pvP _, _ | .pvI _, _ => by rw [← hk]; rfl
  | .pvS _, _ => by
    show Srt.AgreePart .st _ _
    simp only [Srt.AgreePart, Tm.withStM, Tm.eval, hk.getEnv, bind, Except.bind]
    cases σ.getEnv _ with
    | error e => exact ⟨rfl⟩
    | ok b => cases b <;> first | exact ⟨rfl⟩ | exact Res.stPart_ok rfl
  | .app0 o, _ => by
    cases o with
    | storage =>
      show Srt.AgreePart .st _ _
      simp only [Srt.AgreePart, Tm.withStM, Tm.eval, Op0.eval, hs]
      exact ⟨rfl⟩
    | memory =>
      show Srt.AgreePart .mem _ _
      simp only [Srt.AgreePart, Tm.withStM, Tm.eval, Op0.eval]
      exact Res.memPart_ok hk.heapEq
    | lit _ | root _ => rfl
    | env _ => show Srt.AgreePart .val _ _; rw [← hk]; rfl
  | .app1 o a, he => by
    simp only [Tm.stExplicitM, Bool.and_eq_true] at he
    exact Op1.eval_part hk.rest o (Or.inl (by simpa using he.1)) (a.withStM_eval hs hk he.2)
  | .app2 o a b, he => by
    simp only [Tm.stExplicitM, Bool.and_eq_true] at he
    exact Op2.eval_part o (Or.inl (by simpa using he.1.1)) (a.withStM_eval hs hk he.1.2)
      (b.withStM_eval hs hk he.2)
  | .app3 o a b c, he => by
    simp only [Tm.stExplicitM, Bool.and_eq_true] at he
    exact Op3.eval_part o (a.withStM_eval hs hk he.1.1) (b.withStM_eval hs hk he.1.2)
      (c.withStM_eval hs hk he.2)

end WithStM

/-! ## The elements of an update, substituted -/

/-- The element with `F` on its right-hand side. -/
def UpdElem.mapTm (F : {u : Srt} → Tm C u → Tm C u) : UpdElem C → UpdElem C
  | .val x t => .val x (F t)
  | .path x p => .path x (F p)
  | .mref x i => .mref x (F i)
  | .storage s => .storage (F s)
  | .store x s => .store x (F s)
  | .memory m => .memory (F m)
  | .selfBalance op a => .selfBalance op (F a)
  | .net r op a => .net (F r) op (F a)
  | .saveNet x => .saveNet x

/-- `P` of the element's right-hand side. -/
def UpdElem.allTm (P : {u : Srt} → Tm C u → Bool) : UpdElem C → Bool
  | .val _ t => P t
  | .path _ p => P p
  | .mref _ i => P i
  | .storage s => P s
  | .store _ s => P s
  | .memory m => P m
  | .selfBalance _ a => P a
  | .net r _ a => P r && P a
  | .saveNet _ => true

section MapTm

variable {σ τ : State} {F : {u : Srt} → Tm C u → Tm C u} {P : {u : Srt} → Tm C u → Bool}

/-- An element whose right-hand side reads substituted before as it reads
after, where a write looks, writes the same from either. -/
theorem UpdElem.mapTm_write (hr : σ.Rest τ)
    (hF : ∀ {u} (t : Tm C u), P t = true → Srt.AgreePart u ((F t).eval σ) (t.eval τ)) (ρ : State) :
    (e : UpdElem C) → e.allTm P = true → (e.mapTm F).write σ ρ = e.write τ ρ
  | .val _ t, he => by
    have h := hF t he
    simp only [Srt.AgreePart] at h
    simp only [UpdElem.mapTm, UpdElem.write, h]
  | .path _ p, he => by
    have h := hF p he
    simp only [Srt.AgreePart] at h
    simp only [UpdElem.mapTm, UpdElem.write, h]
  | .mref _ i, he => by
    have h := hF i he
    simp only [Srt.AgreePart] at h
    simp only [UpdElem.mapTm, UpdElem.write, h]
  | .storage s, he => by
    have h := hF s he
    simp only [Srt.AgreePart] at h
    simp only [UpdElem.mapTm, UpdElem.write]
    rcases Res.stPart_cases h.eq with ⟨e, h1, h2⟩ | ⟨τ₁, τ₂, h1, h2, h3⟩
    · simp only [h1, h2]
    · simp only [h1, h2, bind, Except.bind, h3]
  | .store _ s, he => by
    have h := hF s he
    simp only [Srt.AgreePart] at h
    simp only [UpdElem.mapTm, UpdElem.write]
    rcases Res.stPart_cases h.eq with ⟨e, h1, h2⟩ | ⟨τ₁, τ₂, h1, h2, h3⟩
    · simp only [h1, h2]
    · simp only [h1, h2, bind, Except.bind, h3]
  | .memory m, he => by
    have h := hF m he
    simp only [Srt.AgreePart] at h
    simp only [UpdElem.mapTm, UpdElem.write]
    rcases Res.memPart_cases h.eq with ⟨e, h1, h2⟩ | ⟨τ₁, τ₂, h1, h2, h3⟩
    · simp only [h1, h2]
    · simp only [h1, h2, bind, Except.bind, h3.1, h3.2]
  | .selfBalance _ a, he => by
    have h := hF a he
    simp only [Srt.AgreePart] at h
    simp only [UpdElem.mapTm, UpdElem.write, h, hr.selfBalance]
  | .net r _ a, he => by
    simp only [UpdElem.allTm, Bool.and_eq_true] at he
    have h1 := hF r he.1
    have h2 := hF a he.2
    simp only [Srt.AgreePart] at h1 h2
    simp only [UpdElem.mapTm, UpdElem.write, h1, h2, State.getNet, hr.net]
  | .saveNet _, _ => by simp only [UpdElem.mapTm, UpdElem.write, hr.net]

theorem Upd.mapTm_foldl (hr : σ.Rest τ)
    (hF : ∀ {u} (t : Tm C u), P t = true → Srt.AgreePart u ((F t).eval σ) (t.eval τ)) :
    (V : Upd C) → V.all (·.allTm P) = true → ∀ ρ,
      (V.map (·.mapTm F)).foldlM (fun ρ e => e.write σ ρ) ρ = V.foldlM (fun ρ e => e.write τ ρ) ρ
  | [], _, _ => rfl
  | e :: V, hV, ρ => by
    simp only [List.all_cons, Bool.and_eq_true] at hV
    simp only [List.map_cons, List.foldlM_cons, UpdElem.mapTm_write hr hF ρ e hV.1]
    congr 1
    funext ρ'
    exact Upd.mapTm_foldl hr hF V hV.2 ρ'

end MapTm

/-- `{memory := M}V`: `M` substituted for `memory` in `V`'s right-hand sides. -/
def Upd.withMem (M : MTerm C) (V : Upd C) : Upd C := V.map (·.mapTm (Tm.withMem M))

/-- `{storage := s}V`: `s` substituted for `storage` in `V`'s right-hand sides,
memory reads included. -/
def Upd.withStM (s : STerm C) (V : Upd C) : Upd C := V.map (·.mapTm (Tm.withStM s))

theorem UpdElem.memory_write (σ₀ τ : State) (M : MTerm C) : (UpdElem.memory M).write σ₀ τ =
    M.eval σ₀ >>= fun μ => .ok { τ with heap := μ.heap, nextId := μ.nextId } := rfl

/-- **`sequentialToParallel`** over a memory write:
`{memory := M}{V} ψ ⟺ {memory := M ‖ {memory := M}V} ψ`. -/
theorem Upd.mergeMemory_holds (m : Modality) (M : MTerm C) (V : Upd C) (ψ : Fml C) (σ : State) :
    holds σ (.upd m (.memory M :: V.withMem M) ψ) ↔ holds σ (.upd m [.memory M] (.upd m V ψ)) := by
  simp only [holds, Upd.apply, List.foldlM_cons, List.foldlM_nil, UpdElem.memory_write]
  cases hM : M.eval σ with
  | error _ => exact Iff.rfl
  | ok μ =>
    have hμ := MTerm.eval_setsMem M hM
    have hr : σ.Rest μ := by rw [hμ]; exact ⟨rfl, rfl, rfl, rfl⟩
    simp only [Res.ok_bind]
    rw [← hμ, Upd.withMem, Upd.mapTm_foldl (P := fun {_} _ => true) hr
      (fun t _ => Tm.withMem_eval hM hμ t) V (List.all_eq_true.2 fun e _ => by cases e <;> rfl) μ]
    exact Iff.rfl

/-- **`sequentialToParallel`** over a storage write, memory reads included:
`{storage := s}{V} ψ ⟺ {storage := s ‖ {storage := s}V} ψ`, where every
storage read of `V` is a `storage` term. -/
theorem Upd.mergeStorageM_holds (m : Modality) (s : STerm C) (V : Upd C)
    (hV : V.all (·.allTm Tm.stExplicitM) = true) (ψ : Fml C) (σ : State) :
    holds σ (.upd m (.storage s :: V.withStM s) ψ) ↔ holds σ (.upd m [.storage s] (.upd m V ψ)) := by
  simp only [holds, Upd.apply, List.foldlM_cons, List.foldlM_nil, UpdElem.storage_write]
  cases hs : s.eval σ with
  | error _ => exact Iff.rfl
  | ok τ =>
    have hk : σ.Keeps τ := STerm.eval_keeps s hs
    simp only [Res.ok_bind]
    rw [hk, Upd.withStM, Upd.mapTm_foldl hk.rest (fun t ht => Tm.withStM_eval hs hk t ht) V hV τ]
    exact Iff.rfl

end Solidity
