import Solidity.Calculus.UpdateRules

/-!
# Readings that agree where a write looks

A storage term reads to a state, of which a storage write takes the storage;
a memory term reads to a state, of which a memory write takes the heap and
the next identity (`UpdElem.write`).  Two readings *agree on the part* a
write looks at (`Srt.AgreePart`) when they halt alike or return states of
one storage (sort `st`), of one heap (sort `mem`), or one value (every other
sort).  Every symbol reads its arguments on that part only, and of the state
it runs in only the ledger, the funds and the transaction (`State.Rest`), a
ledger variable (`netOf`) — but `next` and `at`, which read the storage of
the state they run in, and `storage` and `memory` themselves
(`OpN.eval_part`).

That is what the merges of a chain need.  `{memory := M}{V}` is
`{memory := M ‖ V[M/memory]}`: `V`'s terms read after the write, in a state
of the same storage and locals and the heap `M` leaves, and `V[M/memory]`
reads before it (`Tm.withMem_eval`) — the storage terms of `V` read to states
of another heap, which a storage write does not look at.
`{L ‖ storage := s}{V}`, `L` locals, is `{L ‖ storage := s ‖ V[L, s/storage]}`
(`Tm.substSt`): the locals and `storage` substituted in one pass, memory
terms included, and a push slot `p[p.length]` or an index check `p[i]`,
which read the storage of the state they run in, carried over as
`p[p.length]@s` and `p[i]@s`, their check performed in `s`
(`Tm.substSt_eval`).  `Calculus/UpdateRules.lean`'s `withSt` keeps out of
memory reads, whose Theory denotation is their run, which a merge does not
need.
-/

namespace Solidity

open Semantics SemanticsProperties

variable {C : Contract}

/-! ## The part a write looks at -/

/-- The parts of a state neither a storage or memory term nor a local
writes: the ledger, the funds and the transaction. -/
structure Semantics.State.Rest (σ τ : State) : Prop where
  net : σ.net = τ.net
  selfBalance : σ.selfBalance = τ.selfBalance
  tx : σ.tx = τ.tx

theorem Semantics.State.Rest.refl (σ : State) : σ.Rest σ := ⟨rfl, rfl, rfl⟩

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

/-- A unary symbol reads its argument where a write looks, and of the state
the ledger (`net`) and a ledger variable it carries (`netOf`, bound alike
in the two states: `he`). -/
theorem Op1.eval_part (hr : σ.Rest τ) :
    (o : Op1 a s) → (∀ x, o.vars = [x] → σ.getEnv x = τ.getEnv x) →
      (o.stDirect = false ∨ σ.storage = τ.storage) → {x₁ x₂ : a.Ev} →
      Srt.AgreePart a x₁ x₂ → Srt.AgreePart s (o.eval σ x₁) (o.eval τ x₂)
  | .unop .., _, _, _, _, hx | .delValue, _, _, _, _, hx | .field _, _, _, _, _, hx
  | .sval, _, _, _, _, hx | .newArr _, _, _, _, _, hx | .mfield _, _, _, _, _, hx
  | .mval, _, _, _, _, hx | .ref, _, _, _, _, hx => by
    simp only [Srt.AgreePart] at hx ⊢; subst hx; rfl
  | .net, _, _, _, _, hx => by
    simp only [Srt.AgreePart] at hx ⊢; subst hx
    simp only [Op1.eval, State.getNet, hr.net]
  | .netOf x, he, _, _, _, hx => by
    simp only [Srt.AgreePart] at hx ⊢; subst hx
    simp only [Op1.eval, he x rfl]
  | .next, _, ho, _, _, hx => by
    simp only [Srt.AgreePart] at hx ⊢; subst hx
    have hst := ho.resolve_left (by simp [Op1.stDirect])
    simp only [Op1.eval, State.findStorage_of_storage hst]
  | .select r, _, _, _, _, hx => by
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
  | .alloc R, _, _, _, _, hx => by
    simp only [Srt.AgreePart, Op1.eval] at hx ⊢
    rcases Res.memPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · rfl
    · simp only [bind, Except.bind]
      rcases (allocDefault_heap h R).cases with ⟨e, h₁, h₂⟩ | ⟨_, _, a, h₁, h₂, _⟩ <;>
        simp only [h₁, h₂] <;> rfl
  | .addM R, _, _, _, _, hx => by
    simp only [Srt.AgreePart, Op1.eval] at hx ⊢
    rcases Res.memPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · exact ⟨rfl⟩
    · simp only [bind, Except.bind]
      rcases (allocDefault_heap h R).cases with ⟨e, h₁, h₂⟩ | ⟨_, _, a, h₁, h₂, h₃⟩
      · simp only [h₁, h₂]; exact ⟨rfl⟩
      · simp only [h₁, h₂, pure, Except.pure]; exact Res.memPart_ok h₃
  | .wt _, _, _, _, _, hx => by
    simp only [Srt.AgreePart, Op1.eval] at hx ⊢
    rcases Res.stPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · rfl
    · simp only [bind, Except.bind, h]

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
  | .find, _, _, _, _, _, hx, hy | .sfind, _, _, _, _, _, hx, hy
  | .nextIn, _, _, _, _, _, hx, hy => by
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
  | .atIn, _, _, _, _, _, _, hx, hy, hz => by
    simp only [Srt.AgreePart, Op3.eval] at hx hy hz ⊢; subst hy hz
    rcases Res.stPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · rfl
    · simp only [bind, Except.bind, State.checkIndex_of_storage h]
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
  | MTerm.memory => M
  | .app0 o => .app0 o
  | .app1 o a => .app1 o (Tm.withMem M a)
  | .app2 o a b => .app2 o (Tm.withMem M a) (Tm.withMem M b)
  | .app3 o a b c => .app3 o (Tm.withMem M a) (Tm.withMem M b) (Tm.withMem M c)

/-- A memory term changes the heap and the next identity only. -/
theorem MTerm.eval_setsMem {σ μ : State} :
    (M : MTerm C) → M.eval σ = .ok μ → μ = { σ with heap := μ.heap, nextId := μ.nextId }
  | MTerm.memory, h => by cases h; rfl
  | MTerm.addM m R, h => by
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
  | MTerm.copySt m v, h => by
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
  | MTerm.write m a v, h => by
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
    | mtSt _ => show Srt.AgreePart .st _ _; exact Res.stPart_ok rfl
    | lit _ | root _ => rfl
    | env _ => show Srt.AgreePart .val _ _; rw [hμ]; rfl
  | .app1 o a => by
    have hr : σ.Rest μ := by rw [hμ]; exact ⟨rfl, rfl, rfl⟩
    exact Op1.eval_part hr o (fun _ _ => by rw [hμ]; rfl) (Or.inr (by rw [hμ]))
      (a.withMem_eval hM hμ)
  | .app2 o a b => by
    exact Op2.eval_part o (Or.inr (by rw [hμ])) (a.withMem_eval hM hμ) (b.withMem_eval hM hμ)
  | .app3 o a b c =>
    Op3.eval_part o (a.withMem_eval hM hμ) (b.withMem_eval hM hμ) (c.withMem_eval hM hμ)

end WithMem

/-! ## `{L ‖ storage := S}` substituted, memory reads included -/

/-- `{L ‖ storage := S}e`, `L` locals: the locals substituted as `Tm.subst`
does and `S` for every `storage`, memory reads included (`Tm.withSt` keeps
out of them), in one pass — `S` reads the pre-state as `L` does, so it is
not substituted into.  A push slot `p[p.length]` and an index check `p[i]`
read the storage of the state they run in, which after the write is `S`'s:
they become `p[p.length]@S` and `p[i]@S`. -/
def Tm.substSt (L : Upd C) (S : STerm C) : Tm C u → Tm C u
  | .pvV x => L.valOf x
  | .pvP x => L.pathOf x
  | .pvS x => L.storOf x
  | .pvI x => L.refOf x
  | STerm.storage => S
  | .app0 o => .app0 o
  | Term.netOf x a =>
    match L.lastWrite x with
    | some _ => Term.stuck
    | none => .app1 (.netOf x) (Tm.substSt L S a)
  | PTerm.next p => .app2 .nextIn S (Tm.substSt L S p)
  | .app1 o a => .app1 o (Tm.substSt L S a)
  | PTerm.at p i => .app3 .atIn S (Tm.substSt L S p) (Tm.substSt L S i)
  | .app2 o a b => .app2 o (Tm.substSt L S a) (Tm.substSt L S b)
  | .app3 o a b c => .app3 o (Tm.substSt L S a) (Tm.substSt L S b) (Tm.substSt L S c)

/-- `{storage := s}e`: `Tm.substSt` with no locals. -/
def Tm.withStM (s : STerm C) (e : Tm C u) : Tm C u := Tm.substSt [] s e

section SubstSt

variable {L : Upd C} {ns : List Var} {S : STerm C} {σ σ₁ τ : State}

theorem Semantics.State.Keeps.rest (hk : σ.Keeps τ) : σ.Rest τ := by
  rw [← hk]; exact ⟨rfl, rfl, rfl⟩

theorem Semantics.State.Keeps.heapEq (hk : σ.Keeps τ) : σ.HeapEq τ := by
  rw [← hk]; exact ⟨rfl, rfl⟩

/-- Two storage readings that agree off some locals are of one storage. -/
theorem StPartEq.of_agree {a b : Res State} (h : ResultsAgree ns a b) : StPartEq a b := by
  match a, b, h with
  | .error _, .error _, h => subst h; exact ⟨rfl⟩
  | .ok _, .ok _, h => exact Res.stPart_ok h.storage

/-- **Read before `{L ‖ storage := S}`, the substituted term reads as the
term after it**, on the part a write looks at: `σ₁` is what `L` leaves of
`σ` (`SubstAgree`) and `S` reads to `τ`, so the state after is `σ₁` with
`τ`'s storage.  A variable reads what `L` binds it to; `storage` reads `S`;
a push slot or an index check reads the storage of `S`, where the term
after reads it in the state; every other symbol reads its arguments
(`OpN.eval_part`). -/
theorem Tm.substSt_eval (h : SubstAgree L ns σ σ₁) (hs : S.eval σ = .ok τ) :
    (e : Tm C u) → Srt.AgreePart u ((Tm.substSt L S e).eval σ) (e.eval { σ₁ with storage := τ.storage })
  | .pvV x => h.val x
  | .pvP x => h.path x
  | .pvI x => h.ref x
  | .pvS x => by
    have hx := StPartEq.of_agree (h.stor x)
    show StPartEq _ _
    simp only [Tm.substSt]
    refine ⟨hx.eq.trans ?_⟩
    simp only [Tm.eval, State.getEnv, bind, Except.bind]
  | .app0 o => by
    cases o with
    | storage =>
      show StPartEq _ _
      simp only [Tm.substSt, Tm.eval, Op0.eval, hs]
      exact Res.stPart_ok rfl
    | memory =>
      show MemPartEq _ _
      exact Res.memPart_ok ⟨h.agree.heap, h.agree.nextId⟩
    | mtSt _ => show StPartEq _ _; exact Res.stPart_ok rfl
    | lit _ | root _ => rfl
    | env _ =>
      show Srt.AgreePart .val _ _
      simp only [Srt.AgreePart, Tm.substSt, Tm.eval, Op0.eval, State.envVal_congr h.agree]
      rfl
  | .app1 o a => by
    have ih := a.substSt_eval h hs
    have hr : σ.Rest { σ₁ with storage := τ.storage } := ⟨h.agree.net, h.agree.selfBalance, h.agree.tx⟩
    cases o with
    | netOf x =>
      have ha : (Tm.substSt L S a).eval σ = a.eval { σ₁ with storage := τ.storage } := ih
      simp only [Tm.substSt]
      split
      · rename_i e hx
        obtain ⟨b, hb, hnl⟩ := h.written x e hx
        show Srt.AgreePart .val _ _
        simp only [Srt.AgreePart, Term.stuck_eval, Tm.eval, Op1.eval, bind, Except.bind]
        rw [show State.getEnv { σ₁ with storage := τ.storage } x = .ok b from hb]
        cases b with
        | ledger l => exact absurd rfl (hnl l)
        | _ => rfl
      · rename_i hx
        show Srt.AgreePart .val _ _
        simp only [Srt.AgreePart, Tm.eval, Op1.eval, ha]
        rw [show State.getEnv { σ₁ with storage := τ.storage } x = σ.getEnv x from
          (h.unwritten x hx).symm]
    | next =>
      have hp : (Tm.substSt L S a).eval σ = a.eval { σ₁ with storage := τ.storage } := ih
      show Srt.AgreePart .path _ _
      simp only [Srt.AgreePart, Tm.substSt, Tm.eval, Op1.eval, Op2.eval, hs, hp, Res.ok_bind]
      rfl
    | _ => exact Op1.eval_part hr _ (fun _ hx => by cases hx) (Or.inl rfl) ih
  | .app2 o a b => by
    have iha := a.substSt_eval h hs
    have ihb := b.substSt_eval h hs
    cases o with
    | «at» =>
      have hp : (Tm.substSt L S a).eval σ = a.eval { σ₁ with storage := τ.storage } := iha
      have hi : (Tm.substSt L S b).eval σ = b.eval { σ₁ with storage := τ.storage } := ihb
      show Srt.AgreePart .path _ _
      simp only [Srt.AgreePart, Tm.substSt, Tm.eval, Op2.eval, Op3.eval, hs, hp, hi, Res.ok_bind]
      rfl
    | _ => exact Op2.eval_part _ (Or.inl rfl) iha ihb
  | .app3 o a b c =>
    Op3.eval_part o (a.substSt_eval h hs) (b.substSt_eval h hs) (c.substSt_eval h hs)

/-- `Tm.substSt_eval` with no locals: read before `{storage := s}`, the
substituted term reads as the term after it. -/
theorem Tm.withStM_eval {s : STerm C} (hs : s.eval σ = .ok τ) (hk : σ.Keeps τ) (e : Tm C u) :
    Srt.AgreePart u ((Tm.withStM s e).eval σ) (e.eval τ) := by
  have h : SubstAgree ([] : Upd C) (Upd.targets ([] : Upd C)) σ σ := Upd.substAgree rfl rfl
  have := Tm.substSt_eval h hs e
  rwa [show { σ with storage := τ.storage } = τ from hk] at this

end SubstSt

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
  | .pay r a => .pay (F r) (F a)
  | .saveNet x => .saveNet x
  | .saveNetMt x => .saveNetMt x
  | .netMt r a => .netMt (F r) (F a)
  | .setBalance a => .setBalance (F a)

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
  | .pay r a | .netMt r a => P r && P a
  | .setBalance a => P a
  | .saveNet _ | .saveNetMt _ => true

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
    simp only [UpdElem.mapTm, UpdElem.write, h1, h2, State.getNet]
  | .pay r a, he => by
    simp only [UpdElem.allTm, Bool.and_eq_true] at he
    have h1 := hF r he.1
    have h2 := hF a he.2
    simp only [Srt.AgreePart] at h1 h2
    simp only [UpdElem.mapTm, UpdElem.write, h1, h2, State.getNet, hr.tx]
  | .saveNet _, _ => by simp only [UpdElem.mapTm, UpdElem.write, hr.net]
  | .saveNetMt _, _ => rfl
  | .netMt r a, he => by
    simp only [UpdElem.allTm, Bool.and_eq_true] at he
    have h1 := hF r he.1
    have h2 := hF a he.2
    simp only [Srt.AgreePart] at h1 h2
    simp only [UpdElem.mapTm, UpdElem.write, h1, h2]
  | .setBalance a, he => by
    have h := hF a he
    simp only [Srt.AgreePart] at h
    simp only [UpdElem.mapTm, UpdElem.write, h]

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

/-- `{L ‖ storage := S}V`: `L`'s locals and `S` substituted into `V`'s
right-hand sides (`Tm.substSt`). -/
def Upd.substSt (L : Upd C) (S : STerm C) (V : Upd C) : Upd C := V.map (·.mapTm (Tm.substSt L S))

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
    have hr : σ.Rest μ := by rw [hμ]; exact ⟨rfl, rfl, rfl⟩
    simp only [Res.ok_bind]
    rw [← hμ, Upd.withMem, Upd.mapTm_foldl (P := fun {_} _ => true) hr
      (fun t _ => Tm.withMem_eval hM hμ t) V (List.all_eq_true.2 fun e _ => by cases e <;> rfl) μ]
    exact Iff.rfl

/-- **`sequentialToParallel`** over a storage write, memory reads included:
`{storage := s}{V} ψ ⟺ {storage := s ‖ {storage := s}V} ψ`. -/
theorem Upd.mergeStorageM_holds (m : Modality) (s : STerm C) (V : Upd C) (ψ : Fml C) (σ : State) :
    holds σ (.upd m (.storage s :: V.withStM s) ψ) ↔ holds σ (.upd m [.storage s] (.upd m V ψ)) := by
  simp only [holds, Upd.apply, List.foldlM_cons, List.foldlM_nil, UpdElem.storage_write]
  cases hs : s.eval σ with
  | error _ => exact Iff.rfl
  | ok τ =>
    have hk : σ.Keeps τ := STerm.eval_keeps s hs
    simp only [Res.ok_bind]
    rw [hk, Upd.withStM, Upd.mapTm_foldl (P := fun {_} _ => true) hk.rest
      (fun t _ => Tm.withStM_eval hs hk t) V (List.all_eq_true.2 fun e _ => by cases e <;> rfl) τ]
    exact Iff.rfl

end Solidity
