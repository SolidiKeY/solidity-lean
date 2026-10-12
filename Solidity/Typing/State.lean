import Solidity.Typing.StoragePreservation

/-!
# State typing: store typings and the global invariant

The typing of the erased state's global part, on top of the storage lemmas
of `Typing/StoragePreservation.lean`:

- a store typing `HeapTy` (the type each memory identity holds) — the
  standard shallow store-typing setup: `MVal.hasTyH` checks a reference
  against `H`'s claim only, so no coinduction is needed and heap cycles
  cost nothing;
- `heapTypedB` / `StateWT`, the invariant of a state's global part
  (storage, heap, allocation counter).  The locals are typed by their
  context (`LTy.WT`, `Typing/Soundness.lean`);
- the weakening lemmas (a store typing extended keeps what was typed),
  the copies' lengths, and `CopyOut`, what a storage→memory copy keeps
  (`Typing/Reachability.lean`'s copies read it).
-/

namespace Solidity
namespace Semantics

open SemanticsProperties (lookupBy_setBy_self lookupBy_setBy_ne
  HeapWellFormed lookupBy_eq_some_mem)

/-! ## Contexts and store typings -/

/-- Store typing H: the type each memory identity holds. -/
abbrev HeapTy := List (Nat × Ty)

/-- `H'` claims everything `H` claims (allocation only adds). -/
def HeapTy.Extends (H H' : HeapTy) : Prop :=
  ∀ id ty, lookupBy id H = some ty -> lookupBy id H' = some ty

theorem HeapTy.Extends.refl (H : HeapTy) : H.Extends H :=
  fun _ _ h => h

theorem HeapTy.Extends.trans {H₁ H₂ H₃ : HeapTy}
    (h12 : H₁.Extends H₂) (h23 : H₂.Extends H₃) : H₁.Extends H₃ :=
  fun id ty h => h23 id ty (h12 id ty h)

/-- Adding a *fresh* claim extends the typing. -/
theorem HeapTy.extends_setBy_fresh {H : HeapTy} {id : Nat} {ty : Ty}
    (hfresh : lookupBy id H = none) : H.Extends (setBy id ty H) := by
  intro id' ty' h
  have hne : id' ≠ id := by
    intro he
    subst he
    rw [hfresh] at h
    exact Option.noConfusion h
  rw [lookupBy_setBy_ne hne]
  exact h

/-- `setBy` never breaks key uniqueness: it replaces in place or
appends a genuinely new key. -/
theorem lookupBy_setBy_none [DecidableEq κ] {l : List (κ × α)}
    {k k' : κ} {v : α} (hne : k' ≠ k) (h : lookupBy k' l = none) :
    lookupBy k' (setBy k v l) = none := by
  induction l with
  | nil => simp [setBy, lookupBy, hne]
  | cons p rest ih =>
      obtain ⟨k₀, v₀⟩ := p
      simp only [lookupBy] at h
      by_cases hk0 : k' = k₀
      · rw [if_pos hk0] at h; exact Option.noConfusion h
      · rw [if_neg hk0] at h
        by_cases hkk : k = k₀
        · subst hkk
          simp [setBy, lookupBy, hne, h]
        · simp only [setBy, if_neg hkk, lookupBy, if_neg hk0]
          exact ih h

theorem nodupKeysB_setBy [DecidableEq κ] {l : List (κ × α)} {k : κ}
    {v : α} (hnd : nodupKeysB l = true) :
    nodupKeysB (setBy k v l) = true := by
  induction l with
  | nil => simp [setBy, nodupKeysB, lookupBy]
  | cons p rest ih =>
      obtain ⟨k', v'⟩ := p
      simp only [nodupKeysB, Bool.and_eq_true] at hnd
      by_cases hk : k = k'
      · subst hk
        simp [setBy, nodupKeysB, hnd.1, hnd.2]
      · simp only [setBy, if_neg hk, nodupKeysB, Bool.and_eq_true]
        refine ⟨?_, ih hnd.2⟩
        rw [lookupBy_setBy_none (Ne.symm hk)
          (Option.isNone_iff_eq_none.mp hnd.1)]
        rfl

/-! ## Shallow heap typing -/

/-- A memory slot value inhabits a type, checking references against
`H`'s claim only (shallow — the store-typing trick). -/
def MVal.hasTyH (H : HeapTy) : MVal -> Ty -> Bool
  | MVal.prim (PrimVal.int _), Ty.uint => true
  | MVal.prim (PrimVal.int _), Ty.int => true
  | MVal.prim (PrimVal.bool _), Ty.bool => true
  | MVal.ref id, Ty.ref r => lookupBy id H == some (Ty.ref r)
  | _, _ => false

/-- A memory object inhabits a (reference) type, one level deep:
struct fields against `structDef`, array elements against the element
type, a fixed-size array marked and as long as its type. Mapping types have
no memory objects. -/
def MObj.hasTyH (H : HeapTy) : MObj -> Ty -> Bool
  | MObj.struct fields, Ty.ref (RefTy.struct s) => hasTyHFields s fields
  | MObj.array elems fx, Ty.ref (RefTy.array elem) => !fx && hasTyHElems elem elems
  | MObj.array elems fx, Ty.ref (RefTy.fixed elem n) =>
      fx && elems.length == n && hasTyHElems elem elems
  | _, _ => false
where
  hasTyHFields (s : Name) : List (Name × MVal) -> Bool
    | [] => true
    | (n, v) :: rest =>
        (match lookupBy n (structDef s) with
         | some ty => MVal.hasTyH H v ty
         | none => false) && hasTyHFields s rest
  hasTyHElems (elem : Ty) : List MVal -> Bool
    | [] => true
    | v :: rest => MVal.hasTyH H v elem && hasTyHElems elem rest

/-- Every identity `H` claims exists and matches its claim. -/
def heapTypedB (H : HeapTy) (heap : List (Nat × MObj)) : Bool :=
  H.all fun r =>
    match lookupBy r.1 heap with
    | some obj => obj.hasTyH H r.2
    | none => false

/-! ## The full state invariant -/

/-- The global part of a state is well-typed: layout keys and store typing
unique, storage well-typed, heap matching `H`, allocation counter fresh.
The executable model of the `wellFormed` assumption the solkey proof
obligations need, which every erased typed state's global part satisfies
(`State.glob_wt`). -/
structure StateWT (H : HeapTy) (L : Layout) (s : State) : Prop where
  layoutNodup : nodupKeysB L.globals = true
  heapTyNodup : nodupKeysB H = true
  storage : wellTypedStorageB L s.storage = true
  heap : heapTypedB H s.heap = true
  heapWf : HeapWellFormed s

/-! ## Executable heap freshness

`HeapWellFormed` quantifies over every `Nat`, so a concrete witness
cannot be closed by `decide`; the bound-check over the heap's keys is
equivalent and executable. -/

/-- Every allocated identity is strictly below the allocation counter. -/
def heapWellFormedB (s : State) : Bool :=
  s.heap.all fun r => decide (r.1 < s.nextId)

theorem heapWellFormedB_iff {s : State} :
    heapWellFormedB s = true ↔ HeapWellFormed s := by
  constructor
  · intro h id hid
    have aux : ∀ (l : List (Nat × MObj)),
        (l.all fun r => decide (r.1 < s.nextId)) = true ->
        lookupBy id l = none := by
      intro l hl
      induction l with
      | nil => rfl
      | cons p rest ih =>
          simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
          have hne : id ≠ p.1 := by omega
          simp only [lookupBy, if_neg hne]
          exact ih hl.2
    exact aux s.heap h
  · intro h
    apply List.all_eq_true.mpr
    intro r hr
    apply decide_eq_true
    apply Nat.lt_of_not_le
    intro hge
    have hnone := h r.1 hge
    have hsome := lookupBy_isSome_of_mem (k := r.1) (v := r.2) hr
    rw [hnone] at hsome
    exact Bool.noConfusion hsome

/-- Every `StateWT` conjunct is decidable once `heapWf` is read through
`heapWellFormedB`: one `decide` per concrete witness. -/
theorem StateWT.ofB {H : HeapTy} {L : Layout} {s : State}
    (h : (nodupKeysB L.globals && nodupKeysB H && wellTypedStorageB L s.storage &&
      heapTypedB H s.heap && heapWellFormedB s) = true) :
    StateWT H L s := by
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, heapWellFormedB_iff.mp h.2⟩

/-! ## Weakening -/

theorem MVal.hasTyH_mono {H H' : HeapTy} {v : MVal} {ty : Ty}
    (hext : H.Extends H') (h : MVal.hasTyH H v ty = true) :
    MVal.hasTyH H' v ty = true := by
  cases v with
  | prim p =>
      cases p <;> cases ty with
      | prim pt => cases pt <;> simp_all [MVal.hasTyH]
      | ref r => simp_all [MVal.hasTyH]
  | ref id =>
      cases ty with
      | prim pt => cases pt <;> simp_all [MVal.hasTyH]
      | ref r =>
          simp only [MVal.hasTyH, beq_iff_eq] at h ⊢
          exact hext id _ h

private theorem hasTyHFields_mono {H H' : HeapTy} {s : Name}
    {fields : List (Name × MVal)} (hext : H.Extends H')
    (h : MObj.hasTyH.hasTyHFields H s fields = true) :
    MObj.hasTyH.hasTyHFields H' s fields = true := by
  induction fields with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨n, v⟩ := p
      simp only [MObj.hasTyH.hasTyHFields, Bool.and_eq_true] at h ⊢
      refine ⟨?_, ih h.2⟩
      cases hdef : lookupBy n (structDef s) with
      | none => rw [hdef] at h; exact Bool.noConfusion h.1
      | some ty =>
          rw [hdef] at h
          exact MVal.hasTyH_mono hext h.1

private theorem hasTyHElems_mono {H H' : HeapTy} {elem : Ty}
    {elems : List MVal} (hext : H.Extends H')
    (h : MObj.hasTyH.hasTyHElems H elem elems = true) :
    MObj.hasTyH.hasTyHElems H' elem elems = true := by
  induction elems with
  | nil => rfl
  | cons v rest ih =>
      simp only [MObj.hasTyH.hasTyHElems, Bool.and_eq_true] at h ⊢
      exact ⟨MVal.hasTyH_mono hext h.1, ih h.2⟩

theorem MObj.hasTyH_mono {H H' : HeapTy} {obj : MObj} {ty : Ty}
    (hext : H.Extends H') (h : MObj.hasTyH H obj ty = true) :
    MObj.hasTyH H' obj ty = true := by
  cases obj with
  | struct fields =>
      cases ty with
      | prim pt => simp [MObj.hasTyH] at h
      | ref r =>
          cases r with
          | struct s =>
              simpa only [MObj.hasTyH] using
                hasTyHFields_mono hext (by simpa [MObj.hasTyH] using h)
          | array elem => simp [MObj.hasTyH] at h
          | fixed elem _ => simp [MObj.hasTyH] at h
          | mapping k v => simp [MObj.hasTyH] at h
  | array elems fx =>
      cases ty with
      | prim pt => simp [MObj.hasTyH] at h
      | ref r =>
          cases r with
          | struct s => simp [MObj.hasTyH] at h
          | array elem =>
              simp only [MObj.hasTyH, Bool.and_eq_true] at h ⊢
              exact ⟨h.1, hasTyHElems_mono hext h.2⟩
          | fixed elem n =>
              simp only [MObj.hasTyH, Bool.and_eq_true] at h ⊢
              exact ⟨h.1, hasTyHElems_mono hext h.2⟩
          | mapping k v => simp [MObj.hasTyH] at h

/-- On a fresh key, `setBy` is exactly an append. -/
theorem setBy_eq_append_of_fresh [DecidableEq κ] {l : List (κ × α)}
    {k : κ} {v : α} (hfresh : lookupBy k l = none) :
    setBy k v l = l ++ [(k, v)] := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨k', v'⟩ := p
      simp only [lookupBy] at hfresh
      by_cases hk : k = k'
      · rw [if_pos hk] at hfresh; exact Option.noConfusion hfresh
      · rw [if_neg hk] at hfresh
        simp only [setBy, if_neg hk, List.cons_append]
        exact congrArg _ (ih hfresh)

/-- Allocating a typed object under a fresh claim keeps the heap
typed. -/
theorem heapTypedB_alloc {H : HeapTy} {s : State} {obj : MObj}
    {ty : Ty}
    (hheap : heapTypedB H s.heap = true)
    (hwf : HeapWellFormed s)
    (hfresh : lookupBy s.nextId H = none)
    (hobj : MObj.hasTyH (setBy s.nextId ty H) obj ty = true) :
    heapTypedB (setBy s.nextId ty H) (s.alloc obj).1.heap = true := by
  have hext : H.Extends (setBy s.nextId ty H) :=
    HeapTy.extends_setBy_fresh hfresh
  refine List.all_eq_true.mpr fun r hr => ?_
  show (match lookupBy r.1 (s.alloc obj).1.heap with
    | some o => o.hasTyH (setBy s.nextId ty H) r.2
    | none => false) = true
  have hheap' : (s.alloc obj).1.heap = setBy s.nextId obj s.heap := rfl
  rw [setBy_eq_append_of_fresh hfresh] at hr
  rcases List.mem_append.mp hr with hold | hnew
  · have hid : r.1 ≠ s.nextId := by
      intro he
      have hmem' : (s.nextId, r.2) ∈ H := by
        rw [<- he]
        exact hold
      have := lookupBy_isSome_of_mem hmem'
      rw [hfresh] at this
      exact Bool.noConfusion this
    rw [hheap', lookupBy_setBy_ne hid]
    have := List.all_eq_true.mp hheap _ hold
    cases hlook : lookupBy r.1 s.heap with
    | none => rw [hlook] at this; exact Bool.noConfusion this
    | some o =>
        rw [hlook] at this
        exact MObj.hasTyH_mono hext this
  · have hr' : r = (s.nextId, ty) := by simpa using hnew
    subst hr'
    rw [hheap', lookupBy_setBy_self]
    exact hobj

/-! ## The copies' lengths -/

/-- A copy back from memory has as many elements as the memory array: a
fixed-size array lands as long as it was. -/
theorem copyMElems_length {s : State} {rem : List Nat} :
    ∀ {elems : List MVal} {selems : List SVal},
      copyMElems s rem elems = Except.ok selems -> selems.length = elems.length := by
  intro elems
  induction elems with
  | nil => intro selems h; simp only [copyMElems] at h; cases h; rfl
  | cons v rest ih =>
      intro selems h
      simp only [copyMElems, bind, Except.bind] at h
      split at h
      · exact nomatch h
      · split at h
        · exact nomatch h
        · rename_i hr
          cases h
          simp [ih hr]

/-- A copy into memory has as many elements as the storage array. -/
theorem copyStElems_length {s : State} :
    ∀ {elems : List SVal} {s' : State} {melems : List MVal},
      copyStElems s elems = Except.ok (s', melems) -> melems.length = elems.length := by
  intro elems
  induction elems generalizing s with
  | nil => intro s' melems h; simp only [copyStElems] at h; cases h; rfl
  | cons v rest ih =>
      intro s' melems h
      simp only [copyStElems, bind, Except.bind] at h
      split at h
      · exact nomatch h
      · split at h
        · exact nomatch h
        · rename_i hr
          cases h
          simp [ih hr]

/-! ## What a storage→memory copy keeps -/

/-- What `copyStToM` (and each of its list companions) guarantees:
the store typing extends by fresh claims only, stays nodup-keyed and
heap-typed, the allocation counter stays well-formed, and storage and
env are untouched. -/
structure CopyOut (H : HeapTy) (s : State) (H' : HeapTy) (s' : State) :
    Prop where
  ext : H.Extends H'
  nodup : nodupKeysB H' = true
  heap : heapTypedB H' s'.heap = true
  heapWf : HeapWellFormed s'
  storage : s'.storage = s.storage
  env : s'.env = s.env

theorem CopyOut.refl {H : HeapTy} {s : State}
    (hnd : nodupKeysB H = true) (hheap : heapTypedB H s.heap = true)
    (hwf : HeapWellFormed s) : CopyOut H s H s :=
  ⟨HeapTy.Extends.refl H, hnd, hheap, hwf, rfl, rfl⟩

theorem CopyOut.trans {H₁ H₂ H₃ : HeapTy} {s₁ s₂ s₃ : State}
    (h12 : CopyOut H₁ s₁ H₂ s₂) (h23 : CopyOut H₂ s₂ H₃ s₃) :
    CopyOut H₁ s₁ H₃ s₃ :=
  ⟨h12.ext.trans h23.ext, h23.nodup, h23.heap, h23.heapWf,
    h23.storage.trans h12.storage, h23.env.trans h12.env⟩

/-- A heap-typed store typing never claims the next fresh identity. -/
theorem heapTy_fresh {H : HeapTy} {s : State}
    (hheap : heapTypedB H s.heap = true) (hwf : HeapWellFormed s) :
    lookupBy s.nextId H = none := by
  cases hlook : lookupBy s.nextId H with
  | none => rfl
  | some ty0 =>
      have hmem := lookupBy_eq_some_mem hlook
      have := List.all_eq_true.mp hheap _ hmem
      rw [hwf.nextId_fresh] at this
      exact Bool.noConfusion this

/-- The allocation step of a storage→memory copy (`copyStToM_canon`'s node arms): claim
the fresh identity at the node's (reference) type. -/
theorem CopyOut.alloc {H H₁ : HeapTy} {s s₁ : State} {r : RefTy}
    {obj : MObj} (hout : CopyOut H s H₁ s₁)
    (hobj : MObj.hasTyH H₁ obj (Ty.ref r) = true) :
    CopyOut H s (setBy s₁.nextId (Ty.ref r) H₁) (s₁.alloc obj).1 ∧
      MVal.hasTyH (setBy s₁.nextId (Ty.ref r) H₁)
        (MVal.ref s₁.nextId) (Ty.ref r) = true := by
  have hfresh : lookupBy s₁.nextId H₁ = none :=
    heapTy_fresh hout.heap hout.heapWf
  have hext : H₁.Extends (setBy s₁.nextId (Ty.ref r) H₁) :=
    HeapTy.extends_setBy_fresh hfresh
  refine ⟨⟨hout.ext.trans hext, nodupKeysB_setBy hout.nodup,
    heapTypedB_alloc hout.heap hout.heapWf hfresh
      (MObj.hasTyH_mono hext hobj),
    hout.heapWf.alloc obj,
    hout.storage, hout.env⟩, ?_⟩
  simp [MVal.hasTyH, lookupBy_setBy_self]


end Semantics
end Solidity
