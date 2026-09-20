import Solidity.Typing.StoragePreservation

/-!
# State typing: contexts, heap/env invariants, copy typing

The second layer of the type-soundness development. `StoragePreservation`
handles the storage tree; this module adds what full soundness needs on
top:

- a binding context `Ctx` (what each local name is bound as: a stack
  value, a storage-path alias, a memory reference) and a store typing
  `HeapTy` (the type each memory identity holds) — the standard shallow
  store-typing setup: `MVal.hasTyH` checks a reference against `H`'s
  claim only, so no coinduction is needed and heap cycles cost nothing;
- `envTypedB` / `heapTypedB` / `StateWT`, the full state invariant.
  `envTypedB` also forbids *stray* `spath` bindings (aliases unknown to
  `Γ`): `resolveS` consults the env before falling back to a global
  root, so an untracked alias could silently retarget a well-typed
  global read;
- `wtExpr`, the well-annotatedness check generalizing
  `StorageTyping.wtStorageExpr` to every kind and nesting (the check is
  *annotation consistency* — kind mismatches and out-of-range indices
  are left to die at runtime, where the soundness theorems are
  vacuous). Deliberate v1 exclusions: `.length` reads (no `tyAtSegs`
  story) and every call but the `net` ledger read;
- the cross-domain copy typing theorems: `copyMToSt_hasTy`
  (memory→storage: a heap-typed source lands as a storage value of its
  type — the fuel is the interpreter's own cycle guard, so exhaustion
  is vacuous) and `copyStToM_typed` (storage→memory: the copy
  allocates, so the store typing *extends*, and everything already
  typed stays typed — the weakening lemmas).
-/

namespace Solidity
namespace Semantics

open SemanticsProperties (lookupBy_setBy_self lookupBy_setBy_ne
  HeapWellFormed)

/-! ## Contexts and store typings -/

/-- What a local name is bound as (the typing side of `Binding`). -/
inductive BTy where
  | stack (ty : Ty)
  | path (ty : Ty)
  | mem (ty : Ty)
  deriving DecidableEq, Repr

/-- Binding context Γ. -/
abbrev Ctx := List (Name × BTy)

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
type. Mapping types have no memory objects. -/
def MObj.hasTyH (H : HeapTy) : MObj -> Ty -> Bool
  | MObj.struct fields, Ty.ref (RefTy.struct s) => hasTyHFields s fields
  | MObj.array elems, Ty.ref (RefTy.array elem) => hasTyHElems elem elems
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

/-! ## Env typing -/

/-- The binding matches its context entry. -/
def BTy.matchesB (L : Layout) (H : HeapTy) : BTy -> Binding -> Bool
  | BTy.stack ty, Binding.val v => (Value.toSVal v).hasTy ty
  | BTy.path ty, Binding.spath root segs => L.tyAt root segs == some ty
  | BTy.mem ty, Binding.mref id => MVal.hasTyH H (MVal.ref id) ty
  | _, _ => false

/-- Γ-tracked names are bound as Γ says, and no *untracked* `spath` or
`mref` binding exists: an untracked alias would shadow a global root
inside `resolveS` with a path the layout knows nothing about, and an
untracked memory reference would let `resolveMBase`/`readM` produce an
identity the store typing knows nothing about. (Untracked `val`
bindings are harmless — every read of one goes through Γ.) -/
def envTypedB (Γ : Ctx) (L : Layout) (H : HeapTy)
    (env : List (Name × Binding)) : Bool :=
  (Γ.all fun g =>
    match lookupBy g.1 env with
    | some b => BTy.matchesB L H g.2 b
    | none => false) &&
  (env.all fun nb =>
    match nb.2 with
    | Binding.spath _ _ => (lookupBy nb.1 Γ).isSome
    | Binding.mref _ => (lookupBy nb.1 Γ).isSome
    | _ => true)

/-! ## The full state invariant -/

/-- Full state well-typedness: layout and context keys unique, storage
well-typed, env matching Γ, heap matching H, allocation counter fresh.
This is the invariant `TypeSoundness` carries through evaluation and
execution — the executable model of the `wellFormed` assumption the
solkey proof obligations need. -/
structure StateWT (Γ : Ctx) (H : HeapTy) (L : Layout) (s : State) :
    Prop where
  layoutNodup : nodupKeysB L.globals = true
  ctxNodup : nodupKeysB Γ = true
  heapTyNodup : nodupKeysB H = true
  storage : wellTypedStorageB L s.storage = true
  env : envTypedB Γ L H s.env = true
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
`heapWellFormedB`: one `native_decide` per concrete witness. -/
theorem StateWT.ofB {Γ : Ctx} {H : HeapTy} {L : Layout} {s : State}
    (h : (nodupKeysB L.globals && nodupKeysB Γ && nodupKeysB H &&
      wellTypedStorageB L s.storage && envTypedB Γ L H s.env &&
      heapTypedB H s.heap && heapWellFormedB s) = true) :
    StateWT Γ H L s := by
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2,
    h.1.2, heapWellFormedB_iff.mp h.2⟩

/-! ## Deduplicating a store typing

A store typing with a duplicated key is read through `lookupBy`, which
sees only the first row.  `dedupKeys` keeps exactly the rows `lookupBy`
sees, so it changes no lookup and is key-unique — the tool that shows
`heapTyNodup` is not needed by the type-soundness headline
(`Counterexamples/PreservationNecessity.lean`, `execStmt_sound_dupHeapTy`). -/

/-- Keep the first row of each key (`seen` accumulates the keys kept). -/
def dedupKeysAux [DecidableEq κ] : List (κ × α) -> List κ -> List (κ × α)
  | [], _ => []
  | (k, v) :: rest, seen =>
      if k ∈ seen then dedupKeysAux rest seen
      else (k, v) :: dedupKeysAux rest (k :: seen)

def dedupKeys [DecidableEq κ] (l : List (κ × α)) : List (κ × α) :=
  dedupKeysAux l []

theorem lookupBy_dedupKeysAux [DecidableEq κ] (k : κ) :
    ∀ (l : List (κ × α)) (seen : List κ),
      lookupBy k (dedupKeysAux l seen) =
        if k ∈ seen then none else lookupBy k l
  | [], seen => by
      cases h : decide (k ∈ seen) <;> simp_all [dedupKeysAux, lookupBy]
  | (k', v) :: rest, seen => by
      simp only [dedupKeysAux]
      by_cases hk' : k' ∈ seen
      · rw [if_pos hk', lookupBy_dedupKeysAux k rest seen]
        by_cases hk : k ∈ seen
        · simp [hk]
        · have hne : k ≠ k' := fun he => hk (he ▸ hk')
          simp [hk, lookupBy, hne]
      · rw [if_neg hk']
        simp only [lookupBy]
        by_cases hkk : k = k'
        · subst hkk
          simp [hk']
        · rw [if_neg hkk, lookupBy_dedupKeysAux k rest (k' :: seen)]
          simp [List.mem_cons, hkk]

theorem lookupBy_dedupKeys [DecidableEq κ] (k : κ) (l : List (κ × α)) :
    lookupBy k (dedupKeys l) = lookupBy k l := by
  simp [dedupKeys, lookupBy_dedupKeysAux]

theorem nodupKeysB_dedupKeysAux [DecidableEq κ] :
    ∀ (l : List (κ × α)) (seen : List κ),
      nodupKeysB (dedupKeysAux l seen) = true
  | [], _ => rfl
  | (k, v) :: rest, seen => by
      simp only [dedupKeysAux]
      by_cases hk : k ∈ seen
      · rw [if_pos hk]; exact nodupKeysB_dedupKeysAux rest seen
      · rw [if_neg hk]
        simp only [nodupKeysB, Bool.and_eq_true]
        refine ⟨?_, nodupKeysB_dedupKeysAux rest (k :: seen)⟩
        rw [lookupBy_dedupKeysAux]
        simp

theorem nodupKeysB_dedupKeys [DecidableEq κ] (l : List (κ × α)) :
    nodupKeysB (dedupKeys l) = true :=
  nodupKeysB_dedupKeysAux l []

theorem mem_of_mem_dedupKeysAux [DecidableEq κ] {p : κ × α} :
    ∀ {l : List (κ × α)} {seen : List κ},
      p ∈ dedupKeysAux l seen -> p ∈ l
  | [], _, h => by simp [dedupKeysAux] at h
  | (k, v) :: rest, seen, h => by
      simp only [dedupKeysAux] at h
      by_cases hk : k ∈ seen
      · rw [if_pos hk] at h
        exact List.mem_cons_of_mem _ (mem_of_mem_dedupKeysAux h)
      · rw [if_neg hk] at h
        rcases List.mem_cons.mp h with rfl | h
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (mem_of_mem_dedupKeysAux h)

theorem mem_of_mem_dedupKeys [DecidableEq κ] {p : κ × α}
    {l : List (κ × α)} (h : p ∈ dedupKeys l) : p ∈ l :=
  mem_of_mem_dedupKeysAux h

/-- Deduplication changes no lookup, so it extends and is extended by
the original typing. -/
theorem HeapTy.extends_dedup (H : HeapTy) : HeapTy.Extends H (dedupKeys H) :=
  fun id ty h => by rw [lookupBy_dedupKeys]; exact h

theorem HeapTy.dedup_extends (H : HeapTy) : HeapTy.Extends (dedupKeys H) H :=
  fun id ty h => by rw [lookupBy_dedupKeys] at h; exact h

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
          | mapping k v => simp [MObj.hasTyH] at h
  | array elems =>
      cases ty with
      | prim pt => simp [MObj.hasTyH] at h
      | ref r =>
          cases r with
          | struct s => simp [MObj.hasTyH] at h
          | array elem =>
              simpa only [MObj.hasTyH] using
                hasTyHElems_mono hext (by simpa [MObj.hasTyH] using h)
          | mapping k v => simp [MObj.hasTyH] at h

theorem BTy.matchesB_mono {L : Layout} {H H' : HeapTy} {bty : BTy}
    {b : Binding} (hext : H.Extends H')
    (h : BTy.matchesB L H bty b = true) :
    BTy.matchesB L H' bty b = true := by
  cases bty <;> cases b <;> simp_all [BTy.matchesB]
  case mem.mref ty id =>
    exact MVal.hasTyH_mono hext (by simpa [BTy.matchesB] using h)

theorem envTypedB_mono {Γ : Ctx} {L : Layout} {H H' : HeapTy}
    {env : List (Name × Binding)} (hext : H.Extends H')
    (h : envTypedB Γ L H env = true) : envTypedB Γ L H' env = true := by
  simp only [envTypedB, Bool.and_eq_true] at h ⊢
  refine ⟨List.all_eq_true.mpr fun g hg => ?_, h.2⟩
  have := List.all_eq_true.mp h.1 g hg
  cases hlook : lookupBy g.1 env with
  | none => rw [hlook] at this; exact Bool.noConfusion this
  | some b =>
      rw [hlook] at this
      exact BTy.matchesB_mono hext this

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

/-- A heap typed by `H` is typed by `dedupKeys H`: every kept row is a
row of `H`, and each claim transports along `HeapTy.extends_dedup`. -/
theorem heapTypedB_dedup {H : HeapTy} {heap : List (Nat × MObj)}
    (h : heapTypedB H heap = true) : heapTypedB (dedupKeys H) heap = true := by
  simp only [heapTypedB, List.all_eq_true] at h ⊢
  intro r hr
  have hrow := h r (mem_of_mem_dedupKeys hr)
  cases hl : lookupBy r.1 heap with
  | none => rw [hl] at hrow; exact Bool.noConfusion hrow
  | some obj =>
      rw [hl] at hrow
      exact MObj.hasTyH_mono (HeapTy.extends_dedup H) hrow

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

/-! ## Well-annotated expressions

Annotation consistency for every kind and nesting, the general form of
`StorageTyping.wtStorageExpr`. Storage vars resolve through Γ first
(mirroring `resolveS`'s env-first lookup); a Γ-tracked alias must be
`origin`-local, because `resolveLoc`/`execAssign` route *global*-origin
vars straight to the storage root without consulting the env. -/
def wtExpr (Γ : Ctx) (L : Layout) : WrappedExpr -> Bool
  | WrappedExpr.var Kind.stack ty fld =>
      lookupBy fld.name Γ == some (BTy.stack ty)
  | WrappedExpr.var Kind.storage ty fld =>
      (match lookupBy fld.name Γ with
       | some (BTy.path ty') =>
           ty == ty' && (fld.origin == some StorageOrigin.local)
       | some _ => false
       | none =>
           fld.origin == some StorageOrigin.global &&
             lookupBy fld.name L.globals == some ty)
  | WrappedExpr.var Kind.memory ty fld =>
      lookupBy fld.name Γ == some (BTy.mem ty)
  | WrappedExpr.field _ ty base fld =>
      wtExpr Γ L base && (segTy base.ty (Seg.field fld.name) == some ty)
  | WrappedExpr.index _ ty base index =>
      wtExpr Γ L base && wtExpr Γ L index && (elemTy base.ty == some ty)
  | WrappedExpr.pushPlace target =>
      wtExpr Γ L target &&
        (match target.ty with
         | Ty.ref (RefTy.array elem) => defaultOk elem
         | _ => false)
  | WrappedExpr.bool _ => true
  | WrappedExpr.intLit ty _ => isNumericTy ty
  | Typed.WrappedExpr.mkCall _ ty "net" [addr] =>
      isNumericTy ty && wtExpr Γ L addr
  | Typed.WrappedExpr.mkBinop _ l r => wtExpr Γ L l && wtExpr Γ L r
  | Typed.WrappedExpr.mkUnop _ arg => wtExpr Γ L arg
  | Typed.WrappedExpr.mkIncDec _ target => wtExpr Γ L target
  | Typed.WrappedExpr.mkTernary c t e =>
      wtExpr Γ L c && wtExpr Γ L t && wtExpr Γ L e && (t.ty == e.ty)
  | _ => false

/-! ## Memory→storage copy typing

`rem` is the interpreter's own cycle guard (`copyMem` passes every heap
identity): a cyclic heap exhausts it and errors, so the theorems are
stated for every `rem` and exhaustion is vacuous. -/

private theorem copyMFields_hasTy {s : State} {H : HeapTy} {rem : List Nat}
    {str : Name}
    (IH : ∀ {mv : MVal} {ty : Ty} {sv : SVal},
      MVal.hasTyH H mv ty = true -> copyMToSt s rem mv = Except.ok sv ->
      sv.hasTy ty = true) :
    ∀ {fields : List (Name × MVal)} {sfields : List (Name × SVal)},
      MObj.hasTyH.hasTyHFields H str fields = true ->
      copyMFields s rem fields = Except.ok sfields ->
      SVal.hasTy.hasTyFields str sfields = true := by
  intro fields
  induction fields with
  | nil =>
      intro sfields _ hcopy
      simp only [copyMFields] at hcopy
      simp [<- Except.ok.inj hcopy, SVal.hasTy.hasTyFields]
  | cons p rest ih =>
      intro sfields h hcopy
      obtain ⟨n, v⟩ := p
      simp only [MObj.hasTyH.hasTyHFields, Bool.and_eq_true] at h
      simp only [copyMFields, bind, Except.bind] at hcopy
      cases hv : copyMToSt s rem v with
      | error e => rw [hv] at hcopy; exact nomatch hcopy
      | ok sv =>
          rw [hv] at hcopy
          try dsimp only at hcopy
          cases hrest : copyMFields s rem rest with
          | error e => rw [hrest] at hcopy; exact nomatch hcopy
          | ok srest =>
              rw [hrest] at hcopy
              try dsimp only at hcopy
              simp only [<- Except.ok.inj hcopy,
                SVal.hasTy.hasTyFields, Bool.and_eq_true]
              refine ⟨?_, ih h.2 hrest⟩
              cases hdef : lookupBy n (structDef str) with
              | none => rw [hdef] at h; exact Bool.noConfusion h.1
              | some ty =>
                  rw [hdef] at h
                  exact IH h.1 hv

private theorem copyMElems_hasTy {s : State} {H : HeapTy} {rem : List Nat}
    {elem : Ty}
    (IH : ∀ {mv : MVal} {ty : Ty} {sv : SVal},
      MVal.hasTyH H mv ty = true -> copyMToSt s rem mv = Except.ok sv ->
      sv.hasTy ty = true) :
    ∀ {elems : List MVal} {selems : List SVal},
      MObj.hasTyH.hasTyHElems H elem elems = true ->
      copyMElems s rem elems = Except.ok selems ->
      SVal.hasTy.hasTyElems elem selems = true := by
  intro elems
  induction elems with
  | nil =>
      intro selems _ hcopy
      simp only [copyMElems] at hcopy
      simp [<- Except.ok.inj hcopy, SVal.hasTy.hasTyElems]
  | cons v rest ih =>
      intro selems h hcopy
      simp only [MObj.hasTyH.hasTyHElems, Bool.and_eq_true] at h
      simp only [copyMElems, bind, Except.bind] at hcopy
      cases hv : copyMToSt s rem v with
      | error e => rw [hv] at hcopy; exact nomatch hcopy
      | ok sv =>
          rw [hv] at hcopy
          try dsimp only at hcopy
          cases hrest : copyMElems s rem rest with
          | error e => rw [hrest] at hcopy; exact nomatch hcopy
          | ok srest =>
              rw [hrest] at hcopy
              try dsimp only at hcopy
              simp only [<- Except.ok.inj hcopy,
                SVal.hasTy.hasTyElems, Bool.and_eq_true]
              exact ⟨IH h.1 hv, ih h.2 hrest⟩

/-- Memory→storage copy typing: a heap-typed slot value copies to a
storage value of its type. -/
theorem copyMToSt_hasTy {H : HeapTy} {s : State}
    (hheap : heapTypedB H s.heap = true) {rem : List Nat} :
    ∀ {mv : MVal} {ty : Ty} {sv : SVal},
      MVal.hasTyH H mv ty = true ->
      copyMToSt s rem mv = Except.ok sv -> sv.hasTy ty = true := by
  intro mv ty sv h hcopy
  cases mv with
  | prim p =>
      cases p with
      | int n =>
          simp only [copyMToSt] at hcopy
          cases Except.ok.inj hcopy
          cases ty with
          | prim pt => cases pt <;> simp_all [MVal.hasTyH, SVal.hasTy]
          | ref r => simp [MVal.hasTyH] at h
      | bool b =>
          simp only [copyMToSt] at hcopy
          cases Except.ok.inj hcopy
          cases ty with
          | prim pt => cases pt <;> simp_all [MVal.hasTyH, SVal.hasTy]
          | ref r => simp [MVal.hasTyH] at h
  | ref id =>
      cases ty with
      | prim pt => cases pt <;> simp [MVal.hasTyH] at h
      | ref r =>
          simp only [MVal.hasTyH, beq_iff_eq] at h
          have hin := lookupBy_eq_some_mem h
          have hrow := List.all_eq_true.mp hheap _ hin
          by_cases hmem : id ∈ rem
          · simp only [copyMToSt, hmem, dif_pos, State.getObj] at hcopy
            cases hlook : lookupBy id s.heap with
            | none => rw [hlook] at hrow; exact Bool.noConfusion hrow
            | some obj =>
                rw [hlook] at hrow hcopy
                cases obj with
                | struct fields =>
                    cases r with
                    | struct str =>
                        simp only [bind, Except.bind] at hcopy
                        cases hfs : copyMFields s (rem.erase id) fields with
                        | error e =>
                            rw [hfs] at hcopy; exact nomatch hcopy
                        | ok sfields =>
                            rw [hfs] at hcopy
                            try dsimp only at hcopy
                            simp only [<- Except.ok.inj hcopy, SVal.hasTy]
                            exact copyMFields_hasTy
                              (fun hv hc => copyMToSt_hasTy hheap hv hc)
                              (by simpa [MObj.hasTyH] using hrow) hfs
                    | array elem => simp [MObj.hasTyH] at hrow
                    | mapping k v => simp [MObj.hasTyH] at hrow
                | array elems =>
                    cases r with
                    | struct str => simp [MObj.hasTyH] at hrow
                    | array elem =>
                        simp only [bind, Except.bind] at hcopy
                        cases hes : copyMElems s (rem.erase id) elems with
                        | error e =>
                            rw [hes] at hcopy; exact nomatch hcopy
                        | ok selems =>
                            rw [hes] at hcopy
                            try dsimp only at hcopy
                            simp only [<- Except.ok.inj hcopy, SVal.hasTy,
                              SVal.hasTy.hasTyElems, Bool.and_true]
                            exact copyMElems_hasTy
                              (fun hv hc => copyMToSt_hasTy hheap hv hc)
                              (by simpa [MObj.hasTyH] using hrow) hes
                    | mapping k v => simp [MObj.hasTyH] at hrow
          · simp only [copyMToSt, hmem, dif_neg, not_false_iff] at hcopy
            exact nomatch hcopy
termination_by rem.length
decreasing_by all_goals
  (have h1 := List.length_erase_of_mem hmem
   have h2 := List.length_pos_of_mem hmem
   omega)

/-- `copyMem` at the interpreter's own visited set. -/
theorem copyMem_hasTy {H : HeapTy} {s : State} {mv : MVal} {ty : Ty}
    {sv : SVal} (hheap : heapTypedB H s.heap = true)
    (h : MVal.hasTyH H mv ty = true)
    (hcopy : copyMem s mv = Except.ok sv) : sv.hasTy ty = true :=
  copyMToSt_hasTy hheap h hcopy

/-! ## Storage→memory copy typing -/

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

/-- The allocation step shared by `copyStToM_typed`'s node arms: claim
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

mutual

/-- Storage→memory copy typing: copying a `ty`-typed storage value
allocates fresh objects, extending the store typing so that the
returned slot value has type `ty` and everything already typed stays
typed. -/
theorem copyStToM_typed {H : HeapTy} {s s' : State} {v : SVal}
    {ty : Ty} {mv : MVal}
    (hnd : nodupKeysB H = true) (hheap : heapTypedB H s.heap = true)
    (hwf : HeapWellFormed s) (hty : v.hasTy ty = true)
    (hcopy : copyStToM s v = Except.ok (s', mv)) :
    ∃ H', CopyOut H s H' s' ∧ MVal.hasTyH H' mv ty = true := by
  cases v with
  | prim p =>
      cases p with
      | int n =>
          simp only [copyStToM] at hcopy
          try dsimp only at hcopy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hcopy
          obtain ⟨hs, hmv⟩ := hcopy
          subst hs hmv
          refine ⟨H, CopyOut.refl hnd hheap hwf, ?_⟩
          cases ty with
          | prim pt => cases pt <;> simp_all [SVal.hasTy, MVal.hasTyH]
          | ref r => simp [SVal.hasTy] at hty
      | bool b =>
          simp only [copyStToM] at hcopy
          try dsimp only at hcopy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hcopy
          obtain ⟨hs, hmv⟩ := hcopy
          subst hs hmv
          refine ⟨H, CopyOut.refl hnd hheap hwf, ?_⟩
          cases ty with
          | prim pt => cases pt <;> simp_all [SVal.hasTy, MVal.hasTyH]
          | ref r => simp [SVal.hasTy] at hty
  | struct fields =>
      cases ty with
      | prim pt => simp [SVal.hasTy] at hty
      | ref r =>
          cases r with
          | struct str =>
              simp only [SVal.hasTy] at hty
              simp only [copyStToM, bind, Except.bind] at hcopy
              cases hfs : copyStFields s fields with
              | error e => rw [hfs] at hcopy; exact nomatch hcopy
              | ok out =>
                  obtain ⟨s₁, mfields⟩ := out
                  rw [hfs] at hcopy
                  try dsimp only at hcopy
                  obtain ⟨H₁, hout, hflds⟩ :=
                    copyStFields_typed hnd hheap hwf hty hfs
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hcopy
                  obtain ⟨hs', hmv⟩ := hcopy
                  subst hs' hmv
                  have halloc := CopyOut.alloc
                    (r := RefTy.struct str) (obj := MObj.struct mfields)
                    hout (by simpa [MObj.hasTyH] using hflds)
                  exact ⟨_, halloc.1, halloc.2⟩
          | array elem => simp [SVal.hasTy] at hty
          | mapping k value => simp [SVal.hasTy] at hty
  | array elems =>
      cases ty with
      | prim pt => simp [SVal.hasTy] at hty
      | ref r =>
          cases r with
          | struct str => simp [SVal.hasTy] at hty
          | array elem =>
              simp only [SVal.hasTy] at hty
              simp only [copyStToM, bind, Except.bind] at hcopy
              cases hes : copyStElems s elems with
              | error e => rw [hes] at hcopy; exact nomatch hcopy
              | ok out =>
                  obtain ⟨s₁, melems⟩ := out
                  rw [hes] at hcopy
                  try dsimp only at hcopy
                  obtain ⟨H₁, hout, hels⟩ :=
                    copyStElems_typed hnd hheap hwf
                      (by simpa using (Bool.and_eq_true _ _ ▸ hty : _ ∧ _).1) hes
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hcopy
                  obtain ⟨hs', hmv⟩ := hcopy
                  subst hs' hmv
                  have halloc := CopyOut.alloc
                    (r := RefTy.array elem) (obj := MObj.array melems)
                    hout (by simpa [MObj.hasTyH] using hels)
                  exact ⟨_, halloc.1, halloc.2⟩
          | mapping k value => simp [SVal.hasTy] at hty
  | map entries dflt => exact nomatch hcopy

theorem copyStFields_typed {H : HeapTy} {s s₁ : State} {str : Name}
    {fields : List (Name × SVal)} {mfields : List (Name × MVal)}
    (hnd : nodupKeysB H = true) (hheap : heapTypedB H s.heap = true)
    (hwf : HeapWellFormed s)
    (hty : SVal.hasTy.hasTyFields str fields = true)
    (hcopy : copyStFields s fields = Except.ok (s₁, mfields)) :
    ∃ H₁, CopyOut H s H₁ s₁ ∧
      MObj.hasTyH.hasTyHFields H₁ str mfields = true := by
  match fields with
  | [] =>
      simp only [copyStFields] at hcopy
      try dsimp only at hcopy
      simp only [Except.ok.injEq, Prod.mk.injEq] at hcopy
      obtain ⟨hs, hmf⟩ := hcopy
      subst hs hmf
      exact ⟨H, CopyOut.refl hnd hheap hwf, rfl⟩
  | (n, v) :: rest =>
      simp only [SVal.hasTy.hasTyFields, Bool.and_eq_true] at hty
      simp only [copyStFields, bind, Except.bind] at hcopy
      cases hdef : lookupBy n (structDef str) with
      | none => rw [hdef] at hty; exact Bool.noConfusion hty.1
      | some tyf =>
          rw [hdef] at hty
          cases hv : copyStToM s v with
          | error e => rw [hv] at hcopy; exact nomatch hcopy
          | ok out =>
              obtain ⟨s₂, mv⟩ := out
              rw [hv] at hcopy
              try dsimp only at hcopy
              obtain ⟨H₂, hout₂, hmv⟩ :=
                copyStToM_typed hnd hheap hwf hty.1 hv
              cases hrest : copyStFields s₂ rest with
              | error e => rw [hrest] at hcopy; exact nomatch hcopy
              | ok outr =>
                  obtain ⟨s₃, mrest⟩ := outr
                  rw [hrest] at hcopy
                  try dsimp only at hcopy
                  obtain ⟨H₃, hout₃, hmrest⟩ :=
                    copyStFields_typed hout₂.nodup hout₂.heap
                      hout₂.heapWf hty.2 hrest
                  try dsimp only at hcopy
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hcopy
                  obtain ⟨hs₁, hmf⟩ := hcopy
                  subst hs₁ hmf
                  refine ⟨H₃, hout₂.trans hout₃, ?_⟩
                  simp only [MObj.hasTyH.hasTyHFields, hdef,
                    Bool.and_eq_true]
                  exact ⟨MVal.hasTyH_mono hout₃.ext hmv, hmrest⟩

theorem copyStElems_typed {H : HeapTy} {s s₁ : State} {elem : Ty}
    {elems : List SVal} {melems : List MVal}
    (hnd : nodupKeysB H = true) (hheap : heapTypedB H s.heap = true)
    (hwf : HeapWellFormed s)
    (hty : SVal.hasTy.hasTyElems elem elems = true)
    (hcopy : copyStElems s elems = Except.ok (s₁, melems)) :
    ∃ H₁, CopyOut H s H₁ s₁ ∧
      MObj.hasTyH.hasTyHElems H₁ elem melems = true := by
  match elems with
  | [] =>
      simp only [copyStElems] at hcopy
      try dsimp only at hcopy
      simp only [Except.ok.injEq, Prod.mk.injEq] at hcopy
      obtain ⟨hs, hme⟩ := hcopy
      subst hs hme
      exact ⟨H, CopyOut.refl hnd hheap hwf, rfl⟩
  | v :: rest =>
      simp only [SVal.hasTy.hasTyElems, Bool.and_eq_true] at hty
      simp only [copyStElems, bind, Except.bind] at hcopy
      cases hv : copyStToM s v with
      | error e => rw [hv] at hcopy; exact nomatch hcopy
      | ok out =>
          obtain ⟨s₂, mv⟩ := out
          rw [hv] at hcopy
          try dsimp only at hcopy
          obtain ⟨H₂, hout₂, hmv⟩ :=
            copyStToM_typed hnd hheap hwf hty.1 hv
          cases hrest : copyStElems s₂ rest with
          | error e => rw [hrest] at hcopy; exact nomatch hcopy
          | ok outr =>
              obtain ⟨s₃, mrest⟩ := outr
              rw [hrest] at hcopy
              try dsimp only at hcopy
              obtain ⟨H₃, hout₃, hmrest⟩ :=
                copyStElems_typed hout₂.nodup hout₂.heap
                  hout₂.heapWf hty.2 hrest
              try dsimp only at hcopy
              simp only [Except.ok.injEq, Prod.mk.injEq] at hcopy
              obtain ⟨hs₁, hme⟩ := hcopy
              subst hs₁ hme
              refine ⟨H₃, hout₂.trans hout₃, ?_⟩
              simp only [MObj.hasTyH.hasTyHElems, Bool.and_eq_true]
              exact ⟨MVal.hasTyH_mono hout₃.ext hmv, hmrest⟩

end

/-- Fresh default memory allocation is typed: the identity
`allocDefault` returns is claimed at the declared reference type. -/
theorem allocDefault_typed {H : HeapTy} {s s' : State} {ref : RefTy}
    {id : Nat}
    (hnd : nodupKeysB H = true) (hheap : heapTypedB H s.heap = true)
    (hwf : HeapWellFormed s) (hok : defaultOk (Ty.ref ref) = true)
    (halloc : allocDefault s ref = Except.ok (s', id)) :
    ∃ H', CopyOut H s H' s' ∧
      MVal.hasTyH H' (MVal.ref id) (Ty.ref ref) = true := by
  simp only [allocDefault] at halloc
  cases hcopy : copyStToM s (defaultForRef ref) with
  | error e => rw [hcopy] at halloc; exact nomatch halloc
  | ok out =>
      obtain ⟨s₁, mv⟩ := out
      rw [hcopy] at halloc
      have hdefault : (defaultForRef ref).hasTy (Ty.ref ref) = true :=
        defaultForTy_hasTy hok
      obtain ⟨H', hout, hmv⟩ :=
        copyStToM_typed hnd hheap hwf hdefault hcopy
      cases mv with
      | prim p => exact nomatch halloc
      | ref rid =>
          try dsimp only at halloc
          simp only [Except.ok.injEq, Prod.mk.injEq] at halloc
          obtain ⟨hs', hid⟩ := halloc
          subst hs' hid
          exact ⟨H', hout, hmv⟩

end Semantics
end Solidity
