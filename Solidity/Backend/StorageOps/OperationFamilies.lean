import Solidity.Backend.StorageOps.Commutation

/-!
Partial operation families over the existing intrinsic keyed slots. Each
operation reads only its own defaulted value and immutable captured parameters.
The scheduler reuses `Slots.write`, and returns no result if any step fails.
These are intrinsic operation laws, not a new store or transaction semantics.
-/

namespace Solidity.Backend.StorageOps

open TypeGraph

/-- Apply one partial value operation at a typed keyed slot. Captured source
snapshots are fixed arguments to the value operation, not ambient mutable reads. -/
def modifySlot {K : Type} [DecidableEq K] {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (slots : K → Slot G E) (key : K) (effect : Value G E → Option (Value G E)) :
    Option (K → Slot G E) :=
  (effect ((slots key).getD (Value.dflt E))).map (Slots.write slots key)

/-- Distinct-key partial operations commute, including either/both failure
orders. No success premise or old-allocation/liveness premise is needed. -/
theorem modifySlot_commute {K : Type} [DecidableEq K] {n : Nat} {G : Schema n}
    {E : TypeGraph.Ty n} (slots : K → Slot G E) (a b : K) (different : a ≠ b)
    (f g : Value G E → Option (Value G E)) :
    (modifySlot slots a f).bind (fun next => modifySlot next b g) =
      (modifySlot slots b g).bind (fun next => modifySlot next a f) := by
  cases first : f ((slots a).getD (Value.dflt E)) with
  | none =>
    cases second : g ((slots b).getD (Value.dflt E)) <;>
      simp only [modifySlot, first, second, Option.map_none, Option.map_some,
        Option.bind_none, Option.bind_some,
        Slots.write_other slots b a different]
  | some x =>
    cases second : g ((slots b).getD (Value.dflt E)) with
    | none =>
      simp only [modifySlot, first, second, Option.map_none, Option.map_some,
        Option.bind_none, Option.bind_some,
        Slots.write_other slots a b (Ne.symm different)]
    | some y =>
      simp only [modifySlot, first, second, Option.map_some, Option.bind_some,
        Slots.write_other slots a b (Ne.symm different),
        Slots.write_other slots b a different]
      exact congrArg some (writes_commute slots a b different x y)

/-- Apply an existing value operation through an existing typed graph path.
Failure returns no modified root; no world-level rollback claim is made. -/
def modifyAt {n : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    (root : Value G A) (path : TypeGraph.Path G A E)
    (effect : Value G E → Option (Value G E)) : Option (Value G A) := do
  let old ← root.find path
  let result ← effect old
  root.save path result

/-- The keyed scheduler is exactly the existing find/effect/save sequence for
mapping paths, including implicit-default reads and failing effects. -/
theorem modifyAt_mapping {n : Nat} {G : Schema n} {K : PrimTy} {E : TypeGraph.Ty n}
    (slots : K.Denote → Slot G E) (key : K.Denote)
    (effect : Value G E → Option (Value G E)) :
    modifyAt (.mapping slots) (.cons (.key key) .nil) effect =
      (modifySlot slots key effect).map Value.mapping := by
  simp only [modifyAt, modifySlot, Value.find, Value.save, TypeGraph.Path.read,
    TypeGraph.Path.save, TypeGraph.Step.get, TypeGraph.Step.put, Option.bind_eq_bind, Option.bind_some]
  cases effect ((slots key).getD (Value.dflt E)) <;> rfl

/-- Lift two distinct-key operations to actual graph path updates. Both paths
may address retained nested aggregate values; the operation itself decides
whether a push/pop or other value update succeeds. -/
theorem modifyAt_mapping_commute {n : Nat} {G : Schema n} {K : PrimTy}
    {E : TypeGraph.Ty n} (slots : K.Denote → Slot G E) (a b : K.Denote)
    (different : a ≠ b) (f g : Value G E → Option (Value G E)) :
    (modifyAt (.mapping slots) (.cons (.key a) .nil) f).bind
      (fun root => modifyAt root (.cons (.key b) .nil) g) =
    (modifyAt (.mapping slots) (.cons (.key b) .nil) g).bind
      (fun root => modifyAt root (.cons (.key a) .nil) f) := by
  simp only [modifyAt_mapping, Option.bind_map]
  have commute := modifySlot_commute slots a b different f g
  have transported := congrArg (Option.map Value.mapping) commute
  simpa only [Option.map_bind, Function.comp_def, modifyAt_mapping] using transported

/-- A finite operation-generated key sequence, with no fixed admission cap.
Repeated keys inside a family are retained and execute repeatedly. -/
def modifyMany {K : Type} [DecidableEq K] {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (effect : K → Value G E → Option (Value G E)) :
    List K → (K → Slot G E) → Option (K → Slot G E)
  | [], slots => some slots
  | key :: keys, slots => (modifySlot slots key (effect key)).bind (modifyMany effect keys)

/-- Concatenation executes the original partial scheduler through its actual
intermediate slots; keys are neither reordered nor deduplicated. -/
theorem modifyMany_append {K : Type} [DecidableEq K] {n : Nat} {G : Schema n}
    {E : TypeGraph.Ty n} (effect : K → Value G E → Option (Value G E))
    (left right : List K) (slots : K → Slot G E) :
    modifyMany effect (left ++ right) slots =
      (modifyMany effect left slots).bind (modifyMany effect right) := by
  induction left generalizing slots with
  | nil => rfl
  | cons key keys ih =>
    change (modifySlot slots key (effect key)).bind (modifyMany effect (keys ++ right)) =
      ((modifySlot slots key (effect key)).bind (modifyMany effect keys)).bind
        (modifyMany effect right)
    cases step : modifySlot slots key (effect key) with
    | none => rfl
    | some next => exact ih next

/-- info: 'Solidity.Backend.StorageOps.modifyMany_append' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms modifyMany_append

/-- One partial operation commutes with an entire family that never addresses
its key. Internal repetitions and failures of the other family are allowed. -/
theorem modifySlot_many_commute {K : Type} [DecidableEq K] {n : Nat} {G : Schema n}
    {E : TypeGraph.Ty n} (slots : K → Slot G E) (key : K)
    (f : Value G E → Option (Value G E)) (keys : List K)
    (effect : K → Value G E → Option (Value G E)) (outside : key ∉ keys) :
    (modifySlot slots key f).bind (modifyMany effect keys) =
      (modifyMany effect keys slots).bind (fun next => modifySlot next key f) := by
  induction keys generalizing slots with
  | nil =>
    simp only [modifyMany, Option.bind_some]
    cases modifySlot slots key f <;> rfl
  | cons head tail ih =>
    have different : key ≠ head := fun equal => outside (equal ▸ List.mem_cons_self)
    have rest : key ∉ tail := fun member => outside (List.mem_cons_of_mem _ member)
    change (modifySlot slots key f).bind
        (fun next => (modifySlot next head (effect head)).bind (modifyMany effect tail)) =
      ((modifySlot slots head (effect head)).bind (modifyMany effect tail)).bind
        (fun next => modifySlot next key f)
    rw [← Option.bind_assoc, modifySlot_commute slots key head different f (effect head)]
    simp only [Option.bind_assoc]
    congr 1
    funext next
    exact ih next rest

/-- Disjoint finite partial operation families commute. This proves matching
failure as well as success, rather than assuming both executions succeed. -/
theorem modifyMany_commute {K : Type} [DecidableEq K] {n : Nat} {G : Schema n}
    {E : TypeGraph.Ty n} (slots : K → Slot G E) (left right : List K)
    (f g : K → Value G E → Option (Value G E))
    (separate : ∀ a ∈ left, ∀ b ∈ right, a ≠ b) :
    (modifyMany f left slots).bind (modifyMany g right) =
      (modifyMany g right slots).bind (modifyMany f left) := by
  induction left generalizing slots with
  | nil =>
    simp only [modifyMany, Option.bind_some]
    cases modifyMany g right slots <;> rfl
  | cons head tail ih =>
    have outside : head ∉ right := fun member =>
      separate head List.mem_cons_self head member rfl
    have rest : ∀ a ∈ tail, ∀ b ∈ right, a ≠ b :=
      fun a ha b hb => separate a (List.mem_cons_of_mem _ ha) b hb
    change ((modifySlot slots head (f head)).bind (modifyMany f tail)).bind
        (modifyMany g right) =
      (modifyMany g right slots).bind
        (fun next => (modifySlot next head (f head)).bind (modifyMany f tail))
    calc
      _ = (modifySlot slots head (f head)).bind (fun next =>
          (modifyMany g right next).bind (modifyMany f tail)) := by
            simp only [Option.bind_assoc]
            congr 1
            funext next
            exact ih next rest
      _ = ((modifySlot slots head (f head)).bind (modifyMany g right)).bind
          (modifyMany f tail) := (Option.bind_assoc _ _ _).symm
      _ = ((modifyMany g right slots).bind
          (fun next => modifySlot next head (f head))).bind (modifyMany f tail) :=
        congrArg (fun result => result.bind (modifyMany f tail))
          (modifySlot_many_commute slots head (f head) right g outside)
      _ = _ := Option.bind_assoc _ _ _

/-- The generated key list is a finite footprint even when it contains repeated
accesses. A successful family leaves every key outside it exactly unchanged. -/
theorem modifyMany_outside {K : Type} [DecidableEq K] {n : Nat} {G : Schema n}
    {E : TypeGraph.Ty n} (effect : K → Value G E → Option (Value G E))
    (keys : List K) (slots result : K → Slot G E) (key : K)
    (outside : key ∉ keys) (performed : modifyMany effect keys slots = some result) :
    result key = slots key := by
  induction keys generalizing slots with
  | nil => cases performed; rfl
  | cons head tail ih =>
    have different : key ≠ head := fun equal => outside (equal ▸ List.mem_cons_self)
    have rest : key ∉ tail := fun member => outside (List.mem_cons_of_mem _ member)
    simp only [modifyMany, modifySlot] at performed
    cases step : effect head ((slots head).getD (Value.dflt E)) with
    | none => simp only [step, Option.map_none, Option.bind_none] at performed; cases performed
    | some value =>
      simp only [step, Option.map_some, Option.bind_some] at performed
      exact (ih (Slots.write slots head value) rest performed).trans
        (Slots.write_other slots head key different value)

end Solidity.Backend.StorageOps
