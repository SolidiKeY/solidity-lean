import Solidity.Backend.StorageOps.MappingPaths

/-! Independent operation-side recursive clear. Generalized-index recursors
preserve G0; fields/slots retain the published demand-driven graph model.
Every demanded dynamic array uses the runtime prefix loop, not semantic clear. -/
namespace Solidity.Backend.StorageOps
open TypeGraph

mutual
/-- Total constructor recursion with runtime-length array clearing. -/
def recursiveClear {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (value : Value G T) : Value G T :=
  Value.casesOn (motive_1 := fun T _ => Value G T) value
    (fun {p} _ => .prim p.dflt)
    (fun fields => .node (fun p => recursiveClear (fields p)))
    (fun extent length _ slots => .array extent ⟨0, by decide⟩ (Nat.zero_le _)
      (visit (fun i => recursiveClearSlot (slots i)) length.val slots))
    (fun slots => .fixed (fun i => recursiveClearSlot (slots i)))
    (fun slots => .mapping slots)

/-- Absent slots stay absent; present values recurse without synthesizing data. -/
def recursiveClearSlot {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (slot : Slot G T) : Slot G T :=
  Slot.casesOn (motive_2 := fun T _ => Slot G T) slot
    .absent (fun value => .present (recursiveClear value))
end

mutual
/-- Correspondence to the unchanged independent clear specification. -/
theorem recursiveClear_eq_clear {n : Nat} {G : Schema n} :
    {T : TypeGraph.Ty n} → (value : Value G T) → recursiveClear value = value.clear
  | _, .prim _ => rfl
  | _, .node fields => by
    apply congrArg Value.node
    funext T p
    exact recursiveClear_eq_clear (fields p)
  | _, .array extent length bound slots => by
    unfold recursiveClear Value.clear
    dsimp only
    congr 1
    funext i
    rw [visit_prefix]
    by_cases live : i.val < length.val
    · simp only [if_pos live]
      exact recursiveClearSlot_eq_clear (slots i)
    · simp only [if_neg live]
  | _, .fixed slots => by
    apply congrArg Value.fixed
    funext i
    exact recursiveClearSlot_eq_clear (slots i)
  | _, .mapping _ => rfl

theorem recursiveClearSlot_eq_clear {n : Nat} {G : Schema n} :
    {T : TypeGraph.Ty n} → (slot : Slot G T) → recursiveClearSlot slot = slot.clear
  | _, .absent => rfl
  | _, .present value => congrArg Slot.present (recursiveClear_eq_clear value)
end

/-- Concrete partial execution of precisely the array clear loop. -/
def clearArrayPrefix {n extent : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (slots : Fin extent → Slot G E) (count : Nat) : Fin extent → Slot G E :=
  visit (fun i => recursiveClearSlot (slots i)) count slots

theorem clearArrayPrefix_progress {n extent : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (slots : Fin extent → Slot G E) (count : Nat) (i : Fin extent) :
    clearArrayPrefix slots count i = if i.val < count then recursiveClearSlot (slots i) else slots i :=
  visit_prefix _ _ _ _

theorem clearArrayPrefix_complete {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (extent : Extent) (length : Index) (bound : length.val ≤ extent.val)
    (slots : Fin extent.val → Slot G E) :
    (recursiveClear (.array extent length bound slots)).slots = clearArrayPrefix slots length.val := rfl

theorem clearArrayPrefix_unvisited {n extent : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (slots : Fin extent → Slot G E) (count : Nat) (i : Fin extent) (outside : count ≤ i.val) :
    clearArrayPrefix slots count i = slots i := visit_frame _ _ _ _ outside

theorem clearArrayPrefix_restart {n extent : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (slots : Fin extent → Slot G E) (first second : Nat) :
    visit (fun i => recursiveClearSlot (slots i)) second (clearArrayPrefix slots first) =
      clearArrayPrefix slots (max first second) := visit_restart _ _ _ _

theorem recursiveClear_tail {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (extent : Extent) (length : Index) (bound : length.val ≤ extent.val)
    (slots : Fin extent.val → Slot G E) (i : Fin extent.val) (shadow : length.val ≤ i.val) :
    (recursiveClear (.array extent length bound slots)).slots i = slots i := by
  simp only [recursiveClear, Value.slots, visit_prefix, if_neg (Nat.not_lt_of_ge shadow)]

theorem recursiveClear_mapping {n : Nat} {G : Schema n} {K : PrimTy} {V : TypeGraph.Ty n}
    (slots : K.Denote → Slot G V) : recursiveClear (.mapping slots) = Value.mapping slots := rfl

theorem recursiveClear_header {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) : (recursiveClear old).length.val = 0 ∧ (recursiveClear old).extent = old.extent := by
  cases old
  exact ⟨rfl, rfl⟩

/-- info: 'Solidity.Backend.StorageOps.recursiveClear_header' does not depend on any axioms -/
#guard_msgs in #print axioms recursiveClear_header

/-- Every retained mapping read is preserved, even below cleared live slots. -/
theorem recursiveClear_mapping_read {n : Nat} {G : Schema n} {A : TypeGraph.Ty n}
    {K : PrimTy} {V : TypeGraph.Ty n} (old : Value G A)
    (path : TypeGraph.Path G A (.mapping K V)) : (recursiveClear old).find path = old.find path := by
  rw [recursiveClear_eq_clear]
  exact clear_mapping_read old path

theorem recursiveClear_idem {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old : Value G T) : recursiveClear (recursiveClear old) = recursiveClear old := by
  simp only [recursiveClear_eq_clear, Value.clear_idem]

/-- info: 'Solidity.Backend.StorageOps.recursiveClear_eq_clear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursiveClear_eq_clear
/-- info: 'Solidity.Backend.StorageOps.recursiveClearSlot_eq_clear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursiveClearSlot_eq_clear
/-- info: 'Solidity.Backend.StorageOps.clearArrayPrefix_complete' does not depend on any axioms -/
#guard_msgs in #print axioms clearArrayPrefix_complete
/-- info: 'Solidity.Backend.StorageOps.clearArrayPrefix_progress' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms clearArrayPrefix_progress
/-- info: 'Solidity.Backend.StorageOps.clearArrayPrefix_unvisited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms clearArrayPrefix_unvisited
/-- info: 'Solidity.Backend.StorageOps.clearArrayPrefix_restart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms clearArrayPrefix_restart
/-- info: 'Solidity.Backend.StorageOps.recursiveClear_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursiveClear_tail
/-- info: 'Solidity.Backend.StorageOps.recursiveClear_mapping' does not depend on any axioms -/
#guard_msgs in #print axioms recursiveClear_mapping
/-- info: 'Solidity.Backend.StorageOps.recursiveClear_mapping_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursiveClear_mapping_read
/-- info: 'Solidity.Backend.StorageOps.recursiveClear_idem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursiveClear_idem
end Solidity.Backend.StorageOps
