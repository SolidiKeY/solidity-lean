import Solidity.Backend.StorageOps.Lifecycle

/-! Independent operation-side default push. The existing type-directed scalar
reset / aggregate retained-slot reuse and word capacity check are preserved.
No semantic push or new default/representation layer is used by the algorithm. -/
namespace Solidity.Backend.StorageOps
open TypeGraph

def operationPush {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) : Option (Value G (.array E)) :=
  if room : old.length.val + 1 < 2 ^ 256 then
    let extent : Extent := ⟨max old.extent.val (old.length.val + 1), by
      have bound := old.extent.isLt
      omega⟩
    some (.array extent ⟨old.length.val + 1, room⟩ (Nat.le_max_right _ _)
      (fun i => if E.isPrimitive = true ∧ i.val = old.length.val then .absent
        else if hi : i.val < old.extent.val then old.slots ⟨i.val, hi⟩ else .absent))
  else none

theorem operationPush_eq_push {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) : operationPush old = old.push := by
  cases old
  rfl

theorem operationPush_failure {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) : operationPush old = none ↔ 2 ^ 256 ≤ old.length.val + 1 := by
  rw [operationPush_eq_push]
  exact push_fails_iff old

theorem operationPush_header {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (pushed : operationPush old = some result) :
    result.length.val = old.length.val + 1 ∧ result.extent.val = max old.extent.val (old.length.val + 1) := by
  unfold operationPush at pushed
  split at pushed
  · cases pushed
    exact ⟨rfl, rfl⟩
  · cases pushed

theorem operationPush_keeps {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (pushed : operationPush old = some result)
    (i : Index) (preserve : E.isPrimitive = false ∨ i.val ≠ old.length.val)
    (allocated : i.val < old.extent.val) :
    TypeGraph.Step.get Value.dflt (.index i) result = TypeGraph.Step.get Value.dflt (.index i) old := by
  rw [operationPush_eq_push] at pushed
  exact old.push_keeps_slot Value.dflt result i preserve allocated pushed

/-- Fresh slots read the published default, rather than a new allocation model. -/
theorem operationPush_fresh {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (fresh : old.extent.val = old.length.val)
    (pushed : operationPush old = some result) :
    TypeGraph.Step.get Value.dflt (.index old.length) result = some (Value.dflt E) := by
  rw [operationPush_eq_push] at pushed
  exact push_fresh_default old result fresh pushed

/-- Primitive slots reset even when the new live index was already retained. -/
theorem operationPush_reset {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (primitive : E.isPrimitive = true)
    (pushed : operationPush old = some result) :
    TypeGraph.Step.get Value.dflt (.index old.length) result = some (Value.dflt E) := by
  cases old with
  | array extent length bound slots =>
    simp only [operationPush, Value.extent, Value.length, Value.slots] at pushed
    split at pushed
    · cases pushed
      have inside : length.val < max extent.val (length.val + 1) := by omega
      simp only [Value.length, TypeGraph.Step.get, dif_pos inside, primitive, true_and, if_true, Slot.getD]
    · cases pushed

/-- info: 'Solidity.Backend.StorageOps.operationPush_eq_push' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms operationPush_eq_push
/-- info: 'Solidity.Backend.StorageOps.operationPush_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms operationPush_failure
/-- info: 'Solidity.Backend.StorageOps.operationPush_header' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms operationPush_header
/-- info: 'Solidity.Backend.StorageOps.operationPush_keeps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms operationPush_keeps
/-- info: 'Solidity.Backend.StorageOps.operationPush_fresh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms operationPush_fresh

/-- info: 'Solidity.Backend.StorageOps.operationPush_reset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms operationPush_reset
end Solidity.Backend.StorageOps
