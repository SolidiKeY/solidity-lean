import Solidity.Backend.StorageOps.RecursiveClear
import Solidity.Backend.StorageOps.Lifecycle

/-! Operation-side pop changes the header and recursively clears precisely the
former last live slot. No semantic pop/clear is invoked by the implementation. -/
namespace Solidity.Backend.StorageOps
open TypeGraph

def recursivePop {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) : Option (Value G (.array E)) :=
  if h : 0 < old.length.val then
    some (.array old.extent ⟨old.length.val - 1, by have hl := old.length.isLt; omega⟩
      (by change old.length.val - 1 ≤ old.extent.val; have bound := array_live_bound old; omega)
      (fun i => if i.val = old.length.val - 1 then recursiveClearSlot (old.slots i) else old.slots i))
  else none

theorem recursivePop_eq_pop {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) : recursivePop old = old.pop := by
  cases old
  simp only [recursivePop, Value.pop, Value.extent, Value.length, Value.slots, recursiveClearSlot_eq_clear]

theorem recursivePop_failure {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) : recursivePop old = none ↔ old.length.val = 0 := by
  rw [recursivePop_eq_pop]
  exact pop_fails_iff old

theorem recursivePop_header {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (popped : recursivePop old = some result) :
    result.length.val + 1 = old.length.val ∧ result.extent = old.extent := by
  rw [recursivePop_eq_pop] at popped
  exact old.pop_length result popped

/-- Every other retained index has exactly its original logical read. -/
theorem recursivePop_other {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (popped : recursivePop old = some result)
    (i : Index) (other : i.val ≠ old.length.val - 1) :
    TypeGraph.Step.get Value.dflt (.index i) result = TypeGraph.Step.get Value.dflt (.index i) old := by
  cases old with
  | array extent length bound slots =>
    change i.val ≠ length.val - 1 at other
    simp only [recursivePop, Value.length, Value.extent, Value.slots] at popped
    split at popped
    · cases popped
      simp only [TypeGraph.Step.get]
      split
      · rfl
      · rfl
    · cases popped

/-- info: 'Solidity.Backend.StorageOps.recursivePop_eq_pop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursivePop_eq_pop
/-- info: 'Solidity.Backend.StorageOps.recursivePop_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms recursivePop_failure
/-- info: 'Solidity.Backend.StorageOps.recursivePop_header' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursivePop_header
/-- info: 'Solidity.Backend.StorageOps.recursivePop_other' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursivePop_other
end Solidity.Backend.StorageOps
