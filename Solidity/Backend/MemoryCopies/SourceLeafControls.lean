import Solidity.Backend.MemoryCopies.SourceLeafArrays
import Solidity.Backend.Aggregates.G18ArrayAccessControls

/-! Empty/long Source reference-element arrays on populated state. -/
namespace Solidity.Backend.MemoryCopies.SourceLeafControls
private abbrev E := Backend.Aggregates.SourceArray.Controls.E
private def before : Source.EMState E [.bool] :=
  (Backend.Aggregates.SourceArray.Controls.locals,
    Backend.Aggregates.SourceArray.Controls.state Backend.Aggregates.SourceArray.Controls.live)
private def observe {τ : Source.STy}
    (result : Source.R (Source.Val E.layout τ) × Source.EMState E [.bool]) : Option (Nat × Nat) :=
  match result.1 with
  | .ok (.memRef _ root) => some (root,result.2.2.heap.next)
  | _ => none

/-- Observations come from the actual complete Source certificate, not from
an assumed root or separately executed allocation model. -/
theorem actual_observation {τ : Source.STy} {memory : τ.loc? = some .memory}
    (leaf : SourceLeafDefault E τ memory) (count slack : Nat) :
    observe ((Source.zeroVal (E := E) (Γ := [.bool]) (count + 4 + slack)
      (.array .memory τ (some count))).run before) = some (1 + count,1 + count + 1) := by
  obtain ⟨values,after,certificate,frontier,_⟩ := leaf.fixed count slack before
  rw [certificate.execution]
  change some (after.2.heap.next,after.2.heap.next + 1) = _
  rw [frontier]
  rfl

theorem empty_bytes_array :
    observe ((Source.zeroVal (E := E) (Γ := [.bool]) 4
      (.array .memory (.bytes .memory) (some 0))).run before) = some (1,2) :=
  actual_observation (bytesLeaf E) 0 0

theorem long_bytes_array :
    observe ((Source.zeroVal (E := E) (Γ := [.bool]) 68
      (.array .memory (.bytes .memory) (some 64))).run before) = some (65,66) :=
  actual_observation (bytesLeaf E) 64 0

theorem string_children :
    observe ((Source.zeroVal (E := E) (Γ := [.bool]) 6
      (.array .memory (.string .memory) (some 2))).run before) = some (3,4) :=
  actual_observation (stringLeaf E) 2 0

/-- Reference-valued dynamic children may themselves have reference elements. -/
theorem nested_dynamic_children :
    observe ((Source.zeroVal (E := E) (Γ := [.bool]) 6
      (.array .memory (.array .memory (.bytes .memory) none) (some 2))).run before) = some (3,4) :=
  actual_observation (dynamicLeaf E (.bytes .memory)) 2 0

/-- Insufficient horizon is timeout after a real child allocation, not Panic41
or rollback to the input. This is not an out-of-gas equivalence claim. -/
theorem partial_timeout :
    let result := (Source.zeroVal (E := E) (Γ := [.bool]) 5
      (.array .memory (.bytes .memory) (some 2))).run before
    result.1 = .error .timeout ∧ result.2.2.heap.next = 2 ∧
      result.2.2.heap.get 0 = before.2.heap.get 0 := ⟨rfl,rfl,rfl⟩

theorem wrong_parent_rejected :
    observe ((Source.zeroVal (E := E) (Γ := [.bool]) 68
      (.array .memory (.bytes .memory) (some 64))).run before) ≠ some (64,65) := by
  rw [long_bytes_array]
  decide

#print axioms actual_observation
#print axioms empty_bytes_array
#print axioms long_bytes_array
#print axioms string_children
#print axioms nested_dynamic_children
#print axioms partial_timeout
#print axioms wrong_parent_rejected
end Solidity.Backend.MemoryCopies.SourceLeafControls
