import Solidity.Backend.MemoryCopies.SourceConstruction
import Solidity.Backend.Aggregates.G18ArrayAccessControls

/-! Nested Source default constructors on a genuinely populated input. -/
namespace Solidity.Backend.MemoryCopies.SourceConstructionControls
private abbrev E := Backend.Aggregates.SourceArray.Controls.E
private def before : Source.EMState E [.bool] :=
  (Backend.Aggregates.SourceArray.Controls.locals,
    Backend.Aggregates.SourceArray.Controls.state Backend.Aggregates.SourceArray.Controls.live)
private def observe {τ : Source.STy}
    (result : Source.R (Source.Val E.layout τ) × Source.EMState E [.bool]) : Option (Nat × Nat) :=
  match result.1 with
  | .ok (.memRef _ root) => some (root,result.2.2.heap.next)
  | _ => none
private def nestedBytes : SourceConstructionCertificate E
    (.array .memory (.array .memory (.bytes .memory) (some 3)) (some 2)) rfl := ((bytesLeaf E).construction.fixed 3).fixed 2
private def longStrings : SourceConstructionCertificate E
    (.array .memory (.array .memory (.string .memory) (some 64)) (some 1)) rfl := ((stringLeaf E).construction.fixed 64).fixed 1
private def emptyOuter : SourceConstructionCertificate E
    (.array .memory (.array .memory (.bytes .memory) (some 64)) (some 0)) rfl := ((bytesLeaf E).construction.fixed 64).fixed 0
private def nestedDynamic : SourceConstructionCertificate E
    (.array .memory (.array .memory (.array .memory (.bytes .memory) none) (some 3)) (some 2)) rfl := ((dynamicLeaf E (.bytes .memory)).construction.fixed 3).fixed 2

/-- A constructor gives actual root/frontier observations at every slack, not
an assumed successful run or an evaluation of a replacement interpreter. -/
theorem actual_observation {τ : Source.STy} {memory : τ.loc? = some .memory}
    (constructor : SourceConstructionCertificate E τ memory) (slack : Nat) :
    observe ((Source.zeroVal (E := E) (Γ := [.bool]) (constructor.horizon + slack) τ).run before) =
      some (constructor.objects,1 + constructor.objects) := by
  obtain ⟨after,root,data,certificate,frontier,last⟩ := constructor.execution before slack
  rw [certificate.execution]
  change some (root,after.2.heap.next) = _
  change after.2.heap.next = 1 + constructor.objects at frontier
  have rootIdentity : root = constructor.objects := by omega
  rw [rootIdentity,frontier]

theorem nested_bytes :
    observe ((Source.zeroVal (E := E) (Γ := [.bool]) 11
      (.array .memory (.array .memory (.bytes .memory) (some 3)) (some 2))).run before) = some (9,10) :=
  actual_observation nestedBytes 0

theorem long_strings :
    observe ((Source.zeroVal (E := E) (Γ := [.bool]) 71
      (.array .memory (.array .memory (.string .memory) (some 64)) (some 1))).run before) = some (66,67) :=
  actual_observation longStrings 0

/-- The unused large child's objects are not allocated under an empty parent. -/
theorem empty_outer :
    observe ((Source.zeroVal (E := E) (Γ := [.bool]) 70
      (.array .memory (.array .memory (.bytes .memory) (some 64)) (some 0))).run before) = some (1,2) :=
  actual_observation emptyOuter 0

theorem nested_dynamic :
    observe ((Source.zeroVal (E := E) (Γ := [.bool]) 11
      (.array .memory (.array .memory (.array .memory (.bytes .memory) none) (some 3)) (some 2))).run before) =
      some (9,10) := actual_observation nestedDynamic 0

/-- The full constructor certificate is inhabited and preserves the old live
Boolean plus all nonheap state on the actual populated input. -/
theorem populated_frame :
    ∃ after root data, SourceDefaultCertificate 11
      (.array .memory (.array .memory (.bytes .memory) (some 3)) (some 2)) rfl before after root data ∧
      after.2.heap.get 0 = before.2.heap.get 0 ∧
      after = (before.1,{before.2 with heap := after.2.heap}) := by
  obtain ⟨after,root,data,certificate,_,_⟩ := nestedBytes.execution before 0
  exact ⟨after,root,data,certificate,certificate.old 0 (by change 0 < 1; decide),certificate.frame⟩

theorem wrong_count_rejected :
    observe ((Source.zeroVal (E := E) (Γ := [.bool]) 11
      (.array .memory (.array .memory (.bytes .memory) (some 3)) (some 2))).run before) ≠ some (8,9) := by
  rw [nested_bytes]
  decide

#print axioms actual_observation
#print axioms nested_bytes
#print axioms long_strings
#print axioms empty_outer
#print axioms nested_dynamic
#print axioms populated_frame
#print axioms wrong_count_rejected
end Solidity.Backend.MemoryCopies.SourceConstructionControls
