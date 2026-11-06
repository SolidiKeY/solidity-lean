import Solidity.Yul.Views.PrimitiveDynamicSnapshot

namespace Solidity.Yul.Views

/-- Metadata classification only; not a second layout traversal. -/
def StorageDeclaration.primitiveDynamic {E τ} (d : StorageDeclaration E τ) : Bool :=
  StorageDeclaration.casesOn (motive := fun _ _ => Bool) d
    (fun _ => false) true (fun _ _ _ => true) (fun _ _ => true) (fun _ => true)

theorem StorageDeclaration.primitive_selector_coverage {E τ} (d : StorageDeclaration E τ) :
    (d.integerType?.isSome || d.scalarFamilyType?.isSome) = d.primitiveDynamic := by
  cases d <;> rfl

theorem StorageDeclaration.primitive_selectors_disjoint {E τ} (d : StorageDeclaration E τ) :
    (d.integerType?.isSome && d.scalarFamilyType?.isSome) = false := by
  cases d <;> rfl

theorem ComputedStorage.primitive_trace_roots_disjoint {E ds d active a} (r : @ComputedStorage E ds d active a)
    (i : {entry // entry ∈ r.integerTrace}) (j : {entry // entry ∈ r.scalarFamilyTrace}) : i.val.1 ≠ j.val.1 :=
  primitive_dynamic_roots_ne (r.integerHeader i) (r.scalarFamilyHeader j)

theorem primitive_element_paths_ne {E ri rs t k ci cs}
    (h : IntDynamicHeader E ri t ci) (g : ScalarDynamicHeader E rs k cs)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i j : Nat) :
    (h.element fixed a i).path ≠ (g.element fixed a j).path := by
  intro same
  exact primitive_dynamic_roots_ne h g (congrArg Source.SPath.root same)

/-- Exact enumeration size shows registered fields/headers are appended ONCE.
Duplicate paths/physical collisions are then rejected by the REAL combined
checker, whose success yields primitive_checked_paths/separated. -/
theorem ComputedStorage.primitive_length {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) :
    (r.primitiveSnapshot fixed m).length = r.registrations.length +
      ((r.primitiveIntegerLive fixed m).length + (r.primitiveScalarLive fixed m).length) := by
  simp only [primitiveSnapshot,List.length_append]

end Solidity.Yul.Views
