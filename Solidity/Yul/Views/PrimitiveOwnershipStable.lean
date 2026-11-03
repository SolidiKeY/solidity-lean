import Solidity.Yul.Views.PrimitiveOwnershipPreservation

namespace Solidity.Yul.Views

/-- Concrete declaration/length facts derive retained integer membership on both
sides. The remaining premises are the actual untouched header/data coordinates. -/
theorem PrimitiveOwnershipPlan.integer_other_read {E ds d active Γ F layout fixed written value s r}
    (p : @PrimitiveOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (entry : {entry // entry ∈ layout.integerTrace}) (i : Nat)
    (bound : i < (p.raw ((layout.integerHeader entry).registration F.this).slot).val)
    (header : ((layout.integerHeader entry).registration F.this).slot ≠ written)
    (data : ((layout.integerHeader entry).element fixed F.this i).slot ≠ written) :
    (p.step.1.2.2.ex.world.accounts F.this).storage.read ((layout.integerHeader entry).elementPath i) =
      (s.2.ex.world.accounts F.this).storage.read ((layout.integerHeader entry).elementPath i) := by
  let h := layout.integerHeader entry
  have old : h.element fixed F.this i ∈ p.old := by
    rw [p.old_agrees]
    exact layout.primitive_integer_subset fixed p.raw _ (layout.integer_element_member fixed p.raw entry i bound)
  have nextBound : i < (p.nextRaw (h.registration F.this).slot).val := by
    have same : p.nextRaw (h.registration F.this).slot = p.raw (h.registration F.this).slot := find_saveSlot_other _ _ _ _ header
    rw [same]
    exact bound
  have next : h.element fixed F.this i ∈ p.next :=
    layout.primitive_integer_subset fixed p.nextRaw _ (layout.integer_element_member fixed p.nextRaw entry i nextBound)
  exact p.other_slot_read static _ old next data

theorem PrimitiveOwnershipPlan.scalar_other_read {E ds d active Γ F layout fixed written value s r}
    (p : @PrimitiveOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (entry : {entry // entry ∈ layout.scalarFamilyTrace}) (i : Nat)
    (bound : i < (p.raw ((layout.scalarFamilyHeader entry).registration F.this).slot).val)
    (header : ((layout.scalarFamilyHeader entry).registration F.this).slot ≠ written)
    (data : ((layout.scalarFamilyHeader entry).element fixed F.this i).slot ≠ written) :
    (p.step.1.2.2.ex.world.accounts F.this).storage.read ((layout.scalarFamilyHeader entry).elementPath i) =
      (s.2.ex.world.accounts F.this).storage.read ((layout.scalarFamilyHeader entry).elementPath i) := by
  let h := layout.scalarFamilyHeader entry
  have old : h.element fixed F.this i ∈ p.old := by
    rw [p.old_agrees]
    exact layout.primitive_scalar_subset fixed p.raw _ (layout.scalarFamily_element_member fixed p.raw entry i bound)
  have nextBound : i < (p.nextRaw (h.registration F.this).slot).val := by
    have same : p.nextRaw (h.registration F.this).slot = p.raw (h.registration F.this).slot := find_saveSlot_other _ _ _ _ header
    rw [same]
    exact bound
  have next : h.element fixed F.this i ∈ p.next :=
    layout.primitive_scalar_subset fixed p.nextRaw _ (layout.scalarFamily_element_member fixed p.nextRaw entry i nextBound)
  exact p.other_slot_read static _ old next data

end Solidity.Yul.Views
