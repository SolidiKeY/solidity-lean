import Solidity.Yul.Views.PrimitiveDynamicCoverage

namespace Solidity.Yul.Views

/-- Both actual source length traversals run over the SAME initial typed source.
Only element lists are concatenated; registered headers/fixed fields occur once. -/
def ComputedStorage.primitiveSourceInventory? {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ) := do
  let ints ← r.integerSourceElements? F fixed s r.integerTrace.attach
  let scalars ← r.scalarFamilySourceElements? F fixed s r.scalarFamilyTrace.attach
  some (r.registrations ++ (ints ++ scalars))

theorem ComputedStorage.primitiveSourceInventory_roots {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ) (old)
    (ready : r.primitiveSourceInventory? F fixed s = some old) (c) (member : c ∈ r.registrations) : c ∈ old := by
  cases first : r.integerSourceElements? F fixed s r.integerTrace.attach with
  | none =>
    unfold primitiveSourceInventory? at ready
    rw [first] at ready
    cases ready
  | some ints =>
    cases second : r.scalarFamilySourceElements? F fixed s r.scalarFamilyTrace.attach with
    | none =>
      unfold primitiveSourceInventory? at ready
      rw [first] at ready
      change (do let scalars ← r.scalarFamilySourceElements? F fixed s r.scalarFamilyTrace.attach; some (r.registrations ++ (ints ++ scalars))) = some old at ready
      rw [second] at ready
      cases ready
    | some scalars =>
      unfold primitiveSourceInventory? at ready
      rw [first] at ready
      change (do let scalars ← r.scalarFamilySourceElements? F fixed s r.scalarFamilyTrace.attach; some (r.registrations ++ (ints ++ scalars))) = some old at ready
      rw [second] at ready
      have same : r.registrations ++ (ints ++ scalars) = old := Option.some.inj ready
      rw [← same]
      exact List.mem_append_left _ member

theorem ComputedStorage.primitiveSourceInventory_view {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (m : SlotView) (view : finiteView r.registrations (s.2.ex.world.accounts F.this).storage m) :
    r.primitiveSourceInventory? F fixed s = some (r.primitiveSnapshot fixed m) := by
  unfold primitiveSourceInventory?
  rw [r.integerSourceElements_view F fixed s m view,r.scalarFamilySourceElements_view F fixed s m view]
  rfl

end Solidity.Yul.Views
