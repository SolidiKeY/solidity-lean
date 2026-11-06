import Solidity.Yul.Views.RecursiveDynamicBoundaryControls

namespace Solidity.Yul.Views

theorem RecursiveOwnershipPlan.registered_other_read {E ds d active Γ F layout fixed written value s r}
    (p : @RecursiveOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (c : ScalarPath E.layout (E.lay F.this)) (member : c ∈ layout.registrations) (other : c.slot ≠ written) :
    (p.step.1.2.2.ex.world.accounts F.this).storage.read c.path = (s.2.ex.world.accounts F.this).storage.read c.path := by
  have old : c ∈ p.old := by
    rw [p.old_agrees]
    exact layout.snapshot_root_member fixed p.raw c member
  exact p.other_slot_read static c old (layout.snapshot_root_member fixed p.nextRaw c member) other

end Solidity.Yul.Views

namespace Solidity.Yul.Views.Controls

/-- Whole administrative store identity, not merely selected read equality. -/
theorem rc_initial_whole_store : rcLayout.snapshotWriteback rcFixed rcRaw (rcState.2.ex.world.accounts account).storage =
    some ((rcState.2.ex.world.accounts account).storage,packedMask (rcLayout.snapshot rcFixed rcRaw) rcRaw) := by
  apply rcLayout.snapshot_unchanged
  · rw [rc_empty_inventory]
    exact (packedSeparationCheck_iff _).mpr rcLayout.separated
  · rw [rc_empty_inventory]
    exact rc_initial_view

/-- Covers actual stamp/guard/tag/address/marker, including siblings of BOTH
nested struct levels. Premises are physical untouched-header coordinates. -/
theorem rc_fixed_members_unchanged (c : ScalarPath rcEnv.layout (rcEnv.lay account))
    (member : c ∈ rcLayout.registrations) (other2 : c.slot ≠ 2) (other3 : c.slot ≠ 3) (other5 : c.slot ≠ 5) :
    (rcRegrowY.step.1.2.2.ex.world.accounts account).storage.read c.path = (rcState.2.ex.world.accounts account).storage.read c.path := by
  change (rcRegrowY.step.1.2.2.ex.world.accounts packedStepFrame.this).storage.read c.path = (rcState.2.ex.world.accounts packedStepFrame.this).storage.read c.path
  rw [rcRegrowY.registered_other_read rfl c member other3,
    rcRegrowX.registered_other_read rfl c member other2,
    rcZeroY.registered_other_read rfl c member other3,
    rcZeroX.registered_other_read rfl c member other2,
    rcBool.registered_other_read rfl c member other5,
    rcSigned.registered_other_read rfl c member other3,
    rcGrow.registered_other_read rfl c member other2]

end Solidity.Yul.Views.Controls
