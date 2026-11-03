import Solidity.Yul.Views.MemberOwnershipPreservation

namespace Solidity.Yul.Views

/-- Retained full-path members are derived from the SAME unchanged header;
no caller-supplied output inventory/readback law is required. -/
theorem MemberOwnershipPlan.live_other_read {E ds d active Γ F layout fixed written value s r}
    (p : @MemberOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (entry : {entry // entry ∈ layout.headerTrace}) (c)
    (live : c ∈ (layout.header entry).elements fixed F.this (p.raw ((layout.header entry).registration F.this).slot))
    (header : ((layout.header entry).registration F.this).slot ≠ written) (data : c.slot ≠ written) :
    (p.step.1.2.2.ex.world.accounts F.this).storage.read c.path = (s.2.ex.world.accounts F.this).storage.read c.path := by
  have old : c ∈ p.old := by
    rw [p.old_agrees]
    exact layout.snapshot_live_member fixed p.raw entry c live
  have same : p.nextRaw ((layout.header entry).registration F.this).slot = p.raw ((layout.header entry).registration F.this).slot :=
    find_saveSlot_other _ _ _ _ header
  have next : c ∈ p.next := by
    apply layout.snapshot_live_member fixed p.nextRaw entry
    rw [same]
    exact live
  exact p.other_slot_read static c old next data

end Solidity.Yul.Views
