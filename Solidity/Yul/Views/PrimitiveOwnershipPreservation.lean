import Solidity.Yul.Views.PrimitiveOwnershipBatch

namespace Solidity.Yul.Views

/-- One source run exposes BOTH complete component views, derived from its
whole combined view. These do not replace primitive reencode/pure_connection. -/
theorem PrimitiveOwnershipPlan.integer_view {E ds d active Γ F layout fixed written value s r}
    (p : @PrimitiveOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false) :
    finiteView (layout.integerSnapshot fixed p.nextRaw) (p.step.1.2.2.ex.world.accounts F.this).storage p.nextRaw :=
  fun c member => p.view static c (layout.primitive_integer_subset fixed p.nextRaw c member)

theorem PrimitiveOwnershipPlan.scalar_view {E ds d active Γ F layout fixed written value s r}
    (p : @PrimitiveOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false) :
    finiteView (layout.scalarFamilySnapshot fixed p.nextRaw) (p.step.1.2.2.ex.world.accounts F.this).storage p.nextRaw :=
  fun c member => p.view static c (layout.primitive_scalar_subset fixed p.nextRaw c member)

/-- Actual typed storage reads in ANY retained component are preserved when its
physical slot is not written. Canonical encode injectivity derives the value;
no readback/adequacy assumption is an input. -/
theorem PrimitiveOwnershipPlan.other_slot_read {E ds d active Γ F layout fixed written value s r}
    (p : @PrimitiveOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (c : ScalarPath E.layout (E.lay F.this)) (old : c ∈ p.old) (next : c ∈ p.next)
    (different : c.slot ≠ written) :
    (p.step.1.2.2.ex.world.accounts F.this).storage.read c.path = (s.2.ex.world.accounts F.this).storage.read c.path := by
  have before := finiteEncode_view p.old _ _ p.raw ((packedSeparationCheck_iff _).mp p.oldChecked) p.encoded c old
  obtain ⟨v,read,encoded⟩ := Option.map_eq_some_iff.mp before
  obtain ⟨w,after,encodedAfter⟩ := Option.map_eq_some_iff.mp (p.view static c next)
  have word : p.nextRaw c.slot = p.raw c.slot := find_saveSlot_other p.raw written c.slot value different
  have same : w = v := c.codec.encode_injective (encodedAfter.trans ((congrArg c.field.findWord word).trans encoded.symm))
  rw [same] at after
  exact after.trans read.symm

end Solidity.Yul.Views
