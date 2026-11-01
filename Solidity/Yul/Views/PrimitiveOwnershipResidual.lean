import Solidity.Yul.Views.PrimitiveOwnershipStable

namespace Solidity.Yul.Views

/-- Every actually unowned byte survives the single combined complementary
write, including partial-slot padding and newly dead element bytes. -/
theorem PrimitiveOwnershipPlan.residual_byte {E ds d active Γ F layout fixed written value s r}
    (p : @PrimitiveOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (q : Roadmap.Word) (i : Fin 32) (unowned : packedOwnsByte p.next q i = false) :
    lowByte (p.step.2.cells (complementKey false F.this q)) i = lowByte (p.nextRaw q) i := by
  rw [congrFun (p.complement static) q]
  exact packedMask_residual p.next p.nextRaw q i unowned

end Solidity.Yul.Views
