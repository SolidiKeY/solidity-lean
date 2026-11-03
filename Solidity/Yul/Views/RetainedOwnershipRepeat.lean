import Solidity.Yul.Views.RetainedOwnershipFollowing

namespace Solidity.Yul.Views

theorem saveSlot_shadow (m : SlotView) (q v : Roadmap.Word) : saveSlot (saveSlot m q v) q v=saveSlot m q v := by
  funext p
  unfold saveSlot
  split <;> rfl

def RetainedOwnershipPlan.repeatUpdates {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r) :=
  ownershipUpdates false F.this (ownershipSupport p.next p.next written) (packedMask p.next p.nextRaw)

def RetainedOwnershipPlan.repeatStep {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r) :=
  let source := (Source.applyOp F p.sourceOp).run p.step.1.2
  (source,match source.1 with | .error _ => p.step.2 | .ok _ => residualRun p.step.2 p.repeatUpdates)

theorem RetainedOwnershipPlan.repeat_nonstatic {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r) (static : F.static=false) :
    p.repeatStep=((.ok (),(p.step.1.2.1,{p.step.1.2.2 with ex:=p.step.1.2.2.ex.apply p.sourceOp})),residualRun p.step.2 p.repeatUpdates) := by
  unfold repeatStep
  rw [actualApplyOp_run,static]
  rfl

theorem RetainedOwnershipPlan.repeat_store_identity {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r) (static : F.static=false) :
    (p.repeatStep.1.2.2.ex.world.accounts F.this).storage=(p.step.1.2.2.ex.world.accounts F.this).storage := by
  rw [p.repeat_nonstatic static]
  exact finiteAccountWrite_unchanged F.this p.next p.nextRaw p.step.1.2.2.ex p.sourceOp p.prepared (p.view static)

theorem RetainedOwnershipPlan.repeat_reencode {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r) (static : F.static=false) :
    finiteEncode p.next (p.repeatStep.1.2.2.ex.world.accounts F.this).storage
      (fun q => p.repeatStep.2.cells (complementKey false F.this q))=some p.nextRaw := by
  have slice := ownership_transport_slice p.next p.next (p.step.1.2.2.ex.world.accounts F.this).storage p.step.2 false F.this p.nextRaw (p.reencode static) written value
  have shadow : saveSlot p.nextRaw written value=p.nextRaw := saveSlot_shadow p.raw written value
  rw [shadow] at slice
  rw [p.repeat_store_identity static]
  have same : (fun q => p.repeatStep.2.cells (complementKey false F.this q))=packedMask p.next p.nextRaw := by
    rw [p.repeat_nonstatic static]
    exact slice
  rw [same]
  exact finiteEncode_fromComplement _ _ _ ((packedSeparationCheck_iff _).mp p.nextChecked) (p.view static)

end Solidity.Yul.Views
