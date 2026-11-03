import Solidity.Yul.Views.RetainedEntryOwnership

namespace Solidity.Yul.Views

def CapturedOwnershipPlan.before {E τ b child active Γ F layout fixed history scopes written value s r}
    (_ : @CapturedOwnershipPlan E τ b child active Γ F layout fixed history scopes written value s r) :
    ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership := ⟨s.2.ex,r⟩
def CapturedOwnershipPlan.after {E τ b child active Γ F layout fixed history scopes written value s r}
    (p : @CapturedOwnershipPlan E τ b child active Γ F layout fixed history scopes written value s r) :
    ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership := ⟨p.step.1.2.2.ex,p.step.2⟩

theorem CapturedOwnershipPlan.companion {E τ b child active Γ F layout fixed history scopes written value s r}
    (p : @CapturedOwnershipPlan E τ b child active Γ F layout fixed history scopes written value s r) (static : F.static=false) :
    p.after=companionRunResidual (companionRunSource p.before [p.sourceOp]) p.updates := by
  unfold after
  rw [p.nonstatic static]
  rfl

theorem CapturedOwnershipPlan.pure_connection {E τ b child active Γ F layout fixed history scopes written value s r}
    (p : @CapturedOwnershipPlan E τ b child active Γ F layout fixed history scopes written value s r)
    (static : F.static=false) :
    capturedSnapshotWriteback p.nextImage p.nextRaw (s.2.ex.world.accounts F.this).storage =
      some ((p.step.1.2.2.ex.world.accounts F.this).storage,fun q => p.step.2.cells (complementKey false F.this q)) := by
  unfold capturedSnapshotWriteback
  rw [show packedSeparationCheck (p.nextImage.snapshot p.nextRaw)=true from p.nextChecked]
  obtain ⟨out,decoded,actual,_,_⟩ := finiteAccountWrite_actual F.this p.next p.nextRaw s.2.ex p.sourceOp p.prepared
  rw [p.nonstatic static]
  change packedStoreWriteback p.next p.nextRaw _=some (((s.2.ex.apply p.sourceOp).world.accounts F.this).storage,_)
  rw [actual]
  unfold packedStoreWriteback
  rw [decoded,Option.map_some]
  apply congrArg (fun m => some (out,m))
  exact (ownership_transport_slice p.old p.next _ r false F.this p.raw p.encoded written value).symm

theorem CapturedOwnershipPlan.rollback {E τ b child active Γ F layout fixed history scopes written value s r}
    (p : @CapturedOwnershipPlan E τ b child active Γ F layout fixed history scopes written value s r)
    (static : F.static=false) :
    (companionRollback (companionEnter p.before F.this F.this 0 [] false) p.after,scopes)=(p.before,scopes) := by
  rw [p.companion static,companionRollback_run]

theorem CapturedOwnershipPlan.child_rollback {E τ b child active Γ F layout fixed history scopes written value s r}
    (p : @CapturedOwnershipPlan E τ b child active Γ F layout fixed history scopes written value s r)
    {qslot qvalue} (childPlan : CapturedOwnershipPlan F layout fixed history scopes qslot qvalue p.step.1.2 p.step.2)
    (static : F.static=false) :
    (companionRollback (companionEnter p.after F.this F.this 0 [] false) childPlan.after,scopes)=(p.after,scopes) := by
  rw [childPlan.companion static]
  change (companionRollback (companionEnter p.after F.this F.this 0 [] false)
    (companionRunResidual (companionRunSource p.after [childPlan.sourceOp]) childPlan.updates),scopes)=(p.after,scopes)
  rw [companionRollback_run]

theorem CapturedOwnershipPlan.outer_rollback {E τ b child active Γ F layout fixed history scopes written value s r}
    (p : @CapturedOwnershipPlan E τ b child active Γ F layout fixed history scopes written value s r)
    {qslot qvalue} (childPlan : CapturedOwnershipPlan F layout fixed history scopes qslot qvalue p.step.1.2 p.step.2)
    (static : F.static=false) :
    companionRollback (companionEnter p.before F.this F.this 0 [] false)
      (companionCommit (companionEnter p.after F.this F.this 0 [] false) childPlan.after)=p.before := by
  rw [childPlan.companion static]
  change companionRollback (companionEnter p.before F.this F.this 0 [] false)
    (companionCommit (companionEnter p.after F.this F.this 0 [] false)
      (companionRunResidual (companionRunSource p.after [childPlan.sourceOp]) childPlan.updates))=p.before
  rw [p.companion static,companionRollback_outer_commit]

end Solidity.Yul.Views
