import Solidity.Yul.Views.RetainedOwnershipSub

namespace Solidity.Yul.Views

def RetainedOwnershipPlan.before {E τ b child active Γ F layout fixed history written value s r}
    (_ : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r) :
    ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership := ⟨s.2.ex,r⟩
def RetainedOwnershipPlan.after {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r) :
    ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership := ⟨p.step.1.2.2.ex,p.step.2⟩

theorem RetainedOwnershipPlan.companion {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r) (static : F.static=false) :
    p.after=companionRunResidual (companionRunSource p.before [p.sourceOp]) p.updates := by
  unfold after
  rw [p.nonstatic static]
  rfl

theorem RetainedOwnershipPlan.pure_connection {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r) (static : F.static=false) :
    retainedSnapshotWriteback layout fixed history p.nextRaw (s.2.ex.world.accounts F.this).storage =
      some ((p.step.1.2.2.ex.world.accounts F.this).storage,fun q => p.step.2.cells (complementKey false F.this q)) := by
  unfold retainedSnapshotWriteback RetainedArrayLayout.snapshot?
  dsimp only [Bind.bind,Option.bind]
  have computed : prepareRetainedArrayImage? layout fixed history (p.nextRaw layout.header.slot)=some p.nextImage := p.nextImageComputed
  rw [computed]
  dsimp only [Bind.bind,Option.bind,Pure.pure]
  rw [show packedSeparationCheck (p.nextImage.snapshot p.nextRaw)=true from p.nextChecked]
  obtain ⟨out,decoded,actual,_,_⟩ := finiteAccountWrite_actual F.this p.next p.nextRaw s.2.ex p.sourceOp p.prepared
  rw [p.nonstatic static]
  change packedStoreWriteback p.next p.nextRaw _=some (((s.2.ex.apply p.sourceOp).world.accounts F.this).storage,_)
  rw [actual]
  unfold packedStoreWriteback
  rw [decoded,Option.map_some]
  apply congrArg (fun m => some (out,m))
  exact (ownership_transport_slice p.old p.next _ r false F.this p.raw p.encoded written value).symm

/-- History checkpoint uses the exact caller prefix, independently of the
source and residual journal lengths. A raw write itself forms no references.
Caller history survives local suspension. Capturing ALL producer events and
proving escape completeness are separate open instrumentation obligations. -/
structure RetainedCallSnapshot {E τ b child active a} (layout : @RetainedArrayLayout E τ b child active a) where
  physical : ResidualFrame
  callerHistory : RetainedIndexHistory layout

def retainedEnter {E τ b child active a} {layout : @RetainedArrayLayout E τ b child active a}
    (s : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership) (history : RetainedIndexHistory layout)
    (caller : Roadmap.Address) (amount : Roadmap.Word) (input : Roadmap.Bytes) (static : Bool) : RetainedCallSnapshot layout :=
  ⟨companionEnter s a caller amount input static,history⟩
def retainedRollback {E τ b child active a} {layout : @RetainedArrayLayout E τ b child active a}
    (f : RetainedCallSnapshot layout) (s : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership)
    (_history : RetainedIndexHistory layout) := (companionRollback f.physical s,f.callerHistory)
def retainedCommit {E τ b child active a} {layout : @RetainedArrayLayout E τ b child active a}
    (f : RetainedCallSnapshot layout) (s : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership)
    (history : RetainedIndexHistory layout) := (companionCommit f.physical s,history)

theorem RetainedOwnershipPlan.rollback {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r) (static : F.static=false)
    (events : RetainedIndexHistory layout) :
    retainedRollback (retainedEnter p.before history F.this 0 [] false) p.after (history++events)=(p.before,history) := by
  rw [p.companion static]
  unfold retainedRollback retainedEnter
  dsimp only
  rw [companionRollback_run]

theorem RetainedOwnershipPlan.child_rollback {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r)
    {qslot qvalue} (childPlan : RetainedOwnershipPlan F layout fixed history qslot qvalue p.step.1.2 p.step.2)
    (static : F.static=false) (events : RetainedIndexHistory layout) :
    retainedRollback (retainedEnter p.after history F.this 0 [] false) childPlan.after (history++events)=(p.after,history) := by
  rw [childPlan.companion static]
  change (companionRollback (companionEnter p.after F.this F.this 0 [] false)
    (companionRunResidual (companionRunSource p.after [childPlan.sourceOp]) childPlan.updates),history)=(p.after,history)
  rw [companionRollback_run]

theorem RetainedOwnershipPlan.committed_child_outer_rollback {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r)
    {qslot qvalue} (childPlan : RetainedOwnershipPlan F layout fixed history qslot qvalue p.step.1.2 p.step.2)
    (static : F.static=false) (events : RetainedIndexHistory layout) :
    retainedRollback (retainedEnter p.before history F.this 0 [] false)
      (retainedCommit (retainedEnter p.after history F.this 0 [] false) childPlan.after (history++events)).1
      (retainedCommit (retainedEnter p.after history F.this 0 [] false) childPlan.after (history++events)).2=(p.before,history) := by
  rw [childPlan.companion static]
  change (companionRollback (companionEnter p.before F.this F.this 0 [] false)
    (companionCommit (companionEnter p.after F.this F.this 0 [] false)
      (companionRunResidual (companionRunSource p.after [childPlan.sourceOp]) childPlan.updates)),history)=(p.before,history)
  rw [p.companion static]
  rw [companionRollback_outer_commit]

end Solidity.Yul.Views
