import Solidity.Yul.Views.OwnershipReads
import Solidity.Yul.Views.GenericFlow.Following

namespace Solidity.Yul.Views

private abbrev OwnershipPlan.flowShape {E ds d active Γ F layout fixed written value s r}
    (_ : @OwnershipPlan E ds d active Γ F layout fixed written value s r)
    (q v : Roadmap.Word) (state : Unit → Source.EMState E Γ)
    (journal : Unit → ResidualJournal complementCarrierOwnership) :
    GenericFlow.PreparationShape (List (ScalarPath E.layout (E.lay F.this))) SlotView
      (Source.Op E.layout E.lay E.lay) (OwnershipPlan F layout fixed q v (state ()) (journal ())) :=
  ⟨fun _ => layout.sourceInventory? F fixed (state ()),
    fun old => finiteEncode old ((state ()).2.ex.world.accounts F.this).storage
      (fun slot => (journal ()).cells (complementKey false F.this slot)),
    packedSeparationCheck,
    fun raw => packedSeparationCheck (layout.snapshotInventory fixed (saveSlot raw q v)),
    fun raw => finiteAccountWrite? F.this (layout.snapshotInventory fixed (saveSlot raw q v)) (saveSlot raw q v),
    fun old computed raw encoded checked nextChecked op prepared =>
      ⟨old,computed,raw,encoded,checked,nextChecked,op,prepared⟩⟩

private abbrev OwnershipPlan.flowInput {E ds d active Γ F layout fixed written value s r}
    (p : @OwnershipPlan E ds d active Γ F layout fixed written value s r)
    (static : F.static = false) (q v : Roadmap.Word) :
    GenericFlow.Following (p.flowShape q v (fun _ => p.step.1.2) (fun _ => p.step.2)) :=
  ⟨(fun _ => p.next),layout.sourceInventory_view F fixed p.step.1.2 p.nextRaw
    (fun c member => p.view static c (layout.snapshot_root_member fixed p.nextRaw c member)),
    p.nextRaw,p.reencode static,p.nextChecked⟩

/-- Specialize the shared checked following computation. -/
abbrev OwnershipPlan.following? {E ds d active Γ F layout fixed written value s r}
    (p : @OwnershipPlan E ds d active Γ F layout fixed written value s r)
    (static : F.static = false) (q v : Roadmap.Word) :
    Option (OwnershipPlan F layout fixed q v p.step.1.2 p.step.2) :=
  (p.flowInput static q v).run?

-- Normal delta reduction identifies legacy and generic matcher helpers.
set_option smartUnfolding false in
theorem OwnershipPlan.following_fresh {E ds d active Γ F layout fixed written value s r}
    (p : @OwnershipPlan E ds d active Γ F layout fixed written value s r)
    (static : F.static = false) (q v : Roadmap.Word) :
    p.following? static q v = prepareOwnership? F layout fixed q v p.step.1.2 p.step.2 := by
  exact (p.flowInput static q v).fresh

set_option smartUnfolding false in
theorem OwnershipPlan.following_ready {E ds d active Γ F layout fixed written value s r}
    (p : @OwnershipPlan E ds d active Γ F layout fixed written value s r)
    (static : F.static = false) (q v : Roadmap.Word)
    (checked : packedSeparationCheck (layout.snapshotInventory fixed (saveSlot p.nextRaw q v)) = true)
    (decoded : (finiteAccountWrite? (T := E.lay) F.this (layout.snapshotInventory fixed (saveSlot p.nextRaw q v)) (saveSlot p.nextRaw q v)).isSome) :
    (p.following? static q v).isSome := by
  exact (p.flowInput static q v).ready checked decoded

set_option smartUnfolding false in
theorem OwnershipPlan.prepare_eq {E ds d active Γ F layout fixed written value s r}
    (p : @OwnershipPlan E ds d active Γ F layout fixed written value s r) :
    prepareOwnership? F layout fixed written value s r = some p := by
  exact (p.flowShape written value (fun _ => s) (fun _ => r)).prepare_eq p.old p.oldComputed p.raw p.encoded
    p.oldChecked p.nextChecked p.sourceOp p.prepared

end Solidity.Yul.Views
