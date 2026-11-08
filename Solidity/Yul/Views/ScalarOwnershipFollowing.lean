import Solidity.Yul.Views.ScalarOwnershipReads
import Solidity.Yul.Views.GenericFlow.Following

namespace Solidity.Yul.Views

private abbrev ScalarOwnershipPlan.flowShape {E ds d active Γ F layout fixed written value s r}
    (_ : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r)
    (q v : Roadmap.Word) (state : Unit → Source.EMState E Γ)
    (journal : Unit → ResidualJournal complementCarrierOwnership) :
    GenericFlow.PreparationShape (List (ScalarPath E.layout (E.lay F.this))) SlotView
      (Source.Op E.layout E.lay E.lay) (ScalarOwnershipPlan F layout fixed q v (state ()) (journal ())) :=
  ⟨fun _ => layout.scalarFamilySourceInventory? F fixed (state ()),
    fun old => finiteEncode old ((state ()).2.ex.world.accounts F.this).storage
      (fun slot => (journal ()).cells (complementKey false F.this slot)),
    packedSeparationCheck,
    fun raw => packedSeparationCheck (layout.scalarFamilySnapshot fixed (saveSlot raw q v)),
    fun raw => finiteAccountWrite? F.this (layout.scalarFamilySnapshot fixed (saveSlot raw q v)) (saveSlot raw q v),
    fun old computed raw encoded checked nextChecked op prepared =>
      ⟨old,computed,raw,encoded,checked,nextChecked,op,prepared⟩⟩

private abbrev ScalarOwnershipPlan.flowInput {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r)
    (static : F.static = false) (q v : Roadmap.Word) :
    GenericFlow.Following (p.flowShape q v (fun _ => p.step.1.2) (fun _ => p.step.2)) :=
  ⟨(fun _ => p.next),layout.scalarFamilySourceInventory_view F fixed p.step.1.2 p.nextRaw
    (fun c member => p.view static c (layout.scalarFamily_root_member fixed p.nextRaw c member)),
    p.nextRaw,p.reencode static,p.nextChecked⟩

/-- Specialize the shared checked following computation. -/
abbrev ScalarOwnershipPlan.following? {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r)
    (static : F.static = false) (q v : Roadmap.Word) :
    Option (ScalarOwnershipPlan F layout fixed q v p.step.1.2 p.step.2) :=
  (p.flowInput static q v).run?

-- Normal delta reduction identifies legacy and generic matcher helpers.
set_option smartUnfolding false in
theorem ScalarOwnershipPlan.following_fresh {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r)
    (static : F.static = false) (q v : Roadmap.Word) :
    p.following? static q v = prepareScalarOwnership? F layout fixed q v p.step.1.2 p.step.2 := by
  exact (p.flowInput static q v).fresh

set_option smartUnfolding false in
theorem ScalarOwnershipPlan.following_ready {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r)
    (static : F.static = false) (q v : Roadmap.Word)
    (checked : packedSeparationCheck (layout.scalarFamilySnapshot fixed (saveSlot p.nextRaw q v)) = true)
    (decoded : (finiteAccountWrite? (T := E.lay) F.this (layout.scalarFamilySnapshot fixed (saveSlot p.nextRaw q v)) (saveSlot p.nextRaw q v)).isSome) :
    (p.following? static q v).isSome := by
  exact (p.flowInput static q v).ready checked decoded

set_option smartUnfolding false in
theorem ScalarOwnershipPlan.prepare_eq {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) :
    prepareScalarOwnership? F layout fixed written value s r = some p := by
  exact (p.flowShape written value (fun _ => s) (fun _ => r)).prepare_eq p.old p.oldComputed p.raw p.encoded
    p.oldChecked p.nextChecked p.sourceOp p.prepared

end Solidity.Yul.Views
