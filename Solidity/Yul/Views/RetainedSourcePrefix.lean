import Solidity.Yul.Views.RetainedStorageNegativeControls

namespace Solidity.Yul.Views.Controls

def rhBeforeRaw := saveSlot rhRaw0 0 2
def rhBeforePaths := rhImage2.snapshot rhBeforeRaw

theorem rh_formation_preserves_selection : retainedVisitIndices ([] : RetainedIndexHistory rhLayout) 2=retainedVisitIndices rhHistory 2 := rfl

theorem rh_before_paths : rhBeforePaths=agComputed.1 := rfl

def rhBefore0 := rhBeforePaths[0]'(by decide)
theorem rh_before_view0 : scalarPathView rhBefore0.path rhBefore0.codec rhBefore0.slot
    (agApplied.2.2.ex.world.accounts account).storage rhBeforeRaw := rfl

def rhBefore1 := rhBeforePaths[1]'(by decide)
theorem rh_before_view1 : scalarPathView rhBefore1.path rhBefore1.codec rhBefore1.slot
    (agApplied.2.2.ex.world.accounts account).storage rhBeforeRaw := rfl

def rhBefore2 := rhBeforePaths[2]'(by decide)
theorem rh_before_view2 : scalarPathView rhBefore2.path rhBefore2.codec rhBefore2.slot
    (agApplied.2.2.ex.world.accounts account).storage rhBeforeRaw := rfl

def rhBefore3 := rhBeforePaths[3]'(by decide)
theorem rh_before_view3 : scalarPathView rhBefore3.path rhBefore3.codec rhBefore3.slot
    (agApplied.2.2.ex.world.accounts account).storage rhBeforeRaw := rfl

def rhBefore4 := rhBeforePaths[4]'(by decide)
theorem rh_before_view4 : scalarPathView rhBefore4.path rhBefore4.codec rhBefore4.slot
    (agApplied.2.2.ex.world.accounts account).storage rhBeforeRaw := rfl

def rhBefore5 := rhBeforePaths[5]'(by decide)
theorem rh_before_view5 : scalarPathView rhBefore5.path rhBefore5.codec rhBefore5.slot
    (agApplied.2.2.ex.world.accounts account).storage rhBeforeRaw := rfl

def rhBefore6 := rhBeforePaths[6]'(by decide)
theorem rh_before_view6 : scalarPathView rhBefore6.path rhBefore6.codec rhBefore6.slot
    (agApplied.2.2.ex.world.accounts account).storage rhBeforeRaw := rfl

def rhBefore7 := rhBeforePaths[7]'(by decide)
theorem rh_before_view7 : scalarPathView rhBefore7.path rhBefore7.codec rhBefore7.slot
    (agApplied.2.2.ex.world.accounts account).storage rhBeforeRaw := rfl

theorem rh_before_list : rhBeforePaths=[rhBefore0,rhBefore1,rhBefore2,rhBefore3,rhBefore4,rhBefore5,rhBefore6,rhBefore7] := rfl

theorem rh_before_view : finiteView rhBeforePaths (agApplied.2.2.ex.world.accounts account).storage rhBeforeRaw := by
  intro c member
  rw [rh_before_list] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rh_before_view0
  · exact rh_before_view1
  · exact rh_before_view2
  · exact rh_before_view3
  · exact rh_before_view4
  · exact rh_before_view5
  · exact rh_before_view6
  · exact rh_before_view7

theorem rh_before_separated : packedSeparationCheck rhBeforePaths=true := by decide

def rhBeforeResidual : ResidualJournal complementCarrierOwnership :=
  ⟨fun k => if k.transient then 0 else packedMask rhBeforePaths rhBeforeRaw k.slot,[]⟩

theorem rh_before_encoded : finiteEncode rhBeforePaths (agApplied.2.2.ex.world.accounts account).storage
    (fun q => rhBeforeResidual.cells (complementKey false account q))=some rhBeforeRaw :=
  finiteEncode_fromComplement _ _ _ ((packedSeparationCheck_iff _).mp rh_before_separated) rh_before_view

def rhPrefixUpdates := ownershipUpdates false account (ownershipSupport rhBeforePaths rhOld 0) (packedMask rhOld rhRaw0)
def rhPrefixResidual := residualRun rhBeforeResidual rhPrefixUpdates

theorem rh_shrink_raw : saveSlot rhBeforeRaw 0 0=rhRaw0 := by
  funext q
  by_cases same : q=0
  · subst q; rfl
  · simp only [rhBeforeRaw,saveSlot,if_neg same]

theorem rh_prefix_slice : (fun q => rhPrefixResidual.cells (complementKey false account q))=packedMask rhOld rhRaw0 := by
  have transported := ownership_transport_slice rhBeforePaths rhOld (agApplied.2.2.ex.world.accounts account).storage
    rhBeforeResidual false account rhBeforeRaw rh_before_encoded 0 0
  rw [rh_shrink_raw] at transported
  exact transported

/-- The exact owner writeLen result agShrink, not pure view preparation, now
shares the SAME raw-header shrink and complementary journal update. -/
theorem rh_owner_shrink_coupled : finiteEncode rhOld (agShrink.2.2.ex.world.accounts account).storage
    (fun q => rhPrefixResidual.cells (complementKey false account q))=some rhRaw0 := by
  rw [rh_prefix_slice]
  exact finiteEncode_fromComplement _ _ _ ((packedSeparationCheck_iff _).mp rh_separated) rh_view

theorem rh_dropped_child_full_word : rhPrefixResidual.cells (complementKey false account 2000)=⟨99+2^240,by decide⟩ := by
  have same := congrFun rh_prefix_slice 2000
  exact same

/-- Same concrete source preparation, now over the ACTUAL prefix residual
journal. No caller supplies a final output map or frame law. -/
@[irreducible]
def rhCoupledPlan : RetainedOwnershipPlan packedStepFrame rhLayout agFixed rhHistory 101 3 agShrink.2 rhPrefixResidual :=
  ⟨rhPlan.oldLength,rhPlan.lengthComputed,rhPlan.oldImage,rhPlan.oldImageComputed,rhPlan.old,rhPlan.oldComputed,
   rhRaw0,(by rw [show rhPlan.old=rhOld from by unfold rhPlan; rfl]; exact rh_owner_shrink_coupled),rhPlan.oldChecked,
   rhImage,Option.get_mem rh_image_ready,rh_next_checked,rhOp,Option.get_mem rh_op_ready⟩

theorem rh_coupled_same_op : rhCoupledPlan.sourceOp=rhPlan.sourceOp := by unfold rhCoupledPlan rhPlan; rfl

theorem rh_coupled_same_source : rhCoupledPlan.step.1=rhPlan.step.1 := by
  unfold RetainedOwnershipPlan.step
  rw [rh_coupled_same_op]

theorem rh_closed_with_actual_prefix : finiteEncode rhCoupledPlan.next
    (rhAfterCall.2.ex.world.accounts account).storage
    (fun q => rhCoupledPlan.step.2.cells (complementKey false account q))=some rhCoupledPlan.nextRaw := by
  rw [show rhAfterCall.2=rhCoupledPlan.step.1.2.2 from congrArg (fun x => x.2.2) rh_coupled_same_source.symm]
  exact rhCoupledPlan.reencode rfl

end Solidity.Yul.Views.Controls
