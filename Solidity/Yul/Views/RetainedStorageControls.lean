import Solidity.Yul.Views.RetainedOwnershipFrame
import Solidity.Yul.Views.AggregateStorageAliasControls

namespace Solidity.Yul.Views.Controls

theorem rh_layout_ready : (prepareRetainedArrayLayout? agChild "AG" account (agName "nodes")).isSome := by decide
def rhLayout := (prepareRetainedArrayLayout? agChild "AG" account (agName "nodes")).get rh_layout_ready
theorem rh_path : rhLayout.path=agPath := rfl
theorem rh_origin : rhLayout.header.slot=0 := rfl

theorem rh_formed : (Source.indexLoc (E := agEnv) packedStepFrame
    (Source.Val.storRef (τ := .array .storage (.struct .storage agNode) none) (by rfl) rhLayout.path) 0).run agApplied.2 =
      (.ok (.stor (rhLayout.path.go (.index 0))),agApplied.2) := by
  have formed := rhLayout.indexLoc (F := packedStepFrame) agApplied.2 2 (by rfl) 0
  exact formed

def rhEvent := recordRetainedIndex rhLayout packedStepFrame agApplied.2 0 rfl rh_formed
def rhHistory : RetainedIndexHistory rhLayout := [rhEvent,rhEvent]
theorem rh_duplicate_alias_once : retainedVisitIndices rhHistory 0=[0] := rfl

def rhRaw0 : SlotView := saveSlot (saveSlot agRaw 0 0) 1000 ⟨77+88*65536+77*2^32+2^240,by decide⟩
theorem rh_image_ready : (prepareRetainedArrayImage? rhLayout agFixed rhHistory 0).isSome := by decide
def rhImage := (prepareRetainedArrayImage? rhLayout agFixed rhHistory 0).get rh_image_ready
def rhOld := rhImage.snapshot rhRaw0
theorem rh_coordinates : rhOld.map (fun c => (c.path.steps,c.slot.val,c.field.offset,c.field.width)) =
  [([],0,0,32),([.index 0,.field 0],100,0,2),([.index 0,.field 1],101,0,32),
   ([.index 0,.field 1,.index 0],1000,0,2),([.index 0,.field 1,.index 1],1000,2,2)] := rfl

def rhC0 := rhOld[0]'(by decide)
def rhC1 := rhOld[1]'(by decide)
def rhC2 := rhOld[2]'(by decide)
def rhC3 := rhOld[3]'(by decide)
def rhC4 := rhOld[4]'(by decide)
theorem rh_view0 : scalarPathView rhC0.path rhC0.codec rhC0.slot (agShrink.2.2.ex.world.accounts account).storage rhRaw0 := rfl
theorem rh_view1 : scalarPathView rhC1.path rhC1.codec rhC1.slot (agShrink.2.2.ex.world.accounts account).storage rhRaw0 := rfl
theorem rh_view2 : scalarPathView rhC2.path rhC2.codec rhC2.slot (agShrink.2.2.ex.world.accounts account).storage rhRaw0 := rfl
theorem rh_view3 : scalarPathView rhC3.path rhC3.codec rhC3.slot (agShrink.2.2.ex.world.accounts account).storage rhRaw0 := rfl
theorem rh_view4 : scalarPathView rhC4.path rhC4.codec rhC4.slot (agShrink.2.2.ex.world.accounts account).storage rhRaw0 := rfl
theorem rh_old_list : rhOld=[rhC0,rhC1,rhC2,rhC3,rhC4] := rfl

theorem rh_view : finiteView rhOld (agShrink.2.2.ex.world.accounts account).storage rhRaw0 := by
  intro c member
  rw [rh_old_list] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact rh_view0
  · exact rh_view1
  · exact rh_view2
  · exact rh_view3
  · exact rh_view4

theorem rh_separated : packedSeparationCheck rhOld=true := by decide
def rhResidual : ResidualJournal complementCarrierOwnership :=
  ⟨fun k => if k.transient then 0 else packedMask rhOld rhRaw0 k.slot,[]⟩
theorem rh_encode : finiteEncode rhOld (agShrink.2.2.ex.world.accounts account).storage
    (fun q => rhResidual.cells (complementKey false account q))=some rhRaw0 :=
  finiteEncode_fromComplement _ _ _ ((packedSeparationCheck_iff _).mp rh_separated) rh_view

theorem rh_retained_source_inventory : rhLayout.sourceInventory? (F := packedStepFrame) agFixed rhHistory agShrink.2=some rhOld := rfl

theorem rh_static_view : finiteView rhImage.registrations (agShrink.2.2.ex.world.accounts account).storage rhRaw0 :=
  fun c member => rh_view c (rhImage.snapshot_roots rhRaw0 c member)
theorem rh_source_computed : rhImage.sourceInventory? (F := packedStepFrame) agShrink.2=some rhOld :=
  rhImage.source_view (F := packedStepFrame) agShrink.2 rhRaw0 rh_static_view

def rhNextRaw := saveSlot rhRaw0 101 3
def rhNext := rhImage.snapshot rhNextRaw
theorem rh_next_checked : packedSeparationCheck rhNext=true := by decide
theorem rh_op_ready : (finiteAccountWrite? (T := agEnv.lay) account rhNext rhNextRaw).isSome := by decide
def rhOp := (finiteAccountWrite? (T := agEnv.lay) account rhNext rhNextRaw).get rh_op_ready
@[irreducible]
def rhPlan : RetainedOwnershipPlan packedStepFrame rhLayout agFixed rhHistory 101 3 agShrink.2 rhResidual :=
  ⟨0,(by rfl),rhImage,Option.get_mem rh_image_ready,rhOld,rh_source_computed,rhRaw0,rh_encode,rh_separated,
    rhImage,Option.get_mem rh_image_ready,rh_next_checked,rhOp,Option.get_mem rh_op_ready⟩

theorem rh_raw_input : rhPlan.raw=rhRaw0 := by unfold rhPlan; rfl

theorem rh_full_map : finiteEncode rhPlan.next (rhPlan.step.1.2.2.ex.world.accounts account).storage
    (fun q => rhPlan.step.2.cells (complementKey false account q))=some (saveSlot rhRaw0 101 3) := by
  have h := rhPlan.reencode rfl
  change _=some (saveSlot rhPlan.raw 101 3) at h
  rw [rh_raw_input] at h
  exact h

theorem rh_sub_full_map : finiteEncode rhPlan.next ((rhPlan.subStep (Source.Locals.nil (D := agEnv.layout))).1.2.2.ex.world.accounts account).storage
    (fun q => (rhPlan.subStep (Source.Locals.nil (D := agEnv.layout))).2.1.cells (complementKey false account q))=some rhPlan.nextRaw := rhPlan.sub_reencode _ rfl

theorem rh_caller_aliases_restored : (rhPlan.subStep (Source.Locals.nil (D := agEnv.layout))).1.2.1=agAliases.1 ∧
    (rhPlan.subStep (Source.Locals.nil (D := agEnv.layout))).2.2=rhHistory := by
  rw [rhPlan.sub_nonstatic _ rfl]
  exact ⟨rfl,rfl⟩

theorem rh_source_success : rhPlan.step.1.1=.ok () := by rw [rhPlan.nonstatic rfl]

end Solidity.Yul.Views.Controls
