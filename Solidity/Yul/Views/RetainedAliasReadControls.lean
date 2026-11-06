import Solidity.Yul.Views.RetainedChronologyControls

namespace Solidity.Yul.Views.Controls

theorem rh_next_elements : rhPlan.nextImage.elements=rhImage.elements := by unfold rhPlan; rfl

def rhFirst : {element // element ∈ rhPlan.nextImage.elements} :=
  ⟨rhImage.elements[0]'(by decide),by rw [rh_next_elements]; exact List.mem_cons_self⟩
def rhHeaderEntry : {entry // entry ∈ agChild.headers (rhLayout.path.go (.index rhFirst.val.1)) (rhLayout.childCursor agFixed rhFirst.val.1)} :=
  ⟨(agInner 0,.integer rcU16,3202),by decide⟩
def rhHeader : PathIntHeader agEnv (agInner 0) rcU16 3202 := rhFirst.val.2.header rhHeaderEntry

theorem rh_inner_length3 : (Source.readLen (E := agEnv) packedStepFrame (agInner 0)).run rhPlan.step.1.2 = (.ok 3,rhPlan.step.1.2) := by
  have read := rhPlan.retained_header_read rfl rhFirst rhHeaderEntry
  change (Source.readLen (E := agEnv) packedStepFrame (agInner 0)).run rhPlan.step.1.2 =
    (.ok (rhPlan.nextRaw (rhHeader.registration account).slot).val,rhPlan.step.1.2) at read
  have nextRaw : rhPlan.nextRaw=saveSlot rhRaw0 101 3 := congrArg (fun m => saveSlot m 101 3) rh_raw_input
  rw [nextRaw] at read
  exact read

theorem rh_tail_member : rhHeader.element agFixed account 2 ∈ rhPlan.next := by
  change _ ∈ rhPlan.nextImage.snapshot rhPlan.nextRaw
  apply List.mem_cons.mpr
  right
  apply List.mem_flatMap.mpr
  refine ⟨rhFirst.val,rhFirst.property,?_⟩
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨rhHeaderEntry,List.mem_attach _ _,?_⟩
  apply (rhHeader.elements_member agFixed account _ _).mpr
  refine ⟨2,?_,rfl⟩
  have nextRaw : rhPlan.nextRaw=saveSlot rhRaw0 101 3 := congrArg (fun m => saveSlot m 101 3) rh_raw_input
  rw [nextRaw]
  decide

theorem rh_tail77 : (Source.readLoc (E := agEnv) packedStepFrame (Source.Loc.stor (τ := .int rcU16)
    (rhHeader.elementPath 2))).run rhPlan.step.1.2=(.ok (.int 77 (by decide)),rhPlan.step.1.2) := by
  have read := rhHeader.read_element packedStepFrame rhPlan.step.1.2 agFixed 2 rhPlan.nextRaw rfl (rhPlan.view rfl _ rh_tail_member)
  have nextRaw : rhPlan.nextRaw=saveSlot rhRaw0 101 3 := congrArg (fun m => saveSlot m 101 3) rh_raw_input
  rw [nextRaw] at read
  exact read

theorem rh_actual_source_locals : rhPlan.step.1.2.1=agAliases.1 := by rw [rhPlan.nonstatic rfl]; rfl

theorem rh_first_alias_length : (Source.lengthOf (E := agEnv) packedStepFrame
    ((rhPlan.subStep (Source.Locals.nil (D := agEnv.layout))).1.2.1.get .here)).run
      (rhPlan.subStep (Source.Locals.nil (D := agEnv.layout))).1.2 =
        (.ok 3,(rhPlan.subStep (Source.Locals.nil (D := agEnv.layout))).1.2) := by
  rw [(rhPlan.sub_same_store _).1,rh_actual_source_locals]
  exact rh_inner_length3

theorem rh_second_alias_length : (Source.lengthOf (E := agEnv) packedStepFrame
    ((rhPlan.subStep (Source.Locals.nil (D := agEnv.layout))).1.2.1.get (.there .here))).run
      (rhPlan.subStep (Source.Locals.nil (D := agEnv.layout))).1.2 =
        (.ok 3,(rhPlan.subStep (Source.Locals.nil (D := agEnv.layout))).1.2) := by
  rw [(rhPlan.sub_same_store _).1,rh_actual_source_locals]
  exact rh_inner_length3

theorem rh_typed_index_after_dormancy : (Source.indexLoc (E := agEnv) packedStepFrame
    (rhPlan.step.1.2.1.get .here) 2).run rhPlan.step.1.2 =
      (.ok (.stor (rhHeader.elementPath 2)),rhPlan.step.1.2) := by
  rw [rh_actual_source_locals]
  exact rhHeader.indexLoc packedStepFrame rhPlan.step.1.2 3 rh_inner_length3 2

theorem rh_inhabited_MemOK : Source.MemOK agEnv agState.2.heap.ty rhPlan.step.1.2 :=
  rhPlan.MemOK _ (by
    have h := Source.writeLen_mem (E := agEnv) (H := agState.2.heap.ty) packedStepFrame agPath 0 agAliases ag_alias_MemOK
    change Source.MemOK agEnv agState.2.heap.ty agShrink.2 at h
    exact h)

end Solidity.Yul.Views.Controls
