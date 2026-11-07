import Solidity.Backend.Aggregates.BoolArrayEntry
import Solidity.Backend.Aggregates.BoolArrayControls

/-! Actual argument decoder/conversion clients and total raw-entry phase
outcomes. No physical EVM/resource or general compiler simulation claim. -/
namespace Solidity.Backend.Aggregates.BoolArrayEntryControls
open Solidity ByteParameterControls NestedCalldataControls BoolArrays BoolArrayControls BoolArrayEntry

theorem good_import : lowerEntry (E := E) aliasTarget goodFrame selector goodData rfl rfl 0 = .ok BoolArrayControls.lowered := by
  rw [lowerEntry_of_ok aliasTarget goodFrame selector goodData rfl rfl good_entry]
  exact phase_success

theorem good_source_run : (sourceCopy goodFrame goodData 0).run sourceBefore =
    (Source.cdToMem goodFrame sourceTy 68 2).run sourceBefore := by
  simp only [sourceCopy_run,good_entry]

theorem good_source_result : ((sourceCopy goodFrame goodData 0).run sourceBefore).1 =
    .ok (.val (.memRef rfl 2)) := by
  rw [good_source_run,(Source.cdToMem_array_run (σ := .bool)),validated]
  rfl

theorem good_heap_related : Related ((sourceCopy goodFrame goodData 0).run sourceBefore).2.2.heap
    2 BoolArrayControls.lowered.heap (aliasTarget.alloc (object aliasTarget.H values room)).2 :=
  (successful_import sourceBefore aliasTarget goodFrame selector goodData rfl rfl good_entry validated).2.2

theorem entry_joint_second :
    ((do let _ ← sourceCopy goodFrame goodData 0
         Source.readLoc goodFrame (.mem (τ := .bool) 2 1)) : Source.EM E caller _).run sourceBefore =
      (.ok (.bool false),((sourceCopy goodFrame goodData 0).run sourceBefore).2) ∧
    BoolArrayControls.lowered.heap.readAddr (.index (aliasTarget.alloc (object aliasTarget.H values room)).2
      ArrTy.dyn (uintOfNat 1)) = some false := by
  refine ⟨?_,joint_second.2⟩
  have actual := joint_second.1
  rw [Source.Hoare.run_bind] at actual ⊢
  simpa only [good_source_run] using actual

theorem dirty_import : lowerEntry (E := E) aliasTarget dirtyFrame selector dirtyData rfl rfl 0 =
    .error (.revert []) := by
  rw [lowerEntry_of_ok aliasTarget dirtyFrame selector dirtyData rfl rfl dirty_entry]
  exact dirty_phase

theorem dirty_source_run : (sourceCopy dirtyFrame dirtyData 0).run sourceBefore =
    (.error (.revert []),sourceBefore) := by
  simp only [sourceCopy_run,dirty_entry]
  exact BoolArrayControls.dirty_source

def shortData : Roadmap.Bytes := dirtyData.take 128
def shortFrame : Source.Fr := {frame with cd := selector ++ shortData}

theorem truncated_import : lowerEntry (E := E) aliasTarget shortFrame selector shortData rfl rfl 0 =
    .error (.revert []) :=
  lowerEntry_of_error aliasTarget shortFrame selector shortData rfl rfl BoolArrayControls.truncated_entry

theorem truncated_source_run : (sourceCopy shortFrame shortData 0).run sourceBefore =
    (.error (.revert []),sourceBefore) := by
  simp only [sourceCopy_run,shortData,BoolArrayControls.truncated_entry]

theorem wrong_truncated_allocation :
    ((sourceCopy shortFrame shortData 0).run sourceBefore).2.2.heap.next ≠ 3 := by
  rw [truncated_source_run]
  decide

theorem empty_import : lowerEntry (E := E) aliasTarget emptyFrame selector emptyData rfl rfl 0 =
    .ok (BoolArrays.lower aliasTarget [] emptyRoom) := by
  rw [lowerEntry_of_ok aliasTarget emptyFrame selector emptyData rfl rfl empty_entry]
  exact empty_phase

theorem empty_source_related : Related ((sourceCopy emptyFrame emptyData 0).run sourceBefore).2.2.heap
    2 (BoolArrays.lower aliasTarget [] emptyRoom).heap
      (aliasTarget.alloc (object aliasTarget.H [] emptyRoom)).2 :=
  (successful_import sourceBefore aliasTarget emptyFrame selector emptyData rfl rfl empty_entry rfl).2.2

theorem wrong_dirty_success : lowerEntry (E := E) aliasTarget dirtyFrame selector dirtyData rfl rfl 0 ≠ .ok BoolArrayControls.lowered := by
  rw [dirty_import]
  intro impossible
  cases impossible

theorem good_not_refused (halt : Source.Halt) :
    lowerEntry (E := E) aliasTarget goodFrame selector goodData rfl rfl 0 ≠ .error halt := by
  rw [good_import]
  intro impossible
  cases impossible

end Solidity.Backend.Aggregates.BoolArrayEntryControls
