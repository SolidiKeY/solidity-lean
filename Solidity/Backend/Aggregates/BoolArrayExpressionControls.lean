import Solidity.Backend.Aggregates.BoolArrayExpression
import Solidity.Backend.Aggregates.BoolArrayEntryControls

/-! Actual typed conversion, caller-tail scope and Source-budget controls.
A value snapshot succeeding does not imply exhausted expression execution. -/
namespace Solidity.Backend.Aggregates.BoolArrayExpressionControls
open Solidity ByteParameterControls NestedCalldataControls BoolArrays BoolArrayControls BoolArrayEntry BoolArrayEntryControls BoolArrayExpression

theorem good_scoped_run : (scopedCopy ByteSliceControls.G goodFrame 2 goodData 0).run sourceBefore =
    (sourceCopy goodFrame goodData 0).run sourceBefore :=
  scopedCopy_run ByteSliceControls.G goodFrame 0 goodData 0 sourceBefore

theorem good_result : ((scopedCopy ByteSliceControls.G goodFrame 2 goodData 0).run sourceBefore).1 =
    .ok (.val (.memRef rfl 2)) := by
  rw [good_scoped_run]
  exact good_source_result

theorem caller_locals_restored :
    ((scopedCopy ByteSliceControls.G goodFrame 2 goodData 0).run sourceBefore).2.1 = sourceLocals := by
  rw [good_scoped_run,good_source_run,(Source.cdToMem_array_run (σ := .bool)),validated]
  rfl

theorem heap_related : Related ((scopedCopy ByteSliceControls.G goodFrame 2 goodData 0).run sourceBefore).2.2.heap
    2 BoolArrayControls.lowered.heap (aliasTarget.alloc (object aliasTarget.H values room)).2 := by
  rw [good_scoped_run]
  exact good_heap_related

theorem joint_second :
    ((do let _ ← scopedCopy ByteSliceControls.G goodFrame 2 goodData 0
         Source.readLoc goodFrame (.mem (τ := .bool) 2 1)) : Source.EM E caller _).run sourceBefore =
      (.ok (.bool false),((scopedCopy ByteSliceControls.G goodFrame 2 goodData 0).run sourceBefore).2) ∧
    BoolArrayControls.lowered.heap.readAddr (.index (aliasTarget.alloc (object aliasTarget.H values room)).2
      ArrTy.dyn (uintOfNat 1)) = some false := by
  refine ⟨?_,entry_joint_second.2⟩
  rw [Source.Hoare.run_bind,good_scoped_run,good_source_run,(Source.cdToMem_array_run (σ := .bool)),validated]
  rfl

theorem zero_budget : (scopedCopy ByteSliceControls.G goodFrame 0 goodData 0).run sourceBefore =
    (.error .timeout,sourceBefore) := by
  rw [scopedCopy_low_run ByteSliceControls.G goodFrame 0 (by decide) goodData 0 sourceBefore,good_entry]

theorem one_budget : (scopedCopy ByteSliceControls.G goodFrame 1 goodData 0).run sourceBefore =
    (.error .timeout,sourceBefore) := by
  rw [scopedCopy_low_run ByteSliceControls.G goodFrame 1 (by decide) goodData 0 sourceBefore,good_entry]

theorem low_no_allocation :
    ((scopedCopy ByteSliceControls.G goodFrame 1 goodData 0).run sourceBefore).2.2.heap.next = 2 := by
  rw [one_budget]
  rfl

theorem phase_vs_exhaustion :
    lowerEntry (E := E) aliasTarget goodFrame selector goodData rfl rfl 0 = .ok BoolArrayControls.lowered ∧
    (scopedCopy ByteSliceControls.G goodFrame 0 goodData 0).run sourceBefore = (.error .timeout,sourceBefore) :=
  ⟨good_import,zero_budget⟩

theorem dirty_zero : (scopedCopy ByteSliceControls.G dirtyFrame 0 dirtyData 0).run sourceBefore =
    (.error .timeout,sourceBefore) := by
  rw [scopedCopy_low_run ByteSliceControls.G dirtyFrame 0 (by decide) dirtyData 0 sourceBefore,dirty_entry]

theorem dirty_two : (scopedCopy ByteSliceControls.G dirtyFrame 2 dirtyData 0).run sourceBefore =
    (.error (.revert []),sourceBefore) := by
  rw [scopedCopy_run ByteSliceControls.G dirtyFrame 0 dirtyData 0 sourceBefore]
  exact dirty_source_run

theorem short_zero : (scopedCopy ByteSliceControls.G shortFrame 0 shortData 0).run sourceBefore =
    (.error (.revert []),sourceBefore) := by
  rw [scopedCopy_low_run ByteSliceControls.G shortFrame 0 (by decide) shortData 0 sourceBefore]
  simp only [BoolArrayEntryControls.shortData,BoolArrayControls.truncated_entry]

theorem short_two : (scopedCopy ByteSliceControls.G shortFrame 2 shortData 0).run sourceBefore =
    (.error (.revert []),sourceBefore) := by
  rw [scopedCopy_run ByteSliceControls.G shortFrame 0 shortData 0 sourceBefore]
  exact truncated_source_run

theorem empty_related : Related ((scopedCopy ByteSliceControls.G emptyFrame 2 emptyData 0).run sourceBefore).2.2.heap
    2 (BoolArrays.lower aliasTarget [] emptyRoom).heap
      (aliasTarget.alloc (object aliasTarget.H [] emptyRoom)).2 := by
  rw [scopedCopy_run ByteSliceControls.G emptyFrame 0 emptyData 0 sourceBefore]
  exact empty_source_related

theorem wrong_timeout_revert :
    ((scopedCopy ByteSliceControls.G goodFrame 0 goodData 0).run sourceBefore).1 ≠ .error (.revert []) := by
  rw [zero_budget]
  intro impossible
  cases impossible

theorem protected_old_objects :
    ((scopedCopy ByteSliceControls.G goodFrame 2 goodData 0).run sourceBefore).2.2.heap.get 0 = sourceHeap.get 0 ∧
    ((scopedCopy ByteSliceControls.G goodFrame 2 goodData 0).run sourceBefore).2.2.heap.get 1 = sourceHeap.get 1 := by
  rw [good_scoped_run,good_source_run,(Source.cdToMem_array_run (σ := .bool)),validated]
  exact ⟨rfl,rfl⟩

end Solidity.Backend.Aggregates.BoolArrayExpressionControls
