import Solidity.Source.CalldataCopy
import Solidity.Backend.Aggregates.NestedCalldataControls

/-! G18.05 inhabited complete copy outcomes. A dirty third bool stops
a full copy after two valid decodes, before any allocation. Existing distinct heap
objects and aliased caller locals remain observable. -/
namespace Solidity.Backend.Aggregates.CalldataCopyControls
open Solidity ByteParameterControls NestedCalldataControls

def copyFrame : Source.Fr := {frame with cd := word 1 ++ word 0 ++ word 2}
def copied : Source.EM E caller (Source.RVal E.layout (.array .memory .bool none)) :=
  Source.cdToMem copyFrame (.array .memory .bool none) 0 2

theorem first_word : Source.cdWordAt copyFrame 0 = 1 := by decide +kernel
theorem second_word : Source.cdWordAt copyFrame 32 = 0 := by decide +kernel
theorem dirty_word : Source.cdWordAt copyFrame 64 = 2 := by decide +kernel

theorem decoded_prefix : (List.range 2).mapM (fun j =>
    Source.decodeWord E.layout (Source.cdWordAt copyFrame (0+32*j)) .bool) =
      .ok [.bool true,.bool false] := by
  simp only [List.range_succ,List.range_zero,List.cons_append,List.nil_append,List.mapM_cons,List.mapM_nil]
  rw [show 0+32*0 = 0 from rfl,first_word,show 0+32*1 = 32 from rfl,second_word]
  rfl

theorem copy_success : copied.run sourceBefore =
    (.ok (.val (.memRef rfl 2)),
      (sourceLocals,{sourceState with heap := (sourceHeap.alloc
        ⟨.array .memory .bool none,Source.Data.array 2 (fun _ h => nomatch h)
          (fun k => .val ([Source.Val.bool true,.bool false].get k))⟩).1})) := by
  unfold copied
  rw [(Source.cdToMem_array_run (σ := .bool)),decoded_prefix]
  rfl

theorem copied_order : (copied.run sourceBefore).2.2.heap.get 2 =
    some ⟨.array .memory .bool none,Source.Data.array 2 (fun _ h => nomatch h)
      (fun k => .val ([Source.Val.bool true,.bool false].get k))⟩ := by
  rw [copy_success]
  rfl

theorem kept_aliases : (copied.run sourceBefore).2.1 = sourceLocals := by
  rw [copy_success]

theorem kept_old_objects : (copied.run sourceBefore).2.2.heap.get 0 = sourceHeap.get 0 ∧
    (copied.run sourceBefore).2.2.heap.get 1 = sourceHeap.get 1 := by
  rw [copy_success]
  exact ⟨rfl,rfl⟩

theorem dirty_validation : (List.range 3).mapM (fun j =>
    Source.decodeWord E.layout (Source.cdWordAt copyFrame (0+32*j)) .bool) =
      .error (.revert []) := by
  simp only [List.range_succ,List.range_zero,List.cons_append,List.nil_append,List.mapM_cons,List.mapM_nil]
  rw [show 0+32*0 = 0 from rfl,first_word,show 0+32*1 = 32 from rfl,second_word,
    show 0+32*2 = 64 from rfl,dirty_word]
  rfl

theorem dirty_copy_atomic :
    (Source.cdToMem copyFrame (.array .memory .bool none) 0 3).run sourceBefore =
      (.error (.revert []),sourceBefore) :=
  Source.cdToMem_array_failure copyFrame .bool 0 3 sourceBefore (.revert []) dirty_validation

theorem empty_copy_allocates :
    ((Source.cdToMem copyFrame (.array .memory .bool none) 96 0).run sourceBefore).2.2.heap.next = 3 := by
  rw [(Source.cdToMem_array_run (σ := .bool))]
  rfl

theorem wrong_failure_halt :
    (Source.cdToMem copyFrame (.array .memory .bool none) 0 3).run sourceBefore ≠
      (.error (.revert (Source.panicData .index)),sourceBefore) := by
  rw [dirty_copy_atomic]
  intro impossible
  have bytes := Source.Halt.revert.inj (Except.error.inj (congrArg Prod.fst impossible))
  have nonempty : Source.panicData .index ≠ [] := by decide +kernel
  exact nonempty bytes.symm

theorem wrong_partial_allocation :
    ((Source.cdToMem copyFrame (.array .memory .bool none) 0 3).run sourceBefore).2.2.heap.next ≠ 3 := by
  rw [dirty_copy_atomic]
  decide

theorem actual_conversion_failure :
    (Source.convRV copyFrame 7 (.array .memory .bool none)
      (.val (.cdRef (τ := .array .calldata .bool none) rfl 0 3))).run sourceBefore =
      (.error (.revert []),sourceBefore) := by
  rw [Source.convRV_cdArray]
  exact dirty_copy_atomic

theorem copy_then_read_first :
    ((do let _ ← copied
         Source.readLoc copyFrame (.mem (τ := .bool) 2 0)) : Source.EM E caller _).run sourceBefore =
      (.ok (.bool true),(copied.run sourceBefore).2) := by
  rw [Source.Hoare.run_bind,copy_success]
  rfl

theorem copy_then_read_second :
    ((do let _ ← copied
         Source.readLoc copyFrame (.mem (τ := .bool) 2 1)) : Source.EM E caller _).run sourceBefore =
      (.ok (.bool false),(copied.run sourceBefore).2) := by
  rw [Source.Hoare.run_bind,copy_success]
  rfl

theorem wrong_order :
    ((do let _ ← copied
         Source.readLoc copyFrame (.mem (τ := .bool) 2 0)) : Source.EM E caller _).run sourceBefore ≠
      (.ok (.bool false),(copied.run sourceBefore).2) := by
  rw [copy_then_read_first]
  intro impossible
  cases congrArg Prod.fst impossible

end Solidity.Backend.Aggregates.CalldataCopyControls
