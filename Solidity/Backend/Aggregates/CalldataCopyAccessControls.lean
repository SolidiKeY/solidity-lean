import Solidity.Source.CalldataCopyAccess
import Solidity.Backend.Aggregates.CalldataCopyControls

/-! Actual copied-element origin, extent and exception ordering controls.
The complete original caller and the actual post-copy caller differ. -/
namespace Solidity.Backend.Aggregates.CalldataCopyAccessControls
open Solidity ByteParameterControls NestedCalldataControls CalldataCopyControls

theorem extent_derived : [Source.Val.bool (D := E.layout) true,.bool false].length = 2 :=
  Source.cdToMem_array_length copyFrame .bool 0 2 decoded_prefix

theorem second_decoder_and_read : ∃ bound : 1 < [Source.Val.bool (D := E.layout) true,.bool false].length,
    Source.decodeWord E.layout (Source.cdWordAt copyFrame (0+32*1)) .bool =
      .ok ([Source.Val.bool (D := E.layout) true,.bool false].get ⟨1,bound⟩) ∧
    ((do let _ ← copied
         Source.readLoc copyFrame (.mem (τ := .bool) 2 1)) : Source.EM E caller _).run sourceBefore =
      (.ok (.bool false),(copied.run sourceBefore).2) := by
  obtain ⟨bound,_,position,actual⟩ := Source.cdToMem_array_read_run copyFrame .bool 0 2
    sourceBefore decoded_prefix ⟨1,by decide⟩
  exact ⟨bound,position,actual⟩

theorem bounds_after_copy :
    ((do let _ ← copied
         Source.readLoc copyFrame (.mem (τ := .bool) 2 2)) : Source.EM E caller _).run sourceBefore =
      (.error (.revert (Source.panicData .index)),(copied.run sourceBefore).2) :=
  Source.cdToMem_array_read_out_run copyFrame .bool 0 2 sourceBefore decoded_prefix 2 (by decide)

theorem bounds_keeps_allocation :
    (((do let _ ← copied
          Source.readLoc copyFrame (.mem (τ := .bool) 2 2)) : Source.EM E caller _).run sourceBefore).2.2.heap.next = 3 := by
  rw [bounds_after_copy,copy_success]
  rfl

theorem dirty_before_bounds :
    ((do let _ ← Source.cdToMem copyFrame (.array .memory .bool none) 0 3
         Source.readLoc copyFrame (.mem (τ := .bool) 2 99)) : Source.EM E caller _).run sourceBefore =
      (.error (.revert []),sourceBefore) :=
  Source.cdToMem_array_read_failure copyFrame .bool 0 3 sourceBefore 99 (.revert []) dirty_validation

theorem offset_validation : (List.range 1).mapM (fun j =>
    Source.decodeWord E.layout (Source.cdWordAt copyFrame (32+32*j)) .bool) = .ok [.bool false] := by
  change Source.decodeWord E.layout (Source.cdWordAt copyFrame 32) .bool >>= _ = _
  rw [second_word]
  rfl

theorem nonzero_origin_read :
    ((do let _ ← Source.cdToMem copyFrame (.array .memory .bool none) 32 1
         Source.readLoc copyFrame (.mem (τ := .bool) 2 0)) : Source.EM E caller _).run sourceBefore =
      (.ok (.bool false),((Source.cdToMem copyFrame (.array .memory .bool none) 32 1).run sourceBefore).2) := by
  obtain ⟨_,_,_,actual⟩ := Source.cdToMem_array_read_run copyFrame .bool 32 1
    sourceBefore offset_validation ⟨0,by decide⟩
  exact actual

theorem wrong_origin_read :
    (((do let _ ← copied; Source.readLoc copyFrame (.mem (τ := .bool) 2 0)) : Source.EM E caller _).run sourceBefore).1 ≠
      .ok (.bool false) := by
  rw [copy_then_read_first]
  intro impossible
  cases impossible

theorem empty_copy_then_read :
    ((do let _ ← Source.cdToMem copyFrame (.array .memory .bool none) 96 0
         Source.readLoc copyFrame (.mem (τ := .bool) 2 0)) : Source.EM E caller _).run sourceBefore =
      (.error (.revert (Source.panicData .index)),
        ((Source.cdToMem copyFrame (.array .memory .bool none) 96 0).run sourceBefore).2) :=
  Source.cdToMem_array_read_out_run copyFrame .bool 96 0 sourceBefore rfl 0 (by decide)

theorem wrong_post_copy_rollback :
    (((do let _ ← copied
          Source.readLoc copyFrame (.mem (τ := .bool) 2 2)) : Source.EM E caller _).run sourceBefore).2.2.heap.next ≠
      sourceBefore.2.heap.next := by
  rw [bounds_keeps_allocation]
  decide

end Solidity.Backend.Aggregates.CalldataCopyAccessControls
