import Solidity.Backend.Passes.AllocatedReferenceReadControls
import Solidity.Backend.Passes.ReturnedMemoryCaptureControls
import Solidity.Backend.Passes.MemoryAssociationControls
import Solidity.Backend.Passes.MemoryJoinedOutputControls
import Solidity.Backend.Passes.MemoryJoinFrameControls
import Solidity.Backend.Passes.MemoryJoinedAllocationControls

/-! Guard stale allocator maps, wrong fresh-reference/cursor values and saved-tail
corruption after public joined allocation. Reuse existing compiler certificates;
this module makes no native ByteWorld or full Source/G24 adequacy claim. -/
namespace Solidity.Backend.Passes.AuditJoinedAllocation
open Evm Evm.Memory Evm.Compiler
open Solidity.Backend.Passes

theorem joint :
    (Compilation.memory AllocatingControls.allocationStage).Input 1 6
      AllocatingControls.initialBase (State.init Controls.Fixture.C)
      AllocatingControls.initialMachine ∧
    Memory.allocationCostProg (ReachabilityControls.populatedBuilder.join
      MemoryJoinCost.Controls.appendAllocation) (State.init Controls.Fixture.C) = 9 ∧
    (∃ machine : Machine, machine = AllocatingControls.initialMachine) :=
  ⟨AllocatingControls.prefix_input, MemoryJoinCost.Controls.total_cost,
    AllocatingControls.initialMachine, rfl⟩

-- Retain the original jointly selected middle state/map and every-tail suffix input.
def reached_joint := MemoryJoinCost.Controls.reached_budget
def whole_some := @Solidity.Backend.Passes.MemoryJoinedAllocation.Controls.whole_some
def whole_public := @Solidity.Backend.Passes.MemoryJoinedAllocation.Controls.whole_public
def whole_tail := @Solidity.Backend.Passes.MemoryJoinedAllocation.Controls.whole_tail
def complete_result := @Solidity.Backend.Passes.MemoryJoinedAllocation.Controls.complete_result
def wrong_cursor := @Solidity.Backend.Passes.MemoryJoinedAllocation.Controls.wrong_cursor
def wrong_new_reference := @Solidity.Backend.Passes.MemoryJoinedAllocation.Controls.wrong_new_reference
def stale_initial_map := @Solidity.Backend.Passes.MemoryJoinedAllocation.Controls.stale_initial_map
def corrupted_saved_tail := @Solidity.Backend.Passes.MemoryJoinedAllocation.Controls.corrupted_saved_tail

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.joint

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.reached_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.reached_joint

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.whole_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.whole_some

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.whole_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.whole_public

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.whole_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.whole_tail

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.complete_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.complete_result

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.wrong_cursor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.wrong_cursor

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.wrong_new_reference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.wrong_new_reference

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.stale_initial_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.stale_initial_map

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.corrupted_saved_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.corrupted_saved_tail

-- Resolve actual private originals; anonymous exact-type checks do not re-export them.
macro "joinedAllocationPrivate%" n:ident : term =>
  pure (Lean.mkIdentFrom n ((Lean.Name.num `_private.Solidity.Backend.Passes.MemoryJoinedAllocationControls 0) ++
    `Solidity.Backend.Passes.MemoryJoinedAllocation.Controls ++ n.getId))
example : (joinedAllocationPrivate% readCell) 5 (run MemoryJoinedAllocation.Controls.wholeCode.code AllocatingControls.initialMachine) = some 21 := joinedAllocationPrivate% cell0
example : (joinedAllocationPrivate% readCell) 4 (run MemoryJoinedAllocation.Controls.wholeCode.code AllocatingControls.initialMachine) = some 0 := joinedAllocationPrivate% cell1
example : (joinedAllocationPrivate% readCell) 2 (run MemoryJoinedAllocation.Controls.wholeCode.code AllocatingControls.initialMachine) = some 16 := joinedAllocationPrivate% cell2
example : (joinedAllocationPrivate% readCell) 3 (run MemoryJoinedAllocation.Controls.wholeCode.code AllocatingControls.initialMachine) = some 16 := joinedAllocationPrivate% cell3
example : (joinedAllocationPrivate% readCell) 1 (run MemoryJoinedAllocation.Controls.wholeCode.code AllocatingControls.initialMachine) = some 19 := joinedAllocationPrivate% cell4
example : (joinedAllocationPrivate% readCell) 6 (run MemoryJoinedAllocation.Controls.wholeCode.code AllocatingControls.initialMachine) = some 0 := joinedAllocationPrivate% cell5
example : (joinedAllocationPrivate% readCell) 16 (run MemoryJoinedAllocation.Controls.wholeCode.code AllocatingControls.initialMachine) = some 2 := joinedAllocationPrivate% cell6
example : (joinedAllocationPrivate% readCell) 17 (run MemoryJoinedAllocation.Controls.wholeCode.code AllocatingControls.initialMachine) = some 7 := joinedAllocationPrivate% cell7
example : (joinedAllocationPrivate% readCell) 18 (run MemoryJoinedAllocation.Controls.wholeCode.code AllocatingControls.initialMachine) = some 9 := joinedAllocationPrivate% cell8
example : (joinedAllocationPrivate% readCell) 19 (run MemoryJoinedAllocation.Controls.wholeCode.code AllocatingControls.initialMachine) = some 1 := joinedAllocationPrivate% cell9
example : (joinedAllocationPrivate% readCell) 20 (run MemoryJoinedAllocation.Controls.wholeCode.code AllocatingControls.initialMachine) = some 4 := joinedAllocationPrivate% cell10
example : (joinedAllocationPrivate% readCell) 21 (run MemoryJoinedAllocation.Controls.wholeCode.code AllocatingControls.initialMachine) = some 3 := joinedAllocationPrivate% cell11
example : (joinedAllocationPrivate% readCell) 22 (run MemoryJoinedAllocation.Controls.wholeCode.code AllocatingControls.initialMachine) = some 0 := joinedAllocationPrivate% cell12
example : (joinedAllocationPrivate% readCell) 23 (run MemoryJoinedAllocation.Controls.wholeCode.code AllocatingControls.initialMachine) = some 0 := joinedAllocationPrivate% cell13
example : (joinedAllocationPrivate% readCell) 24 (run MemoryJoinedAllocation.Controls.wholeCode.code AllocatingControls.initialMachine) = some 0 := joinedAllocationPrivate% cell14
example : (joinedAllocationPrivate% readCell) 0 (run MemoryJoinedAllocation.Controls.wholeCode.code AllocatingControls.initialMachine) = some 25 := joinedAllocationPrivate% cell15

/-- info: cell0: [propext, Quot.sound, Classical.choice]
---
info: cell1: [propext, Quot.sound, Classical.choice]
---
info: cell2: [propext, Quot.sound, Classical.choice]
---
info: cell3: [propext, Quot.sound, Classical.choice]
---
info: cell4: [propext, Quot.sound, Classical.choice]
---
info: cell5: [propext, Quot.sound, Classical.choice]
---
info: cell6: [propext, Quot.sound, Classical.choice]
---
info: cell7: [propext, Quot.sound, Classical.choice]
---
info: cell8: [propext, Quot.sound, Classical.choice]
---
info: cell9: [propext, Quot.sound, Classical.choice]
---
info: cell10: [propext, Quot.sound, Classical.choice]
---
info: cell11: [propext, Quot.sound, Classical.choice]
---
info: cell12: [propext, Quot.sound, Classical.choice]
---
info: cell13: [propext, Quot.sound, Classical.choice]
---
info: cell14: [propext, Quot.sound, Classical.choice]
---
info: cell15: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
run_cmd do
  for short in [`cell0, `cell1, `cell2, `cell3, `cell4, `cell5, `cell6, `cell7, `cell8, `cell9, `cell10, `cell11, `cell12, `cell13, `cell14, `cell15] do
    let name := (Lean.Name.num `_private.Solidity.Backend.Passes.MemoryJoinedAllocationControls 0) ++
      `Solidity.Backend.Passes.MemoryJoinedAllocation.Controls ++ short
    let axes ← Lean.collectAxioms name
    Lean.logInfo m!"{short}: {axes}"

namespace CostControls
/-! Guard omitted suffix allocation cost and charging/executing an unreachable
allocation after typed revert. Reuse actual public joins and source runs. -/
def prefix_public := @Solidity.Backend.Passes.MemoryJoinCost.Controls.prefix_public
def suffix_public := @Solidity.Backend.Passes.MemoryJoinCost.Controls.suffix_public
def suffix_cost := @Solidity.Backend.Passes.MemoryJoinCost.Controls.suffix_cost
def total_cost := @Solidity.Backend.Passes.MemoryJoinCost.Controls.total_cost
def reached_budget := @Solidity.Backend.Passes.MemoryJoinCost.Controls.reached_budget
def complete_prefix := @Solidity.Backend.Passes.MemoryJoinCost.Controls.complete_prefix
def wrong_total := @Solidity.Backend.Passes.MemoryJoinCost.Controls.wrong_total
def fail_source := @Solidity.Backend.Passes.MemoryJoinCost.Controls.fail_source
def skipped_allocation := @Solidity.Backend.Passes.MemoryJoinCost.Controls.skipped_allocation
def failed_public := @Solidity.Backend.Passes.MemoryJoinCost.Controls.failed_public

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.CostControls.prefix_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.CostControls.prefix_public

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.CostControls.suffix_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.CostControls.suffix_public

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.CostControls.suffix_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.CostControls.suffix_cost

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.CostControls.total_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.CostControls.total_cost

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.CostControls.reached_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.CostControls.reached_budget

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.CostControls.complete_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.CostControls.complete_prefix

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.CostControls.wrong_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.CostControls.wrong_total

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.CostControls.fail_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.CostControls.fail_source

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.CostControls.skipped_allocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.CostControls.skipped_allocation

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.CostControls.failed_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.CostControls.failed_public

macro "joinCostPrivate%" n:ident : term =>
  pure (Lean.mkIdentFrom n ((Lean.Name.num `_private.Solidity.Backend.Passes.MemoryJoinCostControls 0) ++
    `Solidity.Backend.Passes.MemoryJoinCost.Controls ++ n.getId))
example : (joinCostPrivate% readCell) 4 (run AllocatingControls.allocationStage.code AllocatingControls.initialMachine) = some 0 := joinCostPrivate% cell0
example : (joinCostPrivate% readCell) 2 (run AllocatingControls.allocationStage.code AllocatingControls.initialMachine) = some 16 := joinCostPrivate% cell1
example : (joinCostPrivate% readCell) 3 (run AllocatingControls.allocationStage.code AllocatingControls.initialMachine) = some 16 := joinCostPrivate% cell2
example : (joinCostPrivate% readCell) 1 (run AllocatingControls.allocationStage.code AllocatingControls.initialMachine) = some 19 := joinCostPrivate% cell3
example : (joinCostPrivate% readCell) 17 (run AllocatingControls.allocationStage.code AllocatingControls.initialMachine) = some 7 := joinCostPrivate% cell4
example : (joinCostPrivate% readCell) 18 (run AllocatingControls.allocationStage.code AllocatingControls.initialMachine) = some 9 := joinCostPrivate% cell5
example : (joinCostPrivate% readCell) 20 (run AllocatingControls.allocationStage.code AllocatingControls.initialMachine) = some 4 := joinCostPrivate% cell6
example : (joinCostPrivate% readCell) 0 (run AllocatingControls.allocationStage.code AllocatingControls.initialMachine) = some 21 := joinCostPrivate% cell7

/-- info: cell0: [propext, Quot.sound, Classical.choice]
---
info: cell1: [propext, Quot.sound, Classical.choice]
---
info: cell2: [propext, Quot.sound, Classical.choice]
---
info: cell3: [propext, Quot.sound, Classical.choice]
---
info: cell4: [propext, Quot.sound, Classical.choice]
---
info: cell5: [propext, Quot.sound, Classical.choice]
---
info: cell6: [propext, Quot.sound, Classical.choice]
---
info: cell7: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
run_cmd do
  for short in [`cell0, `cell1, `cell2, `cell3, `cell4, `cell5, `cell6, `cell7] do
    let name := (Lean.Name.num `_private.Solidity.Backend.Passes.MemoryJoinCostControls 0) ++
      `Solidity.Backend.Passes.MemoryJoinCost.Controls ++ short
    let axes ← Lean.collectAxioms name
    Lean.logInfo m!"{short}: {axes}"
end CostControls

namespace FrameControls
/-! Guard prefix-only frame admission, summing sequential scoped maxima, and
mistaking zero reached allocation for permission to drop static frame needs. -/
theorem joint :
    Memory.StateRepr 1 1 6 (Frag.init []) (State.init Controls.Fixture.C)
      AllocatingControls.initialBase AllocatingControls.initialMachine ∧
    Memory.AllocationInput 1 6
      (Memory.allocationCostProg (ReachabilityControls.populatedBuilder.join
        MemoryJoinCost.Controls.appendAllocation) (State.init Controls.Fixture.C))
      (State.init Controls.Fixture.C) AllocatingControls.initialBase AllocatingControls.initialMachine ∧
    (∃ joined : Memory.CompiledProg 1 (Frag.init [])
      (ReachabilityControls.populatedBuilder.join MemoryJoinCost.Controls.appendAllocation),
      joined = MemoryJoinedAllocation.Controls.wholeCode) :=
  ⟨AllocatingControls.initial_repr.1, MemoryJoinFrame.Controls.actual_budget,
    MemoryJoinedAllocation.Controls.wholeCode, rfl⟩
def actual_budget := @Solidity.Backend.Passes.MemoryJoinFrame.Controls.actual_budget
def admitted_execution := @Solidity.Backend.Passes.MemoryJoinFrame.Controls.admitted_execution
def prefix_only_frame_is_insufficient := @Solidity.Backend.Passes.MemoryJoinFrame.Controls.prefix_only_frame_is_insufficient
def scoped_maximum := @Solidity.Backend.Passes.MemoryJoinFrame.Controls.scoped_maximum
def scoped_public := @Solidity.Backend.Passes.MemoryJoinFrame.Controls.scoped_public
def scoped_slot_reuse := @Solidity.Backend.Passes.MemoryJoinFrame.Controls.scoped_slot_reuse
def unreachable_public := @Solidity.Backend.Passes.MemoryJoinFrame.Controls.unreachable_public
def unreachable_frame_retained := @Solidity.Backend.Passes.MemoryJoinFrame.Controls.unreachable_frame_retained
def unreachable_frame_refused := @Solidity.Backend.Passes.MemoryJoinFrame.Controls.unreachable_frame_refused
def unreachable_other_fields := @Solidity.Backend.Passes.MemoryJoinFrame.Controls.unreachable_other_fields

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.FrameControls.joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.FrameControls.joint

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.FrameControls.actual_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.FrameControls.actual_budget

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.FrameControls.admitted_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.FrameControls.admitted_execution

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.FrameControls.prefix_only_frame_is_insufficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.FrameControls.prefix_only_frame_is_insufficient

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.FrameControls.scoped_maximum' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.FrameControls.scoped_maximum

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.FrameControls.scoped_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.FrameControls.scoped_public

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.FrameControls.scoped_slot_reuse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.FrameControls.scoped_slot_reuse

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.FrameControls.unreachable_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.FrameControls.unreachable_public

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.FrameControls.unreachable_frame_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.FrameControls.unreachable_frame_retained

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.FrameControls.unreachable_frame_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.FrameControls.unreachable_frame_refused

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.FrameControls.unreachable_other_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.FrameControls.unreachable_other_fields
end FrameControls

namespace TripleAdmission
/-! Guard assuming a third-stage frame/budget, sharing stage maps only after
choosing the caller tail, or reading an old length after fresh allocation. -/
open AllocatingControls MemoryJoinCost.Controls

theorem joint :
    Memory.StateRepr 1 1 7 (Frag.init []) (State.init Controls.Fixture.C) initialBase initialMachine ∧
    Memory.AllocationInput 1 7
      (Memory.allocationCostProg (ReachabilityControls.populatedBuilder.join
        (appendAllocation.join MemoryTripleAdmission.Controls.capture)) (State.init Controls.Fixture.C))
      (State.init Controls.Fixture.C) initialBase initialMachine ∧
    Memory.AllocationInput 1 7
      (Memory.allocationCostProg (ReachabilityControls.populatedBuilder.join
        (appendAllocation.join MemoryTripleAdmission.Controls.badCapture)) (State.init Controls.Fixture.C))
      (State.init Controls.Fixture.C) initialBase initialMachine ∧
    (∃ whole : Memory.CompiledProg 1 (Frag.init [])
      (ReachabilityControls.populatedBuilder.join
        (appendAllocation.join MemoryTripleAdmission.Controls.capture)), True) ∧
    (∃ tail : List Word, tail = []) := by
  refine ⟨TripleControls.initial_repr7.1, MemoryTripleAdmission.Controls.budget,
    MemoryTripleAdmission.Controls.bad_budget, ?_, [], rfl⟩
  obtain ⟨whole,_⟩ := MemoryJoinedOutput.Controls.public_shared
  exact ⟨whole,True.intro⟩
def length_source := @Solidity.Backend.Passes.MemoryTripleAdmission.Controls.length_source
def capture_source := @Solidity.Backend.Passes.MemoryTripleAdmission.Controls.capture_source
def capture_public := @Solidity.Backend.Passes.MemoryTripleAdmission.Controls.capture_public
def total_cost := @Solidity.Backend.Passes.MemoryTripleAdmission.Controls.total_cost
def budget := @Solidity.Backend.Passes.MemoryTripleAdmission.Controls.budget
def shared := @Solidity.Backend.Passes.MemoryTripleAdmission.Controls.shared
def complete_result := @Solidity.Backend.Passes.MemoryTripleAdmission.Controls.complete_result
def wrong_old_length := @Solidity.Backend.Passes.MemoryTripleAdmission.Controls.wrong_old_length
def third_frame_required := @Solidity.Backend.Passes.MemoryTripleAdmission.Controls.third_frame_required
def bad_public := @Solidity.Backend.Passes.MemoryTripleAdmission.Controls.bad_public
def bad_source := @Solidity.Backend.Passes.MemoryTripleAdmission.Controls.bad_source
def bad_budget := @Solidity.Backend.Passes.MemoryTripleAdmission.Controls.bad_budget
def reached_third_failure := @Solidity.Backend.Passes.MemoryTripleAdmission.Controls.reached_third_failure

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.joint

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.length_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.length_source

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.capture_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.capture_source

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.capture_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.capture_public

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.total_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.total_cost

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.budget

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.shared

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.complete_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.complete_result

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.wrong_old_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.wrong_old_length

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.third_frame_required' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.third_frame_required

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.bad_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.bad_public

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.bad_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.bad_source

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.bad_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.bad_budget

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.reached_third_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.TripleAdmission.reached_third_failure

-- Exact original private observations; do not re-export private declarations.
macro "tripleAdmissionPrivate%" n:ident : term =>
  pure (Lean.mkIdentFrom n ((Lean.Name.num `_private.Solidity.Backend.Passes.MemoryTripleAdmissionControls 0) ++
    `Solidity.Backend.Passes.MemoryTripleAdmission.Controls ++ n.getId))
example : (tripleAdmissionPrivate% readCell) 6 (run MemoryTripleAdmission.Controls.code AllocatingControls.initialMachine) = some 3 := tripleAdmissionPrivate% cell0
example : (tripleAdmissionPrivate% readCell) 5 (run MemoryTripleAdmission.Controls.code AllocatingControls.initialMachine) = some 21 := tripleAdmissionPrivate% cell1
example : (tripleAdmissionPrivate% readCell) 4 (run MemoryTripleAdmission.Controls.code AllocatingControls.initialMachine) = some 0 := tripleAdmissionPrivate% cell2
example : (tripleAdmissionPrivate% readCell) 2 (run MemoryTripleAdmission.Controls.code AllocatingControls.initialMachine) = some 16 := tripleAdmissionPrivate% cell3
example : (tripleAdmissionPrivate% readCell) 3 (run MemoryTripleAdmission.Controls.code AllocatingControls.initialMachine) = some 16 := tripleAdmissionPrivate% cell4
example : (tripleAdmissionPrivate% readCell) 1 (run MemoryTripleAdmission.Controls.code AllocatingControls.initialMachine) = some 19 := tripleAdmissionPrivate% cell5
example : (tripleAdmissionPrivate% readCell) 7 (run MemoryTripleAdmission.Controls.code AllocatingControls.initialMachine) = some 0 := tripleAdmissionPrivate% cell6
example : (tripleAdmissionPrivate% readCell) 16 (run MemoryTripleAdmission.Controls.code AllocatingControls.initialMachine) = some 2 := tripleAdmissionPrivate% cell7
example : (tripleAdmissionPrivate% readCell) 17 (run MemoryTripleAdmission.Controls.code AllocatingControls.initialMachine) = some 7 := tripleAdmissionPrivate% cell8
example : (tripleAdmissionPrivate% readCell) 18 (run MemoryTripleAdmission.Controls.code AllocatingControls.initialMachine) = some 9 := tripleAdmissionPrivate% cell9
example : (tripleAdmissionPrivate% readCell) 19 (run MemoryTripleAdmission.Controls.code AllocatingControls.initialMachine) = some 1 := tripleAdmissionPrivate% cell10
example : (tripleAdmissionPrivate% readCell) 20 (run MemoryTripleAdmission.Controls.code AllocatingControls.initialMachine) = some 4 := tripleAdmissionPrivate% cell11
example : (tripleAdmissionPrivate% readCell) 21 (run MemoryTripleAdmission.Controls.code AllocatingControls.initialMachine) = some 3 := tripleAdmissionPrivate% cell12
example : (tripleAdmissionPrivate% readCell) 22 (run MemoryTripleAdmission.Controls.code AllocatingControls.initialMachine) = some 0 := tripleAdmissionPrivate% cell13
example : (tripleAdmissionPrivate% readCell) 23 (run MemoryTripleAdmission.Controls.code AllocatingControls.initialMachine) = some 0 := tripleAdmissionPrivate% cell14
example : (tripleAdmissionPrivate% readCell) 24 (run MemoryTripleAdmission.Controls.code AllocatingControls.initialMachine) = some 0 := tripleAdmissionPrivate% cell15
example : (tripleAdmissionPrivate% readCell) 0 (run MemoryTripleAdmission.Controls.code AllocatingControls.initialMachine) = some 25 := tripleAdmissionPrivate% cell16

/-- info: cell0: [propext, Quot.sound, Classical.choice]
---
info: cell1: [propext, Quot.sound, Classical.choice]
---
info: cell2: [propext, Quot.sound, Classical.choice]
---
info: cell3: [propext, Quot.sound, Classical.choice]
---
info: cell4: [propext, Quot.sound, Classical.choice]
---
info: cell5: [propext, Quot.sound, Classical.choice]
---
info: cell6: [propext, Quot.sound, Classical.choice]
---
info: cell7: [propext, Quot.sound, Classical.choice]
---
info: cell8: [propext, Quot.sound, Classical.choice]
---
info: cell9: [propext, Quot.sound, Classical.choice]
---
info: cell10: [propext, Quot.sound, Classical.choice]
---
info: cell11: [propext, Quot.sound, Classical.choice]
---
info: cell12: [propext, Quot.sound, Classical.choice]
---
info: cell13: [propext, Quot.sound, Classical.choice]
---
info: cell14: [propext, Quot.sound, Classical.choice]
---
info: cell15: [propext, Quot.sound, Classical.choice]
---
info: cell16: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
run_cmd do
  for short in [`cell0, `cell1, `cell2, `cell3, `cell4, `cell5, `cell6, `cell7, `cell8, `cell9, `cell10, `cell11, `cell12, `cell13, `cell14, `cell15, `cell16] do
    let name := (Lean.Name.num `_private.Solidity.Backend.Passes.MemoryTripleAdmissionControls 0) ++
      `Solidity.Backend.Passes.MemoryTripleAdmission.Controls ++ short
    let axes ← Lean.collectAxioms name
    Lean.logInfo m!"{short}: {axes}"
end TripleAdmission

namespace AssociationControls
/-! Guard losing a shared full output map when reassociating public memory
compilations, or erasing reached bounds failure during that reassociation. -/
def joint := TripleAdmission.joint
def both_outputs := MemoryAssociation.Controls.both_outputs
def both_failures := MemoryAssociation.Controls.both_failures

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.AssociationControls.joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.AssociationControls.joint
/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.AssociationControls.both_outputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.AssociationControls.both_outputs
/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.AssociationControls.both_failures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.AssociationControls.both_failures
end AssociationControls

namespace ReturnedCapture
/-! Guard reading a freshly allocated return through a stale initial map,
or corrupting the saved caller tail while reading its selected pointer. -/
open AllocatingControls MemoryJoinCost.Controls MemoryJoinedAllocation

theorem joint :
    Memory.compileProg 1 (Frag.init [])
      (ReachabilityControls.populatedBuilder.join appendAllocation) =
      some MemoryJoinedAllocation.Controls.wholeCode ∧
    (Compilation.memory MemoryJoinedAllocation.Controls.wholeCode).Input 1 6
      initialBase (State.init Controls.Fixture.C) initialMachine ∧
    TEnv.get .here (suffixOut Controls.Fixture.σ).st.env =
      some ReturnedMemoryCapture.Controls.fresh ∧
    (∃ out : Solidity.Out Controls.Fixture.C (State.init Controls.Fixture.C).H
      (.mem (.array (.prim .uint)) :: Controls.Fixture.Γ),
      (ReachabilityControls.populatedBuilder.join appendAllocation).run
        (State.init Controls.Fixture.C) = .ok out) :=
  ⟨MemoryJoinedAllocation.Controls.whole_public,ReturnedMemoryCapture.Controls.whole_input,
    ReturnedMemoryCapture.Controls.fresh_bound,_,MemoryJoinedAllocation.joined_source⟩

def application := ReturnedMemoryCapture.Controls.application
def fresh_bound := @Solidity.Backend.Passes.ReturnedMemoryCapture.Controls.fresh_bound
def whole_input := @Solidity.Backend.Passes.ReturnedMemoryCapture.Controls.whole_input
def complete_pointer_observation := @Solidity.Backend.Passes.ReturnedMemoryCapture.Controls.complete_pointer_observation
def stale_initial_map := @Solidity.Backend.Passes.ReturnedMemoryCapture.Controls.stale_initial_map
def stale_readback_refused := @Solidity.Backend.Passes.ReturnedMemoryCapture.Controls.stale_readback_refused
def saved_tail_refused := @Solidity.Backend.Passes.ReturnedMemoryCapture.Controls.saved_tail_refused

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.ReturnedCapture.joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.ReturnedCapture.joint

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.ReturnedCapture.application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.ReturnedCapture.application

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.ReturnedCapture.fresh_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.ReturnedCapture.fresh_bound

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.ReturnedCapture.whole_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.ReturnedCapture.whole_input

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.ReturnedCapture.complete_pointer_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.ReturnedCapture.complete_pointer_observation

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.ReturnedCapture.stale_initial_map' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.ReturnedCapture.stale_initial_map

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.ReturnedCapture.stale_readback_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.ReturnedCapture.stale_readback_refused

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.ReturnedCapture.saved_tail_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.ReturnedCapture.saved_tail_refused
end ReturnedCapture

namespace AllocatedRead
/-! Guard reading through an old alias after fresh allocation, and accepting a
suffix that returns the right top word while deleting the caller's saved tail. -/
def joint := ReturnedCapture.joint
def runs := @Solidity.Backend.Passes.AllocatedReferenceRead.Controls.runs
def old_alias_fails := @Solidity.Backend.Passes.AllocatedReferenceRead.Controls.old_alias_fails
def fresh_reference_succeeds := @Solidity.Backend.Passes.AllocatedReferenceRead.Controls.fresh_reference_succeeds
def complete_memory := @Solidity.Backend.Passes.AllocatedReferenceRead.Controls.complete_memory
def corrupted_tail := @Solidity.Backend.Passes.AllocatedReferenceRead.Controls.corrupted_tail

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.AllocatedRead.joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.AllocatedRead.joint

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.AllocatedRead.runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.AllocatedRead.runs

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.AllocatedRead.old_alias_fails' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.AllocatedRead.old_alias_fails

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.AllocatedRead.fresh_reference_succeeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.AllocatedRead.fresh_reference_succeeds

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.AllocatedRead.complete_memory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.AllocatedRead.complete_memory

/-- info: 'Solidity.Backend.Passes.AuditJoinedAllocation.AllocatedRead.corrupted_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditJoinedAllocation.AllocatedRead.corrupted_tail

macro "allocatedReadPrivate%" n:ident : term =>
  pure (Lean.mkIdentFrom n ((Lean.Name.num `_private.Solidity.Backend.Passes.AllocatedReferenceReadControls 0) ++
    `Solidity.Backend.Passes.AllocatedReferenceRead.Controls ++ n.getId))
example : (allocatedReadPrivate% readCell) 5 (run AllocatedReferenceRead.Controls.code AllocatingControls.initialMachine) = some 21 := allocatedReadPrivate% cell0
example : (allocatedReadPrivate% readCell) 4 (run AllocatedReferenceRead.Controls.code AllocatingControls.initialMachine) = some 0 := allocatedReadPrivate% cell1
example : (allocatedReadPrivate% readCell) 2 (run AllocatedReferenceRead.Controls.code AllocatingControls.initialMachine) = some 16 := allocatedReadPrivate% cell2
example : (allocatedReadPrivate% readCell) 3 (run AllocatedReferenceRead.Controls.code AllocatingControls.initialMachine) = some 16 := allocatedReadPrivate% cell3
example : (allocatedReadPrivate% readCell) 1 (run AllocatedReferenceRead.Controls.code AllocatingControls.initialMachine) = some 19 := allocatedReadPrivate% cell4
example : (allocatedReadPrivate% readCell) 6 (run AllocatedReferenceRead.Controls.code AllocatingControls.initialMachine) = some 0 := allocatedReadPrivate% cell5
example : (allocatedReadPrivate% readCell) 16 (run AllocatedReferenceRead.Controls.code AllocatingControls.initialMachine) = some 2 := allocatedReadPrivate% cell6
example : (allocatedReadPrivate% readCell) 17 (run AllocatedReferenceRead.Controls.code AllocatingControls.initialMachine) = some 7 := allocatedReadPrivate% cell7
example : (allocatedReadPrivate% readCell) 18 (run AllocatedReferenceRead.Controls.code AllocatingControls.initialMachine) = some 9 := allocatedReadPrivate% cell8
example : (allocatedReadPrivate% readCell) 19 (run AllocatedReferenceRead.Controls.code AllocatingControls.initialMachine) = some 1 := allocatedReadPrivate% cell9
example : (allocatedReadPrivate% readCell) 20 (run AllocatedReferenceRead.Controls.code AllocatingControls.initialMachine) = some 4 := allocatedReadPrivate% cell10
example : (allocatedReadPrivate% readCell) 21 (run AllocatedReferenceRead.Controls.code AllocatingControls.initialMachine) = some 3 := allocatedReadPrivate% cell11
example : (allocatedReadPrivate% readCell) 22 (run AllocatedReferenceRead.Controls.code AllocatingControls.initialMachine) = some 0 := allocatedReadPrivate% cell12
example : (allocatedReadPrivate% readCell) 23 (run AllocatedReferenceRead.Controls.code AllocatingControls.initialMachine) = some 0 := allocatedReadPrivate% cell13
example : (allocatedReadPrivate% readCell) 24 (run AllocatedReferenceRead.Controls.code AllocatingControls.initialMachine) = some 0 := allocatedReadPrivate% cell14
example : (allocatedReadPrivate% readCell) 0 (run AllocatedReferenceRead.Controls.code AllocatingControls.initialMachine) = some 25 := allocatedReadPrivate% cell15

/-- info: cell0: [propext, Quot.sound, Classical.choice]
---
info: cell1: [propext, Quot.sound, Classical.choice]
---
info: cell2: [propext, Quot.sound, Classical.choice]
---
info: cell3: [propext, Quot.sound, Classical.choice]
---
info: cell4: [propext, Quot.sound, Classical.choice]
---
info: cell5: [propext, Quot.sound, Classical.choice]
---
info: cell6: [propext, Quot.sound, Classical.choice]
---
info: cell7: [propext, Quot.sound, Classical.choice]
---
info: cell8: [propext, Quot.sound, Classical.choice]
---
info: cell9: [propext, Quot.sound, Classical.choice]
---
info: cell10: [propext, Quot.sound, Classical.choice]
---
info: cell11: [propext, Quot.sound, Classical.choice]
---
info: cell12: [propext, Quot.sound, Classical.choice]
---
info: cell13: [propext, Quot.sound, Classical.choice]
---
info: cell14: [propext, Quot.sound, Classical.choice]
---
info: cell15: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
run_cmd do
  for short in [`cell0, `cell1, `cell2, `cell3, `cell4, `cell5, `cell6, `cell7, `cell8, `cell9, `cell10, `cell11, `cell12, `cell13, `cell14, `cell15] do
    let name := (Lean.Name.num `_private.Solidity.Backend.Passes.AllocatedReferenceReadControls 0) ++
      `Solidity.Backend.Passes.AllocatedReferenceRead.Controls ++ short
    let axes ← Lean.collectAxioms name
    Lean.logInfo m!"{short}: {axes}"
end AllocatedRead
end Solidity.Backend.Passes.AuditJoinedAllocation
