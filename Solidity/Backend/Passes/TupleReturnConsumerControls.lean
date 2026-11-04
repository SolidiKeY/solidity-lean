import Solidity.Backend.Passes.TupleReturnConsumer

namespace Solidity.Backend.Passes.TupleReturnConsumer.Controls
open Evm Evm.Memory Evm.Compiler
open Backend.InternalFlow.RuntimeFrame
open Backend.InternalFlow.RuntimeFrame.V3CallProducerRef
open Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.Tuple.Controls

def code : List Evm.Instr := compiled.code ++ readerCode.code
/-- Preserve the producer's original ordered cells, then append every extra
callee interval/sentinel cell needed to distinguish return compaction. -/
def cells : List Nat := [0,1,2,3,4,16,63,128,129,130,5,6,7]
private def observe : Evm.Out → Option (List Nat)
  | .ok machine 0 => (machine.stack ++ cells.map machine.mem).mapM
      (fun word => match word with | .val value => some value.val | _ => none)
  | _ => none

theorem complete_observation : observe (run code (ArrayControls.machine (wmod 0))) =
    some [7,77,131,128,0,128,7,20,99,1,0,0,128,7,0] := by decide +kernel

/-- Omitting actual tuple compaction feeds parameter words to the result reader. -/
theorem missing_compaction_refused : observe
    (run (expanded.checked.code ++ readerCode.code) (ArrayControls.machine (wmod 0))) ≠
    some [7,77,131,128,0,128,7,20,99,1,0,0,128,7,0] := by decide +kernel

theorem corrupted_tail_refused : observe (run code (ArrayControls.machine (wmod 0))) ≠
    some [7,78,131,128,0,128,7,20,99,1,0,0,128,7,0] := by
  rw [complete_observation]
  decide

theorem failure_before_read : run code (ArrayControls.machine (wmod 2)) = .revert :=
  reached_revert [w[77]]

/-- Keep the producer's original exact reached allocation-capacity refusal. -/
theorem insufficient_capacity : ¬ compiled.Input 1 64 ArrayControls.bases
    (ArrayControls.caller (wmod 0))
    (writeMachine (ArrayControls.machine (wmod 0)) 0 (.val (wmod (W-1)))) := by
  intro input
  exact V3CallProducerRef.Tuple.Controls.capacity_refused input.2.2

/-- The retained result fits frame5, but the actual private parameter/result
interval still needs6 slots above b=1; result-only admission is insufficient. -/
theorem private_frame_refused : ¬ compiled.Input 1 5 ArrayControls.bases
    (ArrayControls.caller (wmod 0)) (ArrayControls.machine (wmod 0)) := by
  intro input
  have room := input.2.1
  have minimum : 6 ≤ selected.checked.need := by
    change 6 ≤ max (max expanded.checked.need 6) 4
    exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  omega

/-- These source observations concern the existing intrinsic call, not
independent admitted Source syntax or source-to-bytecode correspondence. -/
def source_tuple_observation := V3CallProducerRef.Tuple.Controls.source_observation

/-- info: 'Solidity.Backend.Passes.TupleReturnConsumer.Controls.corrupted_tail_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms corrupted_tail_refused
/-- info: 'Solidity.Backend.Passes.TupleReturnConsumer.Controls.complete_observation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms complete_observation
/-- info: 'Solidity.Backend.Passes.TupleReturnConsumer.Controls.missing_compaction_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms missing_compaction_refused
/-- info: 'Solidity.Backend.Passes.TupleReturnConsumer.Controls.failure_before_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms failure_before_read
/-- info: 'Solidity.Backend.Passes.TupleReturnConsumer.Controls.insufficient_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms insufficient_capacity
/-- info: 'Solidity.Backend.Passes.TupleReturnConsumer.Controls.private_frame_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms private_frame_refused
end Solidity.Backend.Passes.TupleReturnConsumer.Controls
