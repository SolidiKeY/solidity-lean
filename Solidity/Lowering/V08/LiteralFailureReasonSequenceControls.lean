import Solidity.Lowering.V08.LiteralFailureReasonSequence
import Solidity.Lowering.V08.LiteralFailureMemoryReasonControls
namespace Solidity.Lowering.V08.LiteralFailureReasonSequenceControls
open Solidity Source
open LiteralFailureMemoryReason LiteralFailureMemoryRevert LiteralFailureReasonSequence
open LiteralFailureMemoryReasonControls (state older packetsJson)
open SourceCustomErrorControls (E global frame)

def poison : RItems E [] false .body (context [.string .memory,.bytes .memory,.bool])
 (context [.string .memory,.bytes .memory,.bool]) :=
 .stmt (.expr (.builtin .assert (.cons (.bool false) .nil) rfl)) .nil

theorem tail_alone (bs : Roadmap.Bytes) (p : Roadmap.Pipeline) (static : Bool) :
 (execItems (global p) {frame with static:=static} 12 0 none poison
 (caller false 1 2 older)).run (L0 E,state bs)=
 (.error (.revert (panicData .assert)),(L0 E,state bs)) := by rfl

theorem first_failure_wins (bs : Roadmap.Bytes) (p : Roadmap.Pipeline) (static : Bool) :
 (execItems (global p) {frame with static:=static} 12 0 none
 (.stmt (.expr requireAssigned) poison) (caller false 1 2 older)).run (L0 E,state bs)=
 (.error (.revert (errorData bs)),(L0 E,state bs)) :=
 failed_require (global p) {frame with static:=static} 2 poison 1 2 older (state bs) bs rfl

theorem changed_reference_continues (bs : Roadmap.Bytes) (p : Roadmap.Pipeline) (static : Bool) :
 (execItems (global p) {frame with static:=static} 12 0 none requireThenRevert
 (caller true 1 2 older)).run (L0 E,state bs)=
 (.error (.revert (errorData bs)),(L0 E,state bs)) :=
 success_then_revert (global p) {frame with static:=static} 0 1 2 older (state bs) bs rfl

theorem stale_pointer_baseline (bs : Roadmap.Bytes) (p : Roadmap.Pipeline) :
 (execS (global p) frame 9 0 none (.expr revertCurrent : RStmt E [] false .body _ _)
 (caller true 1 2 older)).run (L0 E,state bs)=
 (.error (.revert (errorData [83])),(L0 E,state bs)) :=
 current_statement (global p) frame 0 true 1 2 older (state bs) [83] rfl

theorem stale_reason_differs : errorData [0,255] ≠ errorData [83] := by decide

theorem distinct_failure_class : errorData [0,255] ≠ panicData .assert := by decide

theorem no_budget_is_not_revert (bs : Roadmap.Bytes) :
 (execItems (global .legacy) frame 0 0 none requireThenRevert
 (caller true 1 2 older)).run (L0 E,state bs) ≠
 (.error (.revert (errorData bs)),(L0 E,state bs)) := by
 intro h
 have bad := congrArg Prod.fst h
 cases bad

#eval IO.println ("REASON_SEQUENCE_PACKETS=" ++ packetsJson)
#print axioms current_statement
#print axioms stale_pointer_baseline
#print axioms stale_reason_differs
#print axioms prefix_error
#print axioms failed_require
#print axioms success_then_revert
#print axioms tail_alone
#print axioms first_failure_wins
#print axioms changed_reference_continues
#print axioms distinct_failure_class
#print axioms no_budget_is_not_revert
end Solidity.Lowering.V08.LiteralFailureReasonSequenceControls
