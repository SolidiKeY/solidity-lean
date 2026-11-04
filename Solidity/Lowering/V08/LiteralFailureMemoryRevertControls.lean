import Solidity.Lowering.V08.LiteralFailureMemoryRevert
import Solidity.Lowering.V08.LiteralFailureMemoryReasonControls
namespace Solidity.Lowering.V08.LiteralFailureMemoryRevertControls
open Solidity Source
open LiteralFailureMemoryReason LiteralFailureMemoryRevert
open LiteralFailureMemoryReasonControls (state older messages packetsJson)
open SourceCustomErrorControls (E global frame)

theorem populated (bs : Roadmap.Bytes) (pipeline : Roadmap.Pipeline) (static b : Bool) :
 (evalE (global pipeline) {frame with static:=static} 8 revertAssigned).run
 (caller b 1 2 older,state bs) =
 (.error (.revert (errorSelector ++ AbiEntry.encodeArgs (LiteralFailureBytesReadback.values bs))),
 (caller b 2 2 older,state bs)) := by
 rw [← LiteralFailureBytesReadback.source_error]
 exact execution (global pipeline) {frame with static:=static} 0 b 1 2 older (state bs) bs rfl

/-- Equal references need no invented disjointness restriction. -/
theorem alias_execution (bs : Roadmap.Bytes) (pipeline : Roadmap.Pipeline) :
 (evalE (global pipeline) frame 8 revertAssigned).run (caller true 2 2 older,state bs) =
 (.error (.revert (errorData bs)),(caller true 2 2 older,state bs)) :=
 execution (global pipeline) frame 0 true 2 2 older (state bs) bs rfl

theorem not_success (bs : Roadmap.Bytes) :
 (evalE (global .legacy) frame 8 revertAssigned).run (caller true 1 2 older,state bs) ≠
 (.ok RVal.unit,(caller true 2 2 older,state bs)) := by
 rw [execution (global .legacy) frame 0 true 1 2 older (state bs) bs rfl]
 intro h
 cases h

theorem insufficient_fuel (bs : Roadmap.Bytes) :
 (evalE (global .legacy) frame 0 revertAssigned).run (caller false 1 2 older,state bs) ≠
 (.error (.revert (errorData bs)),(caller false 2 2 older,state bs)) := by
 intro h
 have bad := congrArg Prod.fst h
 cases bad

#eval IO.println ("MEMORY_REVERT_PACKETS=" ++ packetsJson)
#print axioms execution
#print axioms populated
#print axioms alias_execution
#print axioms not_success
#print axioms insufficient_fuel
end Solidity.Lowering.V08.LiteralFailureMemoryRevertControls
