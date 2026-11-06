import Solidity.Lowering.V08.LiteralFailureMemoryReason
import Solidity.Lowering.V08.SourceCustomErrorControls

namespace Solidity.Lowering.V08.LiteralFailureMemoryReasonControls
open Solidity Source
open LiteralFailureMemoryReason
open SourceCustomErrorControls (E global frame populated)

def state (bs : Roadmap.Bytes) : St E :=
 { populated with heap := ((populated.heap.alloc ⟨.string .memory,.string [83]⟩).1.alloc
   ⟨.string .memory,.string bs⟩).1 }
def older : Locals E.layout [.string .memory,.bytes .memory,.bool] :=
 .cons (.memRef rfl 1) (.cons (.memRef rfl 0) (.cons (.bool true) .nil))

theorem actual_failure (bs : Roadmap.Bytes) (pipeline : Roadmap.Pipeline) (static : Bool) :
 (evalE (global pipeline) {frame with static:=static} 8 requireAssigned).run
  (caller false 1 2 older,state bs) =
 (.error (.revert (errorSelector ++ AbiEntry.encodeArgs (LiteralFailureBytesReadback.values bs))),
   (caller false 2 2 older,state bs)) := by
 rw [← LiteralFailureBytesReadback.source_error]
 exact require_false (global pipeline) {frame with static:=static} 0 1 2 older (state bs) bs rfl

theorem actual_success (bs : Roadmap.Bytes) (pipeline : Roadmap.Pipeline) (static : Bool) :
 (evalE (global pipeline) {frame with static:=static} 8 requireAssigned).run
  (caller true 1 2 older,state bs) = (.ok RVal.unit,(caller true 2 2 older,state bs)) :=
 require_true (global pipeline) {frame with static:=static} 0 1 2 older (state bs)

theorem aliases (bs : Roadmap.Bytes) :
 (state bs).heap.get 0=some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
 (state bs).heap.get 1=some ⟨.string .memory,.string [83]⟩ ∧
 (state bs).heap.get 2=some ⟨.string .memory,.string bs⟩ ∧ (state bs).heap.next=3 :=
 ⟨rfl,rfl,rfl,rfl⟩

theorem no_assignment_at_zero (bs : Roadmap.Bytes) :
 (evalE (global .legacy) frame 0 requireAssigned).run (caller false 1 2 older,state bs) ≠
 (.error (.revert (errorData bs)),(caller false 2 2 older,state bs)) := by
 intro h
 have bad := congrArg Prod.fst h
 cases bad

theorem distinct_reason : errorData [0,255] ≠ errorData [83] := by decide

def messages : List Roadmap.Bytes :=
 [[],[0],[255],[0,255,128],List.replicate 31 255,List.replicate 32 0,List.replicate 33 128]
def packetsJson : String := "[" ++ String.intercalate "," (messages.map fun bs =>
 "[" ++ String.intercalate "," ((errorData bs).map fun b => toString b.toNat) ++ "]") ++ "]"
#eval IO.println ("MEMORY_REASON_PACKETS=" ++ packetsJson)
#print axioms assignment
#print axioms require_true
#print axioms require_false
#print axioms actual_failure
#print axioms actual_success
#print axioms aliases
#print axioms no_assignment_at_zero
#print axioms distinct_reason
end Solidity.Lowering.V08.LiteralFailureMemoryReasonControls
