import Solidity.Lowering.V08.LiteralFailureOverflowReason
import Solidity.Lowering.V08.LiteralFailureMemoryReasonControls
namespace Solidity.Lowering.V08.LiteralFailureOverflowReasonControls
open Solidity Source
open LiteralFailureOverflowReason
open LiteralFailureMemoryReasonControls (state older)
open SourceCustomErrorControls (E global frame)

def signed8 : IntTy := ⟨true,8,by decide⟩

theorem unsigned_failure (p : Roadmap.Pipeline) (static : Bool) :
 (evalE (global p) {frame with static:=static,checked:=true} 5 (addition IntTy.u8)).run
 (caller IntTy.u8 255 1 (by decide) (by decide) older,state [0,255])=
 (.error (.revert (panicData .arithmetic)),
 (caller IntTy.u8 255 1 (by decide) (by decide) older,state [0,255])) :=
 checked_overflow (global p) {frame with static:=static} 0 IntTy.u8 255 1
  (by decide) (by decide) (by decide) older (state [0,255])

theorem unsigned_wrap (p : Roadmap.Pipeline) :
 (evalE (global p) {frame with checked:=false} 5 (addition IntTy.u8)).run
 (caller IntTy.u8 255 1 (by decide) (by decide) older,state [0,255])=
 (.ok (.val (.int 0 (by decide))),
 (caller IntTy.u8 255 1 (by decide) (by decide) older,state [0,255])) :=
 unchecked_overflow (global p) frame 0 IntTy.u8 255 1
  (by decide) (by decide) (by decide) older (state [0,255])

theorem signed_failure (p : Roadmap.Pipeline) :
 (evalE (global p) {frame with checked:=true} 5 (addition signed8)).run
 (caller signed8 127 1 (by decide) (by decide) older,state [0,255])=
 (.error (.revert (panicData .arithmetic)),
 (caller signed8 127 1 (by decide) (by decide) older,state [0,255])) :=
 checked_overflow (global p) frame 0 signed8 127 1
  (by decide) (by decide) (by decide) older (state [0,255])

theorem signed_wrap (p : Roadmap.Pipeline) :
 (evalE (global p) {frame with checked:=false} 5 (addition signed8)).run
 (caller signed8 127 1 (by decide) (by decide) older,state [0,255])=
 (.ok (.val (.int (-128) (by decide))),
 (caller signed8 127 1 (by decide) (by decide) older,state [0,255])) :=
 unchecked_overflow (global p) frame 0 signed8 127 1
  (by decide) (by decide) (by decide) older (state [0,255])

theorem boundary_success (p : Roadmap.Pipeline) (checked : Bool) :
 (evalE (global p) {frame with checked:=checked} 5 (addition signed8)).run
 (caller signed8 127 0 (by decide) (by decide) older,state [0,255])=
 (.ok (.val (.int 127 (by decide))),
 (caller signed8 127 0 (by decide) (by decide) older,state [0,255])) :=
 in_range (global p) {frame with checked:=checked} 0 signed8 127 0
  (by decide) (by decide) (by decide) older (state [0,255])

theorem wrong_panic_class : panicData .arithmetic ≠ panicData .divZero := by decide

def bytesJson (bs : List UInt8) : String :=
 "[" ++ String.intercalate "," (bs.map (fun b => toString b.toNat)) ++ "]"
#eval IO.println ("OVERFLOW_PANIC_PACKET=" ++ bytesJson (panicData .arithmetic))
#print axioms add_value
#print axioms checked_overflow
#print axioms unchecked_overflow
#print axioms in_range
#print axioms unsigned_failure
#print axioms unsigned_wrap
#print axioms signed_failure
#print axioms signed_wrap
#print axioms boundary_success
#print axioms wrong_panic_class
end Solidity.Lowering.V08.LiteralFailureOverflowReasonControls
