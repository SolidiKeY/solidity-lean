import Solidity.Lowering.V08.LiteralFailureArithmeticReason
import Solidity.Lowering.V08.LiteralFailureMemoryReasonControls
import Solidity.Backend.AbiWorld.ErrorReadWindowControls
namespace Solidity.Lowering.V08.LiteralFailureArithmeticReasonControls
open Solidity Source Backend
open LiteralFailureArithmeticReason
open LiteralFailureMemoryReasonControls (state older)
open SourceCustomErrorControls (E global frame)

theorem populated (x : Roadmap.Word) (p : Roadmap.Pipeline) (static checked modulo : Bool) :
 (evalE (global p) {frame with static:=static,checked:=checked} 8 (operation modulo)).run
 (caller (SourceEnvironment.sourceWord x) older,state [0,255])=
 (.error (.revert (panicData .divZero)),(caller zero older,state [0,255])) :=
 execution (global p) {frame with static:=static,checked:=checked} 0 modulo
  (SourceEnvironment.sourceWord x) older (state [0,255])

theorem emitted_packet (x : Roadmap.Word) (p : Roadmap.Pipeline) (modulo : Bool) :
 (evalE (global p) frame 8 (operation modulo)).run
 (caller (SourceEnvironment.sourceWord x) older,state [0,255])=
 (.error (.revert (panicData .divZero)),(caller zero older,state [0,255])) ∧
 Failure.Slice.checkedRun (Failure.emit 8 (LiteralFailureLowering.panicInput .divZero) ++ [.op .ADD])
  AbiWorld.ErrorReadWindowControls.machine =
 some ({AbiWorld.ErrorReadWindowControls.machine with memory := Failure.Slice.putBytes AbiWorld.ErrorReadWindowControls.machine.memory 8 (panicData .divZero)},
  some (revertOutcome (panicData .divZero))) :=
 packet (global p) frame 0 modulo (SourceEnvironment.sourceWord x) older (state [0,255])
  8 [.op .ADD] AbiWorld.ErrorReadWindowControls.machine (by simp only [Failure.Fits,panicData_length]; decide +kernel) (by decide)

theorem old_value_changed :
 caller (E:=E) (SourceEnvironment.sourceWord ⟨42,by decide +kernel⟩) older ≠ caller zero older := by
 intro h
 have bad := congrArg (fun l => l.get .here) h
 cases bad

theorem not_arithmetic_overflow : panicData .divZero ≠ panicData .arithmetic := by decide

theorem not_assertion : panicData .divZero ≠ panicData .assert := by decide

theorem no_horizon (x : Roadmap.Word) :
 (evalE (global .legacy) frame 0 (operation false)).run
 (caller (SourceEnvironment.sourceWord x) older,state [0,255]) ≠
 (.error (.revert (panicData .divZero)),(caller zero older,state [0,255])) := by
 intro h
 have bad := congrArg Prod.fst h
 cases bad

def bytesJson (bs : List UInt8) : String :=
 "[" ++ String.intercalate "," (bs.map (fun b => toString b.toNat)) ++ "]"
#eval IO.println ("ARITHMETIC_PANIC_PACKET=" ++ bytesJson (panicData .divZero))
#print axioms execution
#print axioms packet
#print axioms populated
#print axioms emitted_packet
#print axioms old_value_changed
#print axioms not_arithmetic_overflow
#print axioms not_assertion
#print axioms no_horizon
end Solidity.Lowering.V08.LiteralFailureArithmeticReasonControls
