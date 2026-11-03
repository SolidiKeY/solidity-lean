import Solidity.Lowering.V08.LiteralFailureScalarOverflow
import Solidity.Lowering.V08.LiteralFailureMemoryReasonControls
namespace Solidity.Lowering.V08.LiteralFailureScalarOverflowControls
open Solidity Source Backend
open LiteralFailureScalarOverflow
open LiteralFailureMemoryReasonControls (state older)
open SourceCustomErrorControls (E global frame)

def maximum : PrimTy.uint.Denote := ⟨((2^256-1 : Nat) : Int),by decide +kernel⟩
def one : PrimTy.uint.Denote := ⟨1,by decide +kernel⟩
def stack : Scalar.Stack := [7,9]

theorem overflow_bound : ((2^256 : Nat) : Int)≤maximum.val+one.val := by decide +kernel

theorem populated (p : Roadmap.Pipeline) (static : Bool) :
 (evalE (global p) {frame with static:=static,checked:=true} 5
 (LiteralFailureOverflowReason.addition IntTy.u256)).run
 (LiteralFailureOverflowReason.caller IntTy.u256 maximum.val one.val
 (source_bound maximum) (source_bound one) older,state [0,255])=
 (.error (.revert (panicData .arithmetic)),
 (LiteralFailureOverflowReason.caller IntTy.u256 maximum.val one.val
 (source_bound maximum) (source_bound one) older,state [0,255])) ∧
 Scalar.guarded Scalar.checkedUintAdd.test Scalar.checkedUintAdd.body Scalar.overflowFailure
 (Scalar.encodeValue .uint maximum :: Scalar.encodeValue .uint one :: stack)=
 some (.error (panicData .arithmetic)) :=
 agreement (global p) {frame with static:=static} 0 maximum one older (state [0,255]) stack overflow_bound

theorem retained_operands :
 Scalar.run Scalar.unsignedAddTest (Scalar.encodeValue .uint maximum :: Scalar.encodeValue .uint one :: stack)=
 some (Scalar.flag true :: Scalar.encodeValue .uint maximum :: Scalar.encodeValue .uint one :: stack) :=
 test_flag maximum one stack overflow_bound

theorem raw_zero :
 Scalar.run Scalar.checkedUintAdd.body (Scalar.encodeValue .uint maximum :: Scalar.encodeValue .uint one :: stack)=
 some (0 :: stack) := by
 simpa only [maximum,one] using raw_body maximum one stack

theorem positive_baseline :
 Scalar.guarded Scalar.checkedUintAdd.test Scalar.checkedUintAdd.body Scalar.overflowFailure
 (Scalar.encodeValue .uint one :: Scalar.encodeValue .uint one :: stack)=some (.ok (2 :: stack)) := by
 rfl

theorem no_success_on_overflow :
 Scalar.guarded Scalar.checkedUintAdd.test Scalar.checkedUintAdd.body Scalar.overflowFailure
 (Scalar.encodeValue .uint maximum :: Scalar.encodeValue .uint one :: stack) ≠ some (.ok (0 :: stack)) := by
 rw [target_failure maximum one stack overflow_bound]
 intro h
 cases h

def stackJson (words : Scalar.Stack) : String :=
 "[" ++ String.intercalate "," (words.map (fun w=>toString w.toNat)) ++ "]"
def runJson (result : Option Scalar.Stack) : String :=
 match result with | none => "null" | some words => stackJson words
#eval IO.println ("SCALAR_TEST_STACK=" ++ runJson (Scalar.run Scalar.unsignedAddTest
 (Scalar.encodeValue .uint maximum :: Scalar.encodeValue .uint one :: stack)))
#eval IO.println ("SCALAR_RAW_STACK=" ++ runJson (Scalar.run Scalar.checkedUintAdd.body
 (Scalar.encodeValue .uint maximum :: Scalar.encodeValue .uint one :: stack)))
#eval IO.println ("SCALAR_OVERFLOW_BYTES=[" ++ String.intercalate "," ((panicData .arithmetic).map (fun b=>toString b.toNat)) ++ "]")
#print axioms source_bound
#print axioms failure_bytes
#print axioms range_false
#print axioms target_failure
#print axioms test_flag
#print axioms raw_body
#print axioms agreement
#print axioms populated
#print axioms retained_operands
#print axioms raw_zero
#print axioms positive_baseline
#print axioms no_success_on_overflow
end Solidity.Lowering.V08.LiteralFailureScalarOverflowControls
