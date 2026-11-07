import Solidity.Lowering.V08.SourceEnvironmentControls
import Solidity.Lowering.V08.SourceKeccak

/-! Regression: environment reads must retain an already reached allocation,
and payment value must not be confused with timestamp. These independent reads
use the same actual Source state after hashing, not a compiled session, admitted
program, physical target frame or canonical pass certificate. -/
namespace H62.AuditV08Adapters.SourceEnvironmentJoint
open Solidity Source
open Solidity.Lowering.V08
open SourceEnvironmentControls

/-- The actual allocation and three separate reads share the same reached state. -/
theorem reached_reads (pipeline : Roadmap.Pipeline) (static : Bool) (fuel : Nat)
    (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) {frame with static:=static} (fuel+5)
      (SourceKeccak.literal bytes)).run (locals,populated) =
      (.ok (.val (Source.mkBytes (n:=32) (h:=by decide +kernel)
        (Source.wordBytes ((global pipeline).fixed.hash bytes)))),
        (locals,SourceKeccak.afterLiteral populated bytes)) ∧
    (Source.evalE (global pipeline) {frame with static:=static} (fuel+1)
      (.magic .msg "sender" rfl : RExpr E [.bool] (.address false))).run
        (locals,SourceKeccak.afterLiteral populated bytes) =
      (.ok (.val (.address frame.sender)),(locals,SourceKeccak.afterLiteral populated bytes)) ∧
    (Source.evalE (global pipeline) {frame with static:=static} (fuel+1)
      (.magic .msg "value" rfl : RExpr E [.bool] (.int IntTy.u256))).run
        (locals,SourceKeccak.afterLiteral populated bytes) =
      (.ok (.val (SourceEnvironment.sourceWord frame.value)),
        (locals,SourceKeccak.afterLiteral populated bytes)) ∧
    (Source.evalE (global pipeline) {frame with static:=static} (fuel+1)
      (.magic .block "timestamp" rfl : RExpr E [.bool] (.int IntTy.u256))).run
        (locals,SourceKeccak.afterLiteral populated bytes) =
      (.ok (.val (SourceEnvironment.sourceWord (global pipeline).timestamp)),
        (locals,SourceKeccak.afterLiteral populated bytes)) :=
  ⟨SourceKeccak.eval_literal (global pipeline) {frame with static:=static} fuel bytes locals populated,
    SourceEnvironment.eval_sender (global pipeline) {frame with static:=static} fuel locals _,
    SourceEnvironment.eval_value (global pipeline) {frame with static:=static} fuel locals _,
    SourceEnvironment.eval_timestamp (global pipeline) {frame with static:=static} fuel locals _⟩

/-- Equal reached states do not make distinct context fields interchangeable. -/
theorem value_not_timestamp (pipeline : Roadmap.Pipeline) (static : Bool) (fuel : Nat)
    (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) {frame with static:=static} (fuel+1)
      (.magic .msg "value" rfl : RExpr E [.bool] (.int IntTy.u256))).run
        (locals,SourceKeccak.afterLiteral populated bytes) ≠
    (Source.evalE (global pipeline) {frame with static:=static} (fuel+1)
      (.magic .block "timestamp" rfl : RExpr E [.bool] (.int IntTy.u256))).run
        (locals,SourceKeccak.afterLiteral populated bytes) := by
  rw [SourceEnvironment.eval_value,SourceEnvironment.eval_timestamp]
  intro same
  have number := congrArg (fun result => match result.1 with
    | .ok (.val (.int n _)) => n
    | _ => 0) same
  change (7 : Int) = 12345 at number
  have distinct : (7 : Int) ≠ 12345 := by decide +kernel
  exact distinct number

#print axioms reached_reads
#print axioms value_not_timestamp
end H62.AuditV08Adapters.SourceEnvironmentJoint
