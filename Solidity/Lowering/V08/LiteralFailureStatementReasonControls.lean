import Solidity.Lowering.V08.LiteralFailureStatementReason
import Solidity.Lowering.V08.LiteralFailureMemoryReasonControls
namespace Solidity.Lowering.V08.LiteralFailureStatementReasonControls
open Solidity Source
open LiteralFailureMemoryReason LiteralFailureMemoryRevert LiteralFailureStatementReason
open LiteralFailureMemoryReasonControls (state older packetsJson)
open SourceCustomErrorControls (E global frame)

theorem actual_revert (bs : Roadmap.Bytes) (p : Roadmap.Pipeline) (static b : Bool) :
 (execS (global p) {frame with static:=static} 9 0 none
  (.expr revertAssigned : RStmt E [] false .body _ _) (caller b 1 2 older)).run
 (L0 E,state bs)=(.error (.revert (errorData bs)),(L0 E,state bs)) :=
 revert_statement (global p) {frame with static:=static} 0 b 1 2 older (state bs) bs rfl

theorem actual_require (bs : Roadmap.Bytes) (p : Roadmap.Pipeline) (static : Bool) :
 (execS (global p) {frame with static:=static} 9 0 none
  (.expr requireAssigned : RStmt E [] false .body _ _) (caller false 1 2 older)).run
 (L0 E,state bs)=(.error (.revert (errorData bs)),(L0 E,state bs)) :=
 require_statement (global p) {frame with static:=static} 0 1 2 older (state bs) bs rfl

theorem actual_success (bs : Roadmap.Bytes) (p : Roadmap.Pipeline) (static : Bool) :
 (execS (global p) {frame with static:=static} 9 0 none
  (.expr requireAssigned : RStmt E [] false .body _ _) (caller true 1 2 older)).run
 (L0 E,state bs)=(.ok (.normal (caller true 2 2 older)),(L0 E,state bs)) :=
 require_success (global p) {frame with static:=static} 0 1 2 older (state bs)

theorem wrong_old_pointer : caller (E:=E) true 2 2 older ≠ caller true 1 2 older := by
 intro h
 have bad := congrArg (fun l => l.get (.there .here)) h
 cases bad

#eval IO.println ("STATEMENT_REASON_PACKETS=" ++ packetsJson)
#print axioms expression_error
#print axioms revert_statement
#print axioms require_statement
#print axioms require_success
#print axioms actual_revert
#print axioms actual_require
#print axioms actual_success
#print axioms wrong_old_pointer
end Solidity.Lowering.V08.LiteralFailureStatementReasonControls
