import Solidity.Lowering.Readonly.SourceStatementEffects
import Solidity.Lowering.Readonly.SourceDispatchControls
import Solidity.Lowering.Readonly.SourceHistoryBase

/-! Inhabited actual Source statement controls. Dirty statement failure is not
transaction rollback; finite observations are not target/native adequacy. -/
namespace Solidity.Lowering.Readonly.SourceStatementControls
open Solidity.Source Solidity.Source.SemanticsExamples
open SourceHistory
def global := GB (fun _ => .answer (.success []))
def run {Γ' : RCtx} (mode : Bool) (s : RStmt EB [] false .body [] Γ') (fuel : Nat := 30) :=
  (execS global {FC with static := mode} fuel 0 none s (L0 EB)).run (L0 EB, sB)
def firstLocal (out : Out EB.layout [] [uint]) : Option Int :=
  match out with
  | .normal (.cons (.int k _) _) => some k
  | _ => none
def localInit : RStmt EB [] false .body [] [uint] := .declInit (lit 4) rfl
def declare : RStmt EB [] false .body [] [uint] := .declVar uint
def writeStmt : RStmt EB [] false .body [] [] := setX (lit 4)
def skipStmt : RStmt EB [] false .body [] [] := .skip
def scopeBlock : RStmt EB [] false .body [] [] :=
  .block (.stmt localInit (.stmt (setX (.local .here)) .nil))
def conditional : RStmt EB [] false .body [] [] :=
  .ifElse (.bool false) writeStmt (setX (lit 9))
def target : RExpr EB [] (.contract ⟨none,"I"⟩) :=
  .convExplicit (.addressLit [9]) (by decide)
def call (rethrow : Bool) : RStmt EB [] false .body [] [] :=
  if rethrow then .tryCall target dPing dPing_sig .nil
    (.stmt writeStmt .nil) true (.stmt (.rethrow .here) .nil)
  else .tryCall target dPing dPing_sig .nil
    (.stmt writeStmt .nil) false (.stmt (setX (lit 9)) .nil)
def tryRun (mode : Bool) (answer : Solidity.Roadmap.Outcome) (rethrow : Bool := false)
    (hasCode : Bool := true) :=
  (execS {(GB (fun _ => .answer answer)) with hasCode := fun _ _ => hasCode}
    {FC with static := mode} 30 0 none (call rethrow) (L0 EB)).run (L0 EB, sB)
theorem static_local_initialization : (match (run true localInit).1 with | .ok out => firstLocal out | _ => none) = some 4 := by decide
theorem default_local : (match (run true declare).1 with | .ok out => firstLocal out | _ => none) = some 0 := by decide
theorem local_storage_kept : readX (run true localInit).2.2 = some 3 := by decide
theorem ordinary_write : readX (run false writeStmt).2.2 = some 4 := by decide
theorem ordinary_not_frozen : readX (run false writeStmt).2.2 ≠ some 3 := by decide
theorem static_write : (run true writeStmt).1 = .error (.revert []) := by rfl
theorem static_write_kept : readX (run true writeStmt).2.2 = some 3 := by decide
theorem scoped_local_use : readX (run false scopeBlock).2.2 = some 4 := by decide
theorem scoped_success : SourceLoopControls.status (run false scopeBlock).1 = 0 := by decide
theorem false_branch : readX (run false conditional).2.2 = some 9 := by decide
theorem zero_exhausts : (run true skipStmt 0).1 = .error .timeout := by rfl
theorem one_skip_succeeds : SourceLoopControls.status (run true skipStmt 1).1 = 0 := by decide
theorem success_continuation_write : SourceLoopControls.status (tryRun false (.success [])).1 = 0 ∧ readX (tryRun false (.success [])).2.2 = some 4 := by decide
theorem static_continuation_refused : (tryRun true (.success [])).1 = .error (.revert []) := by rfl
theorem static_continuation_kept : readX (tryRun true (.success [])).2.2 = some 3 := by decide
theorem callee_revert_caught : SourceLoopControls.status (tryRun false (.revert [7,9])).1 = 0 ∧ readX (tryRun false (.revert [7,9])).2.2 = some 9 := by decide
theorem callee_revert_rethrown : (tryRun false (.revert [7,9]) true).1 = .error (.revert [7,9]) := by rfl
theorem no_code_outside_catch : (tryRun false (.revert [7,9]) false false).1 = .error (.revert []) := by rfl
theorem no_code_kept : readX (tryRun false (.revert [7,9]) false false).2.2 = some 3 := by decide
theorem actual_skip_client :
    Effect true (execS global {FC with static := true} 1 0 none skipStmt (L0 EB)) := by
  exact execS_succ global {FC with static := true} 0 (at_zero global) 0 none skipStmt (L0 EB)
end Solidity.Lowering.Readonly.SourceStatementControls
