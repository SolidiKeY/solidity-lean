import Solidity.Lowering.Readonly.SourceLoopEffects
import Solidity.Source.SemanticsExamples

/-! Finite actual Source controls, including dirty timeout and static refusal.
No transaction rollback or native execution is inferred. -/
namespace Solidity.Lowering.Readonly.SourceLoopControls
open Solidity.Source Solidity.Source.SemanticsExamples
def set (k : Nat) (h : (Q.ofInt k).FitsInt IntTy.u256 := by decide) :
    RExpr EB [] uint := .assign (.state dX dX_ty rfl) (lit k h)
def writeBreak : RStmt EB [] false ⟨true, false⟩ [] [] :=
  .block (.stmt (.expr (set 4)) (.stmt .brk .nil))
def run (mode : Bool) (n : Nat) (condition : ROptBool EB [])
    (post : ROptExpr EB []) (body : RStmt EB [] false ⟨true,false⟩ [] []) :=
  (forIter (GB (fun _ => .answer (.success []))) {FC with static := mode}
    n 0 none condition post body (L0 EB)).run (L0 EB, sB)
def status {α : Type} (r : Except Halt α) : Nat :=
  match r with
  | .ok _ => 0
  | .error .timeout => 1
  | .error (.revert _) => 2
  | .error (.stuck _) => 3
def breakRun := run false 12 .none (.some (set 9)) writeBreak
def staticWrite := run true 12 .none (.some (set 9)) writeBreak
def falseRun := run true 12 (.some (.bool false)) (.some (set 9)) writeBreak
def continueRun := run false 12 .none (.some (set 9)) .cont
def staticPost := run true 12 .none (.some (set 9)) .cont
theorem break_value : readX breakRun.2.2 = some 4 := by decide
theorem break_skips_post : readX breakRun.2.2 ≠ some 9 := by decide
theorem break_success : status breakRun.1 = 0 := by decide
theorem static_write_refused : status staticWrite.1 = 2 := by decide
theorem static_write_kept : readX staticWrite.2.2 = some 3 := by decide
theorem false_skips_body : status falseRun.1 = 0 ∧ readX falseRun.2.2 = some 3 := by decide
theorem continue_post_and_timeout : status continueRun.1 = 1 ∧ readX continueRun.2.2 = some 9 := by decide
theorem static_post_refused : status staticPost.1 = 2 ∧ readX staticPost.2.2 = some 3 := by decide
theorem zero_timeout : status (run true 0 .none .none .brk).1 = 1 := by decide
theorem one_timeout : status (run true 1 .none .none .brk).1 = 1 := by decide
theorem break_static_success : status (run true 2 .none .none .brk).1 = 0 := by decide
theorem static_write_exact : staticWrite.1 = .error (.revert []) := by rfl
theorem static_post_exact : staticPost.1 = .error (.revert []) := by rfl
def returnRun := run true 4 .none (.some (set 9)) (.ret rfl)
theorem return_exit : (match returnRun.1 with | .ok (.ret _) => true | _ => false) = true := by decide
theorem return_skips_post : readX returnRun.2.2 = some 3 := by decide
end Solidity.Lowering.Readonly.SourceLoopControls
