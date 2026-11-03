import Solidity.Yul.ClosedHorizon
import Solidity.Source.Semantics

/-! Adapt the closed evaluator's horizons to S03's EXISTING firstDone.
This does not embed Yul statements in Source.RStmt or model dirty Solidity locals. -/
namespace Solidity.Yul.Closed

def sourceResult {α : Type} : Option α → Except Solidity.Source.Halt α × Unit
  | none => (.error .timeout, ())
  | some result => (.ok result, ())

theorem sourceResult_done {α : Type} (result : Option α) :
    Solidity.Source.Done (sourceResult result) = result.isSome := by
  cases result <;> rfl

theorem firstDone_none_iff {α : Type} (run : Nat → Option α) :
    (∀ bound, Solidity.Source.firstDone (fun fuel => sourceResult (run fuel)) bound = none) ↔
      ∀ fuel, run fuel = none := by
  rw [Solidity.Source.firstDone_none_iff]
  constructor
  · intro h fuel
    have hd := h fuel
    rw [sourceResult_done] at hd
    cases hr : run fuel with
    | none => rfl
    | some result => rw [hr] at hd; cases hd
  · intro h fuel
    rw [h fuel]
    rfl

theorem evalStmt_firstDone_agrees {bound chosen : Nat} {F c n}
    (env : FunctionEnv F) (he : EnvWordP env) (s : Stmt F [] c n)
    (h : StmtWordP s) (vars : Values n) {result : Except Solidity.Source.Halt (Outcome c n) × Unit}
    (selected : Solidity.Source.firstDone
      (fun fuel => sourceResult (evalStmt fuel env he s h vars)) bound = some (chosen, result)) :
    result = sourceResult (evalStmt bound env he s h vars) := by
  obtain ⟨hle, hr, hd⟩ := Solidity.Source.firstDone_spec selected
  cases runChosen : evalStmt chosen env he s h vars with
  | none =>
    rw [runChosen] at hd
    cases hd
  | some out =>
    have runBound := evalStmt_stable hle env he s h vars runChosen
    rw [hr, runChosen, runBound]

theorem evalExpr_firstDone_agrees {bound chosen : Nat} {F n r}
    (env : FunctionEnv F) (he : EnvWordP env) (e : Expr F [] n r)
    (h : ExprWordP e) (vars : Values n) {result : Except Solidity.Source.Halt (Values r) × Unit}
    (selected : Solidity.Source.firstDone
      (fun fuel => sourceResult (evalExpr fuel env he e h vars)) bound = some (chosen, result)) :
    result = sourceResult (evalExpr bound env he e h vars) := by
  obtain ⟨hle, hr, hd⟩ := Solidity.Source.firstDone_spec selected
  cases runChosen : evalExpr chosen env he e h vars with
  | none =>
    rw [runChosen] at hd
    cases hd
  | some out =>
    have runBound := evalExpr_stable hle env he e h vars runChosen
    rw [hr, runChosen, runBound]

end Solidity.Yul.Closed
