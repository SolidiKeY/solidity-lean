import Solidity.Yul.LocalCompareControl
import Solidity.Yul.LocalU8CompareHorizon
import Solidity.Yul.LocalBoolHorizon

/-! Exact terminal fuel stability for the existing comparison/Boolean conditional.
Concrete comparison and selected-branch horizon producers are composed here.
Timeout prefixes and broader admission/readback/adequacy remain separate. -/
namespace Solidity.Yul.LocalCompareHorizon

theorem successor : ∀ (env : Solidity.Source.Env) (ctx : Solidity.Source.RCtx)
 (left right : Solidity.Source.RExpr env ctx Solidity.Yul.LocalU8Expr.Ty)
 (yes no : Solidity.Source.RExpr env ctx .bool) (op : Solidity.Source.BinOp)
 (one : Solidity.Yul.LocalU8Expr.Supported env ctx left)
 (two : Solidity.Yul.LocalU8Expr.Supported env ctx right)
 (yesProof : Solidity.Yul.LocalBoolControl.Supported env ctx yes)
 (noProof : Solidity.Yul.LocalBoolControl.Supported env ctx no)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (state : Solidity.Yul.LocalState env ctx),
 (Solidity.Yul.LocalCompareControl.eval op one two yesProof noProof pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.LocalCompareControl.eval op one two yesProof noProof pipeline (fuel+1) state =
 Solidity.Yul.LocalCompareControl.eval op one two yesProof noProof pipeline fuel state := by
  intro env ctx left right yes no op one two yesProof noProof pipeline fuel state terminal
  cases fuel with
  | zero => exact False.elim (terminal rfl)
  | succ fuel =>
    cases actual : Solidity.Yul.LocalU8Compare.compare op one two pipeline fuel state with
    | mk result next =>
      cases result with
      | error halt =>
        have ready : (Solidity.Yul.LocalU8Compare.compare op one two pipeline fuel state).1 ≠ .error .timeout := by
          simpa only [Solidity.Yul.LocalCompareControl.step,actual] using terminal
        have same := Solidity.Yul.LocalU8CompareHorizon.successor env ctx left right op one two pipeline fuel state ready
        simp only [Solidity.Yul.LocalCompareControl.step,same,actual]
      | ok value =>
        have ready : (Solidity.Yul.LocalU8Compare.compare op one two pipeline fuel state).1 ≠ .error .timeout := by
          rw [actual]
          intro impossible
          cases impossible
        have same := Solidity.Yul.LocalU8CompareHorizon.successor env ctx left right op one two pipeline fuel state ready
        cases choice : Solidity.Yul.LocalBoolControl.truth value with
        | false =>
          have branchReady : (Solidity.Yul.LocalBoolControl.eval noProof fuel next).1 ≠ .error .timeout := by
            simpa only [Solidity.Yul.LocalCompareControl.step,actual,choice] using terminal
          have branchSame := Solidity.Yul.LocalBoolHorizon.successor env ctx no noProof fuel next branchReady
          simp only [Solidity.Yul.LocalCompareControl.step,same,actual,choice,branchSame,Bool.false_eq_true,if_false]
        | true =>
          have branchReady : (Solidity.Yul.LocalBoolControl.eval yesProof fuel next).1 ≠ .error .timeout := by
            simpa only [Solidity.Yul.LocalCompareControl.step,actual,choice] using terminal
          have branchSame := Solidity.Yul.LocalBoolHorizon.successor env ctx yes yesProof fuel next branchReady
          simp only [Solidity.Yul.LocalCompareControl.step,same,actual,choice,branchSame,if_true]

theorem extension : ∀ (env : Solidity.Source.Env) (ctx : Solidity.Source.RCtx)
 (left right : Solidity.Source.RExpr env ctx Solidity.Yul.LocalU8Expr.Ty)
 (yes no : Solidity.Source.RExpr env ctx .bool) (op : Solidity.Source.BinOp)
 (one : Solidity.Yul.LocalU8Expr.Supported env ctx left)
 (two : Solidity.Yul.LocalU8Expr.Supported env ctx right)
 (yesProof : Solidity.Yul.LocalBoolControl.Supported env ctx yes)
 (noProof : Solidity.Yul.LocalBoolControl.Supported env ctx no)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel extra : Nat)
 (state : Solidity.Yul.LocalState env ctx),
 (Solidity.Yul.LocalCompareControl.eval op one two yesProof noProof pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.LocalCompareControl.eval op one two yesProof noProof pipeline (fuel+extra) state =
 Solidity.Yul.LocalCompareControl.eval op one two yesProof noProof pipeline fuel state := by
  intro env ctx left right yes no op one two yesProof noProof pipeline fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have stillTerminal : (Solidity.Yul.LocalCompareControl.eval op one two yesProof noProof pipeline (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (Solidity.Yul.LocalCompareHorizon.successor env ctx left right yes no op one two yesProof noProof pipeline (fuel+extra) state stillTerminal).trans ih

end Solidity.Yul.LocalCompareHorizon
