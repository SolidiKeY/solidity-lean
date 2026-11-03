import Solidity.Yul.LocalU8Compare
import Solidity.Yul.LocalBoolControlAgreement
import Solidity.Yul.LocalBoolControlEvidence

/-! Actual Source conditional combining uint8 comparison and boolean control
consumers. No new AST or general admission claim. Raw branch results and all
partial writes are preserved; clean agreement retains the checked-frame premise
required by arithmetic inside comparison operands. -/
namespace Solidity.Yul.LocalCompareControl

def eval {env ctx left right yes no} (op : Solidity.Source.BinOp)
    (one : LocalU8Expr.Supported env ctx left) (two : LocalU8Expr.Supported env ctx right)
    (yesProof : LocalBoolControl.Supported env ctx yes)
    (noProof : LocalBoolControl.Supported env ctx no)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : LocalState env ctx) :
    Solidity.Source.R (LocalValue env .bool) × LocalState env ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | fuel+1 =>
      let (result,next) := LocalU8Compare.compare op one two pipeline fuel state
      match result with
      | .error halt => (.error halt,next)
      | .ok value => if LocalBoolControl.truth value then
          LocalBoolControl.eval yesProof fuel next else LocalBoolControl.eval noProof fuel next

theorem step {env ctx left right yes no} (op : Solidity.Source.BinOp)
    (one : LocalU8Expr.Supported env ctx left) (two : LocalU8Expr.Supported env ctx right)
    (yesProof : LocalBoolControl.Supported env ctx yes)
    (noProof : LocalBoolControl.Supported env ctx no)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : LocalState env ctx) :
    eval op one two yesProof noProof pipeline (fuel+1) state =
      (let (result,next) := LocalU8Compare.compare op one two pipeline fuel state
       match result with
       | .error halt => (.error halt,next)
       | .ok value => if LocalBoolControl.truth value then
           LocalBoolControl.eval yesProof fuel next else LocalBoolControl.eval noProof fuel next) := rfl

/-- Final concrete equality supplies the comparison and BOTH branch laws from
actual producer theorems; there is no assumed branch or simulation premise. -/
theorem source_agrees {env ctx left right yes no} (op : Solidity.Source.BinOp)
    (one : LocalU8Expr.Supported env ctx left) (two : LocalU8Expr.Supported env ctx right)
    (yesProof : LocalBoolControl.Supported env ctx yes)
    (noProof : LocalBoolControl.Supported env ctx no)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
    (checked : frame.checked = true) (fuel : Nat)
    (state : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env) :
    eval op one two yesProof noProof glob.pipeline fuel (LocalState.ofClean state) =
      LocalBoolExpr.cleanOutcome ((Solidity.Source.evalE glob frame fuel
        (.cond (.compare op left right) yes no)).run state) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      have comparison := LocalU8Compare.source_agrees op one two glob frame checked fuel state
      cases actual : (Solidity.Source.evalE glob frame fuel (.compare op left right)).run state with
      | mk result next =>
          rw [actual] at comparison
          cases result with
          | error halt =>
              change LocalU8Compare.compare op one two glob.pipeline fuel (LocalState.ofClean state) =
                (.error halt,LocalState.ofClean next) at comparison
              rw [step,comparison,LocalBoolControl.source_cond_error
                (.compare op left right) yes no glob frame fuel state next halt actual]
              rfl
          | ok value =>
              cases value with
              | val value =>
                  cases value with
                  | bool value =>
                      change LocalU8Compare.compare op one two glob.pipeline fuel (LocalState.ofClean state) =
                        (.ok (.clean (.bool value)),LocalState.ofClean next) at comparison
                      cases value with
                      | false =>
                          rw [step,comparison,LocalBoolControl.source_cond_false
                            (.compare op left right) yes no glob frame fuel state next actual]
                          simp only [LocalBoolControl.truth_clean,Bool.false_eq_true,if_false]
                          exact LocalBoolControl.source_agrees noProof glob frame fuel next
                      | true =>
                          rw [step,comparison,LocalBoolControl.source_cond_true
                            (.compare op left right) yes no glob frame fuel state next actual]
                          simp only [LocalBoolControl.truth_clean,if_true]
                          exact LocalBoolControl.source_agrees yesProof glob frame fuel next
                  | memRef impossible _ => cases impossible
                  | storRef impossible _ => cases impossible
                  | cdRef impossible _ => cases impossible

theorem world {env ctx left right yes no} (op : Solidity.Source.BinOp)
    (one : LocalU8Expr.Supported env ctx left) (two : LocalU8Expr.Supported env ctx right)
    (yesProof : LocalBoolControl.Supported env ctx yes)
    (noProof : LocalBoolControl.Supported env ctx no)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : LocalState env ctx) :
    (eval op one two yesProof noProof pipeline fuel state).2.2 = state.2 := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      have unchanged := LocalU8Compare.world op one two pipeline fuel state
      cases actual : LocalU8Compare.compare op one two pipeline fuel state with
      | mk result next =>
          rw [actual] at unchanged
          rw [step,actual]
          cases result with
          | error halt => exact unchanged
          | ok value =>
              dsimp only
              split
              · exact (LocalBoolControl.world yesProof fuel next).trans unchanged
              · exact (LocalBoolControl.world noProof fuel next).trans unchanged

end Solidity.Yul.LocalCompareControl
