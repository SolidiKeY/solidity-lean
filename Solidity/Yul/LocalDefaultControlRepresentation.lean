import Solidity.Yul.LocalDefaultRepresentation
import Solidity.Yul.LocalDefaultIfElse
import Solidity.Yul.LocalDefaultDoWhile

/-! Exact-word congruence for existing heterogeneous branch and loop scopes.
No clean projection or Source admission equivalence is asserted. -/
namespace Solidity.Yul.LocalDefaultControlRepresentation

theorem ifElse : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types yesOut noOut : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (yesItems : Solidity.Source.RItems env returns modifier control types yesOut)
 (yes : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control yesItems)
 (noItems : Solidity.Source.RItems env returns modifier control types noOut)
 (no : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control noItems)
 (fuel : Nat) (one two : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolRepresentation.State one two →
 Solidity.Yul.LocalBoolItemRepresentation.Items env types
 (Solidity.Yul.LocalDefaultIfElse.run test yes no fuel one)
 (Solidity.Yul.LocalDefaultIfElse.run test yes no fuel two) := by

  intro env returns modifier control types yesOut noOut condition test yesItems yes noItems no fuel one two given
  cases fuel with
  | zero => exact .halted .timeout given
  | succ fuel =>
    have compared := Solidity.Yul.LocalBoolControlRepresentation.control
      env types condition test fuel one two given
    cases leftActual : Solidity.Yul.LocalBoolControl.eval test fuel one with
    | mk leftResult leftState =>
      cases rightActual : Solidity.Yul.LocalBoolControl.eval test fuel two with
      | mk rightResult rightState =>
        rw [leftActual,rightActual] at compared
        rcases compared with ⟨outcomes,states⟩
        rcases Solidity.Yul.LocalBoolRepresentation.outcome_cases env leftResult rightResult outcomes with
          ⟨halt,leftTag,rightTag⟩ | ⟨leftValue,rightValue,leftTag,rightTag,words⟩
        · simp only [Solidity.Yul.LocalDefaultIfElse.run,leftActual,rightActual,leftTag,rightTag]
          exact .halted halt states
        · simp only [Solidity.Yul.LocalDefaultIfElse.run,leftActual,rightActual,leftTag,rightTag]
          have choices := Solidity.Yul.LocalBoolRepresentation.truth_congr env leftValue rightValue words
          simp only [← choices]
          cases choice : Solidity.Yul.LocalBoolControl.truth leftValue with
          | false =>
            simp only [Bool.false_eq_true,if_false]
            exact Solidity.Yul.LocalDefaultRepresentation.block
              env returns modifier control types noOut noItems no fuel leftState rightState states
          | true =>
            simp only [if_true]
            exact Solidity.Yul.LocalDefaultRepresentation.block
              env returns modifier control types yesOut yesItems yes fuel leftState rightState states

theorem whileLoop : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (body : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (proof : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ body)
 (fuel : Nat) (one two : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolRepresentation.State one two →
 Solidity.Yul.LocalBoolItemRepresentation.Items env types
 (Solidity.Yul.LocalDefaultWhile.run test proof fuel one)
 (Solidity.Yul.LocalDefaultWhile.run test proof fuel two) := by

  intro env returns modifier u types out condition test body proof fuel
  induction fuel with
  | zero =>
    intro one two given
    exact .halted .timeout given
  | succ fuel ih =>
    intro one two given
    have compared := Solidity.Yul.LocalBoolControlRepresentation.control
      env types condition test fuel one two given
    cases leftActual : Solidity.Yul.LocalBoolControl.eval test fuel one with
    | mk leftResult leftState =>
      cases rightActual : Solidity.Yul.LocalBoolControl.eval test fuel two with
      | mk rightResult rightState =>
        rw [leftActual,rightActual] at compared
        rcases compared with ⟨outcomes,states⟩
        rcases Solidity.Yul.LocalBoolRepresentation.outcome_cases env leftResult rightResult outcomes with
          ⟨halt,leftTag,rightTag⟩ | ⟨leftValue,rightValue,leftTag,rightTag,words⟩
        · conv => lhs; rw [Solidity.Yul.LocalDefaultWhile.run]
          conv => rhs; rw [Solidity.Yul.LocalDefaultWhile.run]
          simp only [leftActual,rightActual,leftTag,rightTag]
          exact .halted halt states
        · conv => lhs; rw [Solidity.Yul.LocalDefaultWhile.run]
          conv => rhs; rw [Solidity.Yul.LocalDefaultWhile.run]
          simp only [leftActual,rightActual,leftTag,rightTag]
          have choices := Solidity.Yul.LocalBoolRepresentation.truth_congr env leftValue rightValue words
          simp only [← choices]
          cases choice : Solidity.Yul.LocalBoolControl.truth leftValue with
          | false =>
            simp only [Bool.false_eq_true,if_false]
            exact .normal states
          | true =>
            simp only [if_true]
            have bodies := Solidity.Yul.LocalDefaultRepresentation.block
              env returns modifier ⟨true,u⟩ types out body proof fuel leftState rightState states
            generalize leftBody : Solidity.Yul.LocalDefaultItems.blockRun proof fuel leftState = leftRun at bodies ⊢
            generalize rightBody : Solidity.Yul.LocalDefaultItems.blockRun proof fuel rightState = rightRun at bodies ⊢
            cases bodies with
            | normal states => exact ih _ _ states
            | halted halt states => exact .halted halt states


theorem doWhileLoop : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (body : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (proof : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ body)
 (fuel : Nat) (one two : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolRepresentation.State one two →
 Solidity.Yul.LocalBoolItemRepresentation.Items env types
 (Solidity.Yul.LocalDefaultDoWhile.run test proof fuel one)
 (Solidity.Yul.LocalDefaultDoWhile.run test proof fuel two) := by

  intro env returns modifier u types out condition test body proof fuel
  induction fuel with
  | zero =>
    intro one two given
    exact .halted .timeout given
  | succ fuel ih =>
    intro one two given
    have bodies := Solidity.Yul.LocalDefaultRepresentation.block
      env returns modifier ⟨true,u⟩ types out body proof fuel one two given
    conv => lhs; rw [Solidity.Yul.LocalDefaultDoWhile.run]
    conv => rhs; rw [Solidity.Yul.LocalDefaultDoWhile.run]
    generalize leftBody : Solidity.Yul.LocalDefaultItems.blockRun proof fuel one = leftRun at bodies ⊢
    generalize rightBody : Solidity.Yul.LocalDefaultItems.blockRun proof fuel two = rightRun at bodies ⊢
    cases bodies with
    | halted halt states => exact .halted halt states
    | @normal leftState rightState states =>
      have compared := Solidity.Yul.LocalBoolControlRepresentation.control
        env types condition test fuel leftState rightState states
      cases leftActual : Solidity.Yul.LocalBoolControl.eval test fuel leftState with
      | mk leftResult leftNext =>
        cases rightActual : Solidity.Yul.LocalBoolControl.eval test fuel rightState with
        | mk rightResult rightNext =>
          rw [leftActual,rightActual] at compared
          rcases compared with ⟨outcomes,nextStates⟩
          rcases Solidity.Yul.LocalBoolRepresentation.outcome_cases env leftResult rightResult outcomes with
            ⟨halt,leftTag,rightTag⟩ | ⟨leftValue,rightValue,leftTag,rightTag,words⟩
          · simp only [leftActual,rightActual,leftTag,rightTag]
            exact .halted halt nextStates
          · simp only [leftActual,rightActual,leftTag,rightTag]
            have choices := Solidity.Yul.LocalBoolRepresentation.truth_congr env leftValue rightValue words
            simp only [← choices]
            cases choice : Solidity.Yul.LocalBoolControl.truth leftValue with
            | false =>
              simp only [Bool.false_eq_true,if_false]
              exact .normal nextStates
            | true =>
              simp only [if_true]
              exact ih leftNext rightNext nextStates


end Solidity.Yul.LocalDefaultControlRepresentation
