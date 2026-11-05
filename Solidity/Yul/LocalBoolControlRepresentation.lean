import Solidity.Yul.LocalBoolRepresentation

/-! Exact-word congruence for the existing six-form local Boolean evaluator.
This proof relation does not identify clean projections or certify admission. -/
namespace Solidity.Yul.LocalBoolControlRepresentation

theorem control : ∀ (env : Solidity.Source.Env) (ctx : Solidity.Source.RCtx)
 (expr : Solidity.Source.RExpr env ctx .bool)
 (proof : Solidity.Yul.LocalBoolControl.Supported env ctx expr)
 (fuel : Nat) (one two : Solidity.Yul.LocalState env ctx),
 Solidity.Yul.LocalBoolRepresentation.State one two →
 Solidity.Yul.LocalBoolRepresentation.Run
 (Solidity.Yul.LocalBoolControl.eval proof fuel one)
 (Solidity.Yul.LocalBoolControl.eval proof fuel two) := by

  intro env ctx expr proof
  induction proof with
  | base child =>
    exact Solidity.Yul.LocalBoolRepresentation.expression env ctx _ child
  | and left right ihLeft ihRight =>
    intro fuel one two given
    cases fuel with
    | zero =>
      rw [Solidity.Yul.LocalBoolControl.zero,Solidity.Yul.LocalBoolControl.zero]
      exact ⟨.same _,given⟩
    | succ fuel =>
      have compared := ihLeft fuel one two given
      cases leftActual : Solidity.Yul.LocalBoolControl.eval left fuel one with
      | mk leftResult leftState =>
        cases rightActual : Solidity.Yul.LocalBoolControl.eval left fuel two with
        | mk rightResult rightState =>
          rw [leftActual,rightActual] at compared
          rcases compared with ⟨outcomes,states⟩
          rcases Solidity.Yul.LocalBoolRepresentation.outcome_cases env leftResult rightResult outcomes with
            ⟨halt,leftTag,rightTag⟩ | ⟨leftValue,rightValue,leftTag,rightTag,words⟩
          · simp only [Solidity.Yul.LocalBoolControl.and_step,leftActual,rightActual,leftTag,rightTag]
            exact ⟨.same _,states⟩
          · simp only [Solidity.Yul.LocalBoolControl.and_step,leftActual,rightActual,leftTag,rightTag]
            have choices := Solidity.Yul.LocalBoolRepresentation.truth_congr env leftValue rightValue words
            simp only [← choices]
            cases choice : Solidity.Yul.LocalBoolControl.truth leftValue with
            | false =>
              simp only [Bool.false_eq_true,if_false]
              exact ⟨.boolean words,states⟩
            | true =>
              simp only [if_true]
              exact ihRight fuel leftState rightState states
  | or left right ihLeft ihRight =>
    intro fuel one two given
    cases fuel with
    | zero =>
      rw [Solidity.Yul.LocalBoolControl.zero,Solidity.Yul.LocalBoolControl.zero]
      exact ⟨.same _,given⟩
    | succ fuel =>
      have compared := ihLeft fuel one two given
      cases leftActual : Solidity.Yul.LocalBoolControl.eval left fuel one with
      | mk leftResult leftState =>
        cases rightActual : Solidity.Yul.LocalBoolControl.eval left fuel two with
        | mk rightResult rightState =>
          rw [leftActual,rightActual] at compared
          rcases compared with ⟨outcomes,states⟩
          rcases Solidity.Yul.LocalBoolRepresentation.outcome_cases env leftResult rightResult outcomes with
            ⟨halt,leftTag,rightTag⟩ | ⟨leftValue,rightValue,leftTag,rightTag,words⟩
          · simp only [Solidity.Yul.LocalBoolControl.or_step,leftActual,rightActual,leftTag,rightTag]
            exact ⟨.same _,states⟩
          · simp only [Solidity.Yul.LocalBoolControl.or_step,leftActual,rightActual,leftTag,rightTag]
            have choices := Solidity.Yul.LocalBoolRepresentation.truth_congr env leftValue rightValue words
            simp only [← choices]
            cases choice : Solidity.Yul.LocalBoolControl.truth leftValue with
            | false =>
              simp only [Bool.false_eq_true,if_false]
              exact ihRight fuel leftState rightState states
            | true =>
              simp only [if_true]
              exact ⟨.boolean words,states⟩
  | cond test yes no ihTest ihYes ihNo =>
    intro fuel one two given
    cases fuel with
    | zero =>
      rw [Solidity.Yul.LocalBoolControl.zero,Solidity.Yul.LocalBoolControl.zero]
      exact ⟨.same _,given⟩
    | succ fuel =>
      have compared := ihTest fuel one two given
      cases leftActual : Solidity.Yul.LocalBoolControl.eval test fuel one with
      | mk leftResult leftState =>
        cases rightActual : Solidity.Yul.LocalBoolControl.eval test fuel two with
        | mk rightResult rightState =>
          rw [leftActual,rightActual] at compared
          rcases compared with ⟨outcomes,states⟩
          rcases Solidity.Yul.LocalBoolRepresentation.outcome_cases env leftResult rightResult outcomes with
            ⟨halt,leftTag,rightTag⟩ | ⟨leftValue,rightValue,leftTag,rightTag,words⟩
          · simp only [Solidity.Yul.LocalBoolControl.cond_step,leftActual,rightActual,leftTag,rightTag]
            exact ⟨.same _,states⟩
          · simp only [Solidity.Yul.LocalBoolControl.cond_step,leftActual,rightActual,leftTag,rightTag]
            have choices := Solidity.Yul.LocalBoolRepresentation.truth_congr env leftValue rightValue words
            simp only [← choices]
            cases choice : Solidity.Yul.LocalBoolControl.truth leftValue with
            | false =>
              simp only [Bool.false_eq_true,if_false]
              exact ihNo fuel leftState rightState states
            | true =>
              simp only [if_true]
              exact ihYes fuel leftState rightState states
  | not child ihChild =>
    intro fuel one two given
    cases fuel with
    | zero =>
      rw [Solidity.Yul.LocalBoolControl.zero,Solidity.Yul.LocalBoolControl.zero]
      exact ⟨.same _,given⟩
    | succ fuel =>
      have compared := ihChild fuel one two given
      cases leftActual : Solidity.Yul.LocalBoolControl.eval child fuel one with
      | mk leftResult leftState =>
        cases rightActual : Solidity.Yul.LocalBoolControl.eval child fuel two with
        | mk rightResult rightState =>
          rw [leftActual,rightActual] at compared
          rcases compared with ⟨outcomes,states⟩
          rcases Solidity.Yul.LocalBoolRepresentation.outcome_cases env leftResult rightResult outcomes with
            ⟨halt,leftTag,rightTag⟩ | ⟨leftValue,rightValue,leftTag,rightTag,words⟩
          · simp only [Solidity.Yul.LocalBoolControl.not_step,leftActual,rightActual,leftTag,rightTag]
            exact ⟨.same _,states⟩
          · simp only [Solidity.Yul.LocalBoolControl.not_step,leftActual,rightActual,leftTag,rightTag]
            change Solidity.Yul.LocalBoolRepresentation.Outcome env
              (Solidity.Yul.LocalOperations.boolNot leftValue)
              (Solidity.Yul.LocalOperations.boolNot rightValue) ∧ _
            rw [Solidity.Yul.LocalBoolRepresentation.not_congr env leftValue rightValue words]
            exact ⟨.same _,states⟩
  | assign index child ihChild =>
    intro fuel one two given
    cases fuel with
    | zero =>
      rw [Solidity.Yul.LocalBoolControl.zero,Solidity.Yul.LocalBoolControl.zero]
      exact ⟨.same _,given⟩
    | succ fuel =>
      have compared := ihChild fuel one two given
      cases leftActual : Solidity.Yul.LocalBoolControl.eval child fuel one with
      | mk leftResult leftState =>
        cases rightActual : Solidity.Yul.LocalBoolControl.eval child fuel two with
        | mk rightResult rightState =>
          rw [leftActual,rightActual] at compared
          rcases compared with ⟨outcomes,states⟩
          rcases Solidity.Yul.LocalBoolRepresentation.outcome_cases env leftResult rightResult outcomes with
            ⟨halt,leftTag,rightTag⟩ | ⟨leftValue,rightValue,leftTag,rightTag,words⟩
          · simp only [Solidity.Yul.LocalBoolControl.assign_step,leftActual,rightActual,leftTag,rightTag]
            exact ⟨.same _,states⟩
          · simp only [Solidity.Yul.LocalBoolControl.assign_step,leftActual,rightActual,leftTag,rightTag]
            exact ⟨.boolean words,⟨Solidity.Yul.LocalBoolRepresentation.write env ctx .bool index
              leftState.1 rightState.1 leftValue rightValue states.1 (.boolean words),states.2⟩⟩


end Solidity.Yul.LocalBoolControlRepresentation
