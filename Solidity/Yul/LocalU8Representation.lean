import Solidity.Yul.LocalBoolRepresentation
import Solidity.Yul.LocalCompareControl
import Solidity.Yul.LocalBoolControlRepresentation

/-! Exact checked-u8 result congruence over the existing local-frame relation.
Pipeline-specific operand order and all exact errors/partial states are retained.
No unchecked, readback, admission or cross-pipeline equality is asserted. -/
namespace Solidity.Yul.LocalU8Representation

def Run {env : Solidity.Source.Env} {ctx : Solidity.Source.RCtx}
    (one two : Solidity.Source.R (LocalValue env LocalU8Expr.Ty) × LocalState env ctx) : Prop :=
  one.1 = two.1 ∧ LocalBoolRepresentation.State one.2 two.2

theorem value_eq : ∀ (env : Solidity.Source.Env)
 (one two : Solidity.Yul.LocalValue env Solidity.Yul.LocalU8Expr.Ty),
 Solidity.Yul.LocalBoolRepresentation.Value env one two → one = two := by

  intro env one two given
  cases given
  rfl

theorem expression : ∀ (env : Solidity.Source.Env) (ctx : Solidity.Source.RCtx)
 (expr : Solidity.Source.RExpr env ctx Solidity.Yul.LocalU8Expr.Ty)
 (proof : Solidity.Yul.LocalU8Expr.Supported env ctx expr)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (one two : Solidity.Yul.LocalState env ctx),
 Solidity.Yul.LocalBoolRepresentation.State one two →
 Solidity.Yul.LocalU8Representation.Run
 (Solidity.Yul.LocalU8Expr.eval proof pipeline fuel one)
 (Solidity.Yul.LocalU8Expr.eval proof pipeline fuel two) := by

  intro env ctx expr proof
  induction proof with
  | «local» index =>
    intro pipeline fuel one two given
    cases fuel with
    | zero => exact ⟨rfl,given⟩
    | succ fuel =>
      have same := Solidity.Yul.LocalU8Representation.value_eq env _ _
        (Solidity.Yul.LocalBoolRepresentation.read env ctx one.1 two.1 given.1 _ index)
      exact ⟨congrArg Except.ok same,given⟩
  | assign index child ih =>
    intro pipeline fuel one two given
    cases fuel with
    | zero => exact ⟨rfl,given⟩
    | succ fuel =>
      have compared := ih pipeline fuel one two given
      cases leftActual : Solidity.Yul.LocalU8Expr.eval child pipeline fuel one with
      | mk leftResult leftState =>
        cases rightActual : Solidity.Yul.LocalU8Expr.eval child pipeline fuel two with
        | mk rightResult rightState =>
          rw [leftActual,rightActual] at compared
          rcases compared with ⟨same,states⟩
          simp only [Solidity.Yul.LocalU8Expr.assign_step,leftActual,rightActual,← same]
          cases leftResult with
          | error halt => exact ⟨rfl,states⟩
          | ok value =>
            exact ⟨rfl,⟨Solidity.Yul.LocalBoolRepresentation.write env ctx _ index
              leftState.1 rightState.1 value value states.1 (.same value),states.2⟩⟩
  | add left right ihLeft ihRight =>
    intro pipeline fuel one two given
    cases fuel with
    | zero => exact ⟨rfl,given⟩
    | succ fuel =>
      cases fuel with
      | zero => exact ⟨rfl,given⟩
      | succ fuel =>
        cases pipeline with
        | legacy =>
          have first := ihRight .legacy fuel one two given
          cases firstLeft : Solidity.Yul.LocalU8Expr.eval right .legacy fuel one with
          | mk firstResult firstState =>
            cases firstRight : Solidity.Yul.LocalU8Expr.eval right .legacy fuel two with
            | mk otherResult otherState =>
              rw [firstLeft,firstRight] at first
              rcases first with ⟨firstSame,firstStates⟩
              simp only [Solidity.Yul.LocalU8Expr.add_legacy,firstLeft,firstRight,← firstSame]
              cases firstResult with
              | error halt => exact ⟨rfl,firstStates⟩
              | ok firstValue =>
                have second := ihLeft .legacy fuel firstState otherState firstStates
                cases secondLeft : Solidity.Yul.LocalU8Expr.eval left .legacy fuel firstState with
                | mk secondResult secondState =>
                  cases secondRight : Solidity.Yul.LocalU8Expr.eval left .legacy fuel otherState with
                  | mk lastResult lastState =>
                    rw [secondLeft,secondRight] at second
                    rcases second with ⟨secondSame,secondStates⟩
                    change
                      secondResult.bind (fun value => Solidity.Yul.LocalOperations.u8Binary true .add value firstValue) =
                      lastResult.bind (fun value => Solidity.Yul.LocalOperations.u8Binary true .add value firstValue) ∧
                      Solidity.Yul.LocalBoolRepresentation.State secondState lastState
                    exact ⟨congrArg
                      (fun result : Solidity.Source.R (Solidity.Yul.LocalValue env Solidity.Yul.LocalU8Expr.Ty) =>
                        result.bind (fun value => Solidity.Yul.LocalOperations.u8Binary true .add value firstValue))
                      secondSame,secondStates⟩
        | viaIR =>
          have first := ihLeft .viaIR fuel one two given
          cases firstLeft : Solidity.Yul.LocalU8Expr.eval left .viaIR fuel one with
          | mk firstResult firstState =>
            cases firstRight : Solidity.Yul.LocalU8Expr.eval left .viaIR fuel two with
            | mk otherResult otherState =>
              rw [firstLeft,firstRight] at first
              rcases first with ⟨firstSame,firstStates⟩
              simp only [Solidity.Yul.LocalU8Expr.add_viaIR,firstLeft,firstRight,← firstSame]
              cases firstResult with
              | error halt => exact ⟨rfl,firstStates⟩
              | ok firstValue =>
                have second := ihRight .viaIR fuel firstState otherState firstStates
                cases secondLeft : Solidity.Yul.LocalU8Expr.eval right .viaIR fuel firstState with
                | mk secondResult secondState =>
                  cases secondRight : Solidity.Yul.LocalU8Expr.eval right .viaIR fuel otherState with
                  | mk lastResult lastState =>
                    rw [secondLeft,secondRight] at second
                    rcases second with ⟨secondSame,secondStates⟩
                    change
                      secondResult.bind (fun value => Solidity.Yul.LocalOperations.u8Binary true .add firstValue value) =
                      lastResult.bind (fun value => Solidity.Yul.LocalOperations.u8Binary true .add firstValue value) ∧
                      Solidity.Yul.LocalBoolRepresentation.State secondState lastState
                    exact ⟨congrArg
                      (fun result : Solidity.Source.R (Solidity.Yul.LocalValue env Solidity.Yul.LocalU8Expr.Ty) =>
                        result.bind (fun value => Solidity.Yul.LocalOperations.u8Binary true .add firstValue value))
                      secondSame,secondStates⟩


theorem comparison : ∀ (env : Solidity.Source.Env) (ctx : Solidity.Source.RCtx)
 (left right : Solidity.Source.RExpr env ctx Solidity.Yul.LocalU8Expr.Ty)
 (op : Solidity.Source.BinOp)
 (first : Solidity.Yul.LocalU8Expr.Supported env ctx left)
 (second : Solidity.Yul.LocalU8Expr.Supported env ctx right)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (one two : Solidity.Yul.LocalState env ctx),
 Solidity.Yul.LocalBoolRepresentation.State one two →
 Solidity.Yul.LocalBoolRepresentation.Run
 (Solidity.Yul.LocalU8Compare.compare op first second pipeline fuel one)
 (Solidity.Yul.LocalU8Compare.compare op first second pipeline fuel two) := by

  intro env ctx left right op first second pipeline fuel one two given
  cases fuel with
  | zero => exact ⟨.same _,given⟩
  | succ fuel =>
    cases fuel with
    | zero => exact ⟨.same _,given⟩
    | succ fuel =>
      cases pipeline with
      | legacy =>
        have headRelated := Solidity.Yul.LocalU8Representation.expression env ctx _ second .legacy fuel one two given
        cases headLeft : Solidity.Yul.LocalU8Expr.eval second .legacy fuel one with
        | mk headResult headState =>
          cases headRight : Solidity.Yul.LocalU8Expr.eval second .legacy fuel two with
          | mk otherResult otherState =>
            rw [headLeft,headRight] at headRelated
            rcases headRelated with ⟨headSame,headStates⟩
            simp only [Solidity.Yul.LocalU8Compare.compare_legacy,headLeft,headRight,← headSame]
            cases headResult with
            | error halt => exact ⟨.same _,headStates⟩
            | ok headValue =>
              have tailRelated := Solidity.Yul.LocalU8Representation.expression
                env ctx _ first .legacy fuel headState otherState headStates
              cases tailLeft : Solidity.Yul.LocalU8Expr.eval first .legacy fuel headState with
              | mk tailResult tailState =>
                cases tailRight : Solidity.Yul.LocalU8Expr.eval first .legacy fuel otherState with
                | mk finalResult finalState =>
                  rw [tailLeft,tailRight] at tailRelated
                  rcases tailRelated with ⟨tailSame,tailStates⟩
                  change Solidity.Yul.LocalBoolRepresentation.Outcome env
                    (tailResult.bind (fun value => Solidity.Yul.LocalU8Compare.operation op value headValue))
                    (finalResult.bind (fun value => Solidity.Yul.LocalU8Compare.operation op value headValue)) ∧
                    Solidity.Yul.LocalBoolRepresentation.State tailState finalState
                  have same : tailResult = finalResult := tailSame
                  rw [same]
                  exact ⟨.same _,tailStates⟩
      | viaIR =>
        have headRelated := Solidity.Yul.LocalU8Representation.expression env ctx _ first .viaIR fuel one two given
        cases headLeft : Solidity.Yul.LocalU8Expr.eval first .viaIR fuel one with
        | mk headResult headState =>
          cases headRight : Solidity.Yul.LocalU8Expr.eval first .viaIR fuel two with
          | mk otherResult otherState =>
            rw [headLeft,headRight] at headRelated
            rcases headRelated with ⟨headSame,headStates⟩
            simp only [Solidity.Yul.LocalU8Compare.compare_viaIR,headLeft,headRight,← headSame]
            cases headResult with
            | error halt => exact ⟨.same _,headStates⟩
            | ok headValue =>
              have tailRelated := Solidity.Yul.LocalU8Representation.expression
                env ctx _ second .viaIR fuel headState otherState headStates
              cases tailLeft : Solidity.Yul.LocalU8Expr.eval second .viaIR fuel headState with
              | mk tailResult tailState =>
                cases tailRight : Solidity.Yul.LocalU8Expr.eval second .viaIR fuel otherState with
                | mk finalResult finalState =>
                  rw [tailLeft,tailRight] at tailRelated
                  rcases tailRelated with ⟨tailSame,tailStates⟩
                  change Solidity.Yul.LocalBoolRepresentation.Outcome env
                    (tailResult.bind (fun value => Solidity.Yul.LocalU8Compare.operation op headValue value))
                    (finalResult.bind (fun value => Solidity.Yul.LocalU8Compare.operation op headValue value)) ∧
                    Solidity.Yul.LocalBoolRepresentation.State tailState finalState
                  have same : tailResult = finalResult := tailSame
                  rw [same]
                  exact ⟨.same _,tailStates⟩


theorem conditional : ∀ (env : Solidity.Source.Env) (ctx : Solidity.Source.RCtx)
 (left right : Solidity.Source.RExpr env ctx Solidity.Yul.LocalU8Expr.Ty)
 (op : Solidity.Source.BinOp)
 (first : Solidity.Yul.LocalU8Expr.Supported env ctx left)
 (second : Solidity.Yul.LocalU8Expr.Supported env ctx right)
 (yes no : Solidity.Source.RExpr env ctx .bool)
 (yesProof : Solidity.Yul.LocalBoolControl.Supported env ctx yes)
 (noProof : Solidity.Yul.LocalBoolControl.Supported env ctx no)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (one two : Solidity.Yul.LocalState env ctx),
 Solidity.Yul.LocalBoolRepresentation.State one two →
 Solidity.Yul.LocalBoolRepresentation.Run
 (Solidity.Yul.LocalCompareControl.eval op first second yesProof noProof pipeline fuel one)
 (Solidity.Yul.LocalCompareControl.eval op first second yesProof noProof pipeline fuel two) := by

  intro env ctx left right op first second yes no yesProof noProof pipeline fuel one two given
  cases fuel with
  | zero => exact ⟨.same _,given⟩
  | succ fuel =>
    have compared := Solidity.Yul.LocalU8Representation.comparison
      env ctx left right op first second pipeline fuel one two given
    cases leftActual : Solidity.Yul.LocalU8Compare.compare op first second pipeline fuel one with
    | mk leftResult leftState =>
      cases rightActual : Solidity.Yul.LocalU8Compare.compare op first second pipeline fuel two with
      | mk rightResult rightState =>
        rw [leftActual,rightActual] at compared
        rcases compared with ⟨outcomes,states⟩
        rcases Solidity.Yul.LocalBoolRepresentation.outcome_cases env leftResult rightResult outcomes with
          ⟨halt,leftTag,rightTag⟩ | ⟨leftValue,rightValue,leftTag,rightTag,words⟩
        · simp only [Solidity.Yul.LocalCompareControl.step,leftActual,rightActual,leftTag,rightTag]
          exact ⟨.same _,states⟩
        · simp only [Solidity.Yul.LocalCompareControl.step,leftActual,rightActual,leftTag,rightTag]
          have choices := Solidity.Yul.LocalBoolRepresentation.truth_congr env leftValue rightValue words
          simp only [← choices]
          cases choice : Solidity.Yul.LocalBoolControl.truth leftValue with
          | false =>
            simp only [Bool.false_eq_true,if_false]
            exact Solidity.Yul.LocalBoolControlRepresentation.control env ctx no noProof fuel leftState rightState states
          | true =>
            simp only [if_true]
            exact Solidity.Yul.LocalBoolControlRepresentation.control env ctx yes yesProof fuel leftState rightState states

end Solidity.Yul.LocalU8Representation
