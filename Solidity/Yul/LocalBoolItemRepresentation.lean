import Solidity.Yul.LocalBoolControlRepresentation
import Solidity.Yul.LocalBoolItems

/-! Exact-word relations for existing context-growing Boolean executions.
Halted results retain the same reached intrinsic context and exact halt tag.
These relations do not equate clean projections or establish admission. -/
namespace Solidity.Yul.LocalBoolItemRepresentation
open Solidity.Yul.LocalBoolRepresentation

inductive Initialization (env : Solidity.Source.Env) (types : Solidity.Source.RCtx) :
    LocalBoolInitialization.Result env types → LocalBoolInitialization.Result env types → Prop where
  | normal {one two : LocalState env (.bool :: types)} :
      State one two → Initialization env types (.normal one) (.normal two)
  | halted {one two : LocalState env types} (halt : Solidity.Source.Halt) :
      State one two → Initialization env types (.halted halt one) (.halted halt two)

inductive Items (env : Solidity.Source.Env) (out : Solidity.Source.RCtx) :
    LocalBoolItems.Result env out → LocalBoolItems.Result env out → Prop where
  | normal {one two : LocalState env out} :
      State one two → Items env out (.normal one) (.normal two)
  | halted {reached : Solidity.Source.RCtx} {one two : LocalState env reached}
      (halt : Solidity.Source.Halt) :
      State one two → Items env out (.halted halt one) (.halted halt two)

theorem finish : ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx)
 (one two : Solidity.Source.R (Solidity.Yul.LocalValue env .bool) × Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolRepresentation.Run one two →
 Solidity.Yul.LocalBoolItemRepresentation.Initialization env types
 (Solidity.Yul.LocalBoolInitialization.finish one)
 (Solidity.Yul.LocalBoolInitialization.finish two) := by

  intro env types one two given
  rcases one with ⟨leftResult,leftState⟩
  rcases two with ⟨rightResult,rightState⟩
  rcases given with ⟨outcomes,states⟩
  rcases Solidity.Yul.LocalBoolRepresentation.outcome_cases env leftResult rightResult outcomes with
    ⟨halt,leftTag,rightTag⟩ | ⟨leftValue,rightValue,leftTag,rightTag,words⟩
  · simp only [Solidity.Yul.LocalBoolInitialization.finish,leftTag,rightTag]
    exact .halted halt states
  · simp only [Solidity.Yul.LocalBoolInitialization.finish,leftTag,rightTag]
    exact .normal ⟨.cons (.boolean words) states.1,states.2⟩

theorem initialization : ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx)
 (expr : Solidity.Source.RExpr env types .bool)
 (proof : Solidity.Yul.LocalBoolControl.Supported env types expr)
 (fuel : Nat) (one two : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolRepresentation.State one two →
 Solidity.Yul.LocalBoolItemRepresentation.Initialization env types
 (Solidity.Yul.LocalBoolInitialization.run proof fuel one)
 (Solidity.Yul.LocalBoolInitialization.run proof fuel two) := by

  intro env types expr proof fuel one two given
  cases fuel with
  | zero => exact .halted .timeout given
  | succ fuel =>
    exact Solidity.Yul.LocalBoolItemRepresentation.finish env types _ _
      (Solidity.Yul.LocalBoolControlRepresentation.control env types expr proof fuel one two given)

theorem items : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (body : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalBoolItems.Supported env returns modifier control body)
 (fuel : Nat) (one two : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolRepresentation.State one two →
 Solidity.Yul.LocalBoolItemRepresentation.Items env out
 (Solidity.Yul.LocalBoolItems.run proof fuel one)
 (Solidity.Yul.LocalBoolItems.run proof fuel two) := by

  intro env returns modifier control types out body proof
  induction proof with
  | nil =>
    intro fuel one two given
    cases fuel with
    | zero => exact .halted .timeout given
    | succ fuel => exact .normal given
  | expression child tail ih =>
    intro fuel one two given
    cases fuel with
    | zero => exact .halted .timeout given
    | succ fuel =>
      cases fuel with
      | zero => exact .halted .timeout given
      | succ fuel =>
        have compared := Solidity.Yul.LocalBoolControlRepresentation.control env _ _ child fuel one two given
        cases leftActual : Solidity.Yul.LocalBoolControl.eval child fuel one with
        | mk leftResult leftState =>
          cases rightActual : Solidity.Yul.LocalBoolControl.eval child fuel two with
          | mk rightResult rightState =>
            rw [leftActual,rightActual] at compared
            rcases compared with ⟨outcomes,states⟩
            rcases Solidity.Yul.LocalBoolRepresentation.outcome_cases env leftResult rightResult outcomes with
              ⟨halt,leftTag,rightTag⟩ | ⟨leftValue,rightValue,leftTag,rightTag,words⟩
            · conv => lhs; rw [Solidity.Yul.LocalBoolItems.run]
              conv => rhs; rw [Solidity.Yul.LocalBoolItems.run]
              simp only [Solidity.Yul.LocalExprStatement.discard_step,leftActual,rightActual,leftTag,rightTag]
              exact .halted halt states
            · conv => lhs; rw [Solidity.Yul.LocalBoolItems.run]
              conv => rhs; rw [Solidity.Yul.LocalBoolItems.run]
              simp only [Solidity.Yul.LocalExprStatement.discard_step,leftActual,rightActual,leftTag,rightTag]
              exact ih (fuel+1) leftState rightState states
  | declaration child tail ih =>
    intro fuel one two given
    cases fuel with
    | zero => exact .halted .timeout given
    | succ fuel =>
      have compared := Solidity.Yul.LocalBoolItemRepresentation.initialization env _ _ child fuel one two given
      conv => lhs; rw [Solidity.Yul.LocalBoolItems.run]
      conv => rhs; rw [Solidity.Yul.LocalBoolItems.run]
      dsimp only []
      generalize leftActual : Solidity.Yul.LocalBoolInitialization.run child fuel one = leftResult at compared ⊢
      generalize rightActual : Solidity.Yul.LocalBoolInitialization.run child fuel two = rightResult at compared ⊢
      cases compared with
      | normal states => exact ih fuel _ _ states
      | halted halt states => exact .halted halt states

end Solidity.Yul.LocalBoolItemRepresentation
