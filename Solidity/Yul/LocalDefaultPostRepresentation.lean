import Solidity.Yul.LocalDefaultControlRepresentation
import Solidity.Yul.LocalDefaultNoGuard

/-! Exact-word congruence for existing default-scope guarded and omitted-guard iterations.
No admission or clean projection equivalence is asserted. -/
namespace Solidity.Yul.LocalDefaultPostRepresentation

theorem postIter : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (condition post : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (step : Solidity.Yul.LocalBoolControl.Supported env types post)
 (body : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (proof : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ body)
 (fuel : Nat) (one two : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolRepresentation.State one two →
 Solidity.Yul.LocalBoolItemRepresentation.Items env types
 (Solidity.Yul.LocalDefaultPostIter.run test step proof fuel one)
 (Solidity.Yul.LocalDefaultPostIter.run test step proof fuel two) := by

  intro env returns modifier u types out condition post test step body proof fuel
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
        · conv => lhs; rw [Solidity.Yul.LocalDefaultPostIter.run]
          conv => rhs; rw [Solidity.Yul.LocalDefaultPostIter.run]
          simp only [leftActual,rightActual,leftTag,rightTag]
          exact .halted halt states
        · conv => lhs; rw [Solidity.Yul.LocalDefaultPostIter.run]
          conv => rhs; rw [Solidity.Yul.LocalDefaultPostIter.run]
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
            | halted halt states => exact .halted halt states
            | @normal bodyLeft bodyRight states =>
              have posts := Solidity.Yul.LocalBoolControlRepresentation.control
                env types post step fuel bodyLeft bodyRight states
              cases leftPost : Solidity.Yul.LocalBoolControl.eval step fuel bodyLeft with
              | mk postLeft postLeftState =>
                cases rightPost : Solidity.Yul.LocalBoolControl.eval step fuel bodyRight with
                | mk postRight postRightState =>
                  rw [leftPost,rightPost] at posts
                  rcases posts with ⟨postOutcomes,postStates⟩
                  rcases Solidity.Yul.LocalBoolRepresentation.outcome_cases env postLeft postRight postOutcomes with
                    ⟨halt,leftHalt,rightHalt⟩ | ⟨leftValue,rightValue,leftTag,rightTag,_words⟩
                  · simp only [leftPost,rightPost,leftHalt,rightHalt]
                    exact .halted halt postStates
                  · simp only [leftPost,rightPost,leftTag,rightTag]
                    exact ih postLeftState postRightState postStates


theorem noGuard : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (post : Solidity.Source.RExpr env types .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported env types post)
 (body : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (proof : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ body)
 (fuel : Nat) (one two : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolRepresentation.State one two →
 Solidity.Yul.LocalBoolItemRepresentation.Items env types
 (Solidity.Yul.LocalDefaultNoGuard.run step proof fuel one)
 (Solidity.Yul.LocalDefaultNoGuard.run step proof fuel two) := by

  intro env returns modifier u types out post step body proof fuel one two given
  exact Solidity.Yul.LocalDefaultPostRepresentation.postIter
    env returns modifier u types out (.bool true) post (.base (.literal true)) step
    body proof fuel one two given

theorem noGuardNoPost : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (body : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (proof : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ body)
 (fuel : Nat) (one two : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolRepresentation.State one two →
 Solidity.Yul.LocalBoolItemRepresentation.Items env types
 (Solidity.Yul.LocalDefaultNoGuard.runNoPost proof fuel one)
 (Solidity.Yul.LocalDefaultNoGuard.runNoPost proof fuel two) := by

  intro env returns modifier u types out body proof fuel one two given
  exact Solidity.Yul.LocalDefaultControlRepresentation.whileLoop
    env returns modifier u types out (.bool true) (.base (.literal true))
    body proof fuel one two given

end Solidity.Yul.LocalDefaultPostRepresentation
