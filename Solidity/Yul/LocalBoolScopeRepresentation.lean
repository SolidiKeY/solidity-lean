import Solidity.Yul.LocalBoolItemRepresentation
import Solidity.Yul.LocalBoolIf

/-! Exact-word congruence through existing scope restoration and conditionals.
No Source projection equivalence or admission is asserted. -/
namespace Solidity.Yul.LocalBoolScopeRepresentation

theorem drop : ∀ (env : Solidity.Source.Env) (count : Nat) (types : Solidity.Source.RCtx)
 (one two : Solidity.Yul.LocalValues env types),
 Solidity.Yul.LocalBoolRepresentation.Locals env one two →
 Solidity.Yul.LocalBoolRepresentation.Locals env
 (Solidity.Yul.LocalBoolItemScope.drop count one)
 (Solidity.Yul.LocalBoolItemScope.drop count two) := by

  intro env count
  induction count with
  | zero => intro types one two given; exact given
  | succ count ih =>
    intro types one two given
    cases types with
    | nil => cases one; cases two; exact .same _
    | cons ty types =>
      cases given with
      | same => exact .same _
      | cons head tail => exact ih _ _ _ tail

theorem cast : ∀ (env : Solidity.Source.Env) (before after : Solidity.Source.RCtx)
 (same : before = after) (one two : Solidity.Yul.LocalValues env before),
 Solidity.Yul.LocalBoolRepresentation.Locals env one two →
 Solidity.Yul.LocalBoolRepresentation.Locals env (same ▸ one) (same ▸ two) := by

  intro env before after same one two given
  cases same
  exact given

theorem restore : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (body : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalBoolItems.Supported env returns modifier control body)
 (one two : Solidity.Yul.LocalState env out),
 Solidity.Yul.LocalBoolRepresentation.State one two →
 Solidity.Yul.LocalBoolRepresentation.State
 (Solidity.Yul.LocalBoolItemScope.restore proof one)
 (Solidity.Yul.LocalBoolItemScope.restore proof two) := by

  intro env returns modifier control types out body proof one two given
  exact ⟨Solidity.Yul.LocalBoolScopeRepresentation.cast env _ _
    (Solidity.Yul.LocalBoolItemScope.suffix env returns modifier control types out body proof)
    _ _ (Solidity.Yul.LocalBoolScopeRepresentation.drop env (out.length-types.length)
      out one.1 two.1 given.1),given.2⟩

theorem close : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (body : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalBoolItems.Supported env returns modifier control body)
 (one two : Solidity.Yul.LocalBoolItems.Result env out),
 Solidity.Yul.LocalBoolItemRepresentation.Items env out one two →
 Solidity.Yul.LocalBoolItemRepresentation.Items env types
 (Solidity.Yul.LocalBoolItemScope.close proof one)
 (Solidity.Yul.LocalBoolItemScope.close proof two) := by

  intro env returns modifier control types out body proof one two given
  cases given with
  | normal states =>
    exact .normal (Solidity.Yul.LocalBoolScopeRepresentation.restore
      env returns modifier control types out body proof _ _ states)
  | halted halt states => exact .halted halt states

theorem scope : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (body : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalBoolItems.Supported env returns modifier control body)
 (fuel : Nat) (one two : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolRepresentation.State one two →
 Solidity.Yul.LocalBoolItemRepresentation.Items env types
 (Solidity.Yul.LocalBoolItemScope.run proof fuel one)
 (Solidity.Yul.LocalBoolItemScope.run proof fuel two) := by

  intro env returns modifier control types out body proof fuel one two given
  cases fuel with
  | zero => exact .halted .timeout given
  | succ fuel =>
    exact Solidity.Yul.LocalBoolScopeRepresentation.close
      env returns modifier control types out body proof _ _
      (Solidity.Yul.LocalBoolItemRepresentation.items
        env returns modifier control types out body proof fuel one two given)

theorem conditional : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (body : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalBoolItems.Supported env returns modifier control body)
 (condition : Solidity.Source.RExpr env types .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env types condition)
 (fuel : Nat) (one two : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolRepresentation.State one two →
 Solidity.Yul.LocalBoolItemRepresentation.Items env types
 (Solidity.Yul.LocalBoolIf.run test proof fuel one)
 (Solidity.Yul.LocalBoolIf.run test proof fuel two) := by

  intro env returns modifier control types out body proof condition test fuel one two given
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
        · simp only [Solidity.Yul.LocalBoolIf.run,leftActual,rightActual,leftTag,rightTag]
          exact .halted halt states
        · simp only [Solidity.Yul.LocalBoolIf.run,leftActual,rightActual,leftTag,rightTag]
          have choices := Solidity.Yul.LocalBoolRepresentation.truth_congr env leftValue rightValue words
          simp only [← choices]
          cases choice : Solidity.Yul.LocalBoolControl.truth leftValue with
          | false =>
            simp only [Bool.false_eq_true,if_false]
            exact .normal states
          | true =>
            simp only [if_true]
            exact Solidity.Yul.LocalBoolScopeRepresentation.scope
              env returns modifier control types out body proof fuel leftState rightState states

end Solidity.Yul.LocalBoolScopeRepresentation
