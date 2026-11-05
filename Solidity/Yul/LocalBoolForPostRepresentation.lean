import Solidity.Yul.LocalBoolForRepresentation
import Solidity.Yul.LocalBoolPostRepresentation
import Solidity.Yul.LocalBoolForPost

/-! Exact-word congruence for existing Boolean-init guarded post for execution.
No admission or clean projection equivalence is asserted. -/
namespace Solidity.Yul.LocalBoolForPostRepresentation

theorem forLoop : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (init : Solidity.Source.RExpr env types .bool)
 (initializer : Solidity.Yul.LocalBoolControl.Supported env types init)
 (condition post : Solidity.Source.RExpr env (.bool :: types) .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env (.bool :: types) condition)
 (step : Solidity.Yul.LocalBoolControl.Supported env (.bool :: types) post)
 (body : Solidity.Source.RItems env returns modifier ⟨true,u⟩ (.bool :: types) out)
 (proof : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ body)
 (fuel : Nat) (one two : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolRepresentation.State one two →
 Solidity.Yul.LocalBoolItemRepresentation.Items env types
 (Solidity.Yul.LocalBoolForPost.run initializer test step proof fuel one)
 (Solidity.Yul.LocalBoolForPost.run initializer test step proof fuel two) := by

  intro env returns modifier u types out init initializer condition post test step body proof fuel one two given
  cases fuel with
  | zero => exact .halted .timeout given
  | succ fuel =>
    have initial := Solidity.Yul.LocalBoolItemRepresentation.initialization
      env types init initializer fuel one two given
    simp only [Solidity.Yul.LocalBoolForPost.run]
    generalize leftInit : Solidity.Yul.LocalBoolInitialization.run initializer fuel one = leftRun at initial ⊢
    generalize rightInit : Solidity.Yul.LocalBoolInitialization.run initializer fuel two = rightRun at initial ⊢
    cases initial with
    | @normal left right states =>
      exact Solidity.Yul.LocalBoolForRepresentation.close env types _ _
        (Solidity.Yul.LocalBoolPostRepresentation.postIter
          env returns modifier u (.bool :: types) out condition post test step body proof fuel left right states)
    | halted halt states => exact .halted halt states

end Solidity.Yul.LocalBoolForPostRepresentation
