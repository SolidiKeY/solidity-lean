import Solidity.Yul.LocalBoolWhileRepresentation
import Solidity.Yul.LocalBoolFor

/-! Exact-word congruence for existing Boolean-initialized for execution, no post.
Proof-only; no Source readback or admission equivalence is asserted. -/
namespace Solidity.Yul.LocalBoolForRepresentation

theorem close : ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx)
 (one two : Solidity.Yul.LocalBoolItems.Result env (.bool :: types)),
 Solidity.Yul.LocalBoolItemRepresentation.Items env (.bool :: types) one two →
 Solidity.Yul.LocalBoolItemRepresentation.Items env types
 (Solidity.Yul.LocalBoolFor.close one) (Solidity.Yul.LocalBoolFor.close two) := by

  intro env types one two given
  cases given with
  | @normal left right states =>
    exact .normal ⟨Solidity.Yul.LocalBoolScopeRepresentation.drop
      env 1 (.bool :: types) left.1 right.1 states.1,states.2⟩
  | halted halt states => exact .halted halt states

theorem forLoop : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (init : Solidity.Source.RExpr env types .bool)
 (initializer : Solidity.Yul.LocalBoolControl.Supported env types init)
 (condition : Solidity.Source.RExpr env (.bool :: types) .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env (.bool :: types) condition)
 (body : Solidity.Source.RItems env returns modifier ⟨true,u⟩ (.bool :: types) out)
 (proof : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ body)
 (fuel : Nat) (one two : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolRepresentation.State one two →
 Solidity.Yul.LocalBoolItemRepresentation.Items env types
 (Solidity.Yul.LocalBoolFor.run initializer test proof fuel one)
 (Solidity.Yul.LocalBoolFor.run initializer test proof fuel two) := by

  intro env returns modifier u types out init initializer condition test body proof fuel one two given
  cases fuel with
  | zero => exact .halted .timeout given
  | succ fuel =>
    have initial := Solidity.Yul.LocalBoolItemRepresentation.initialization
      env types init initializer fuel one two given
    simp only [Solidity.Yul.LocalBoolFor.run]
    generalize leftInit : Solidity.Yul.LocalBoolInitialization.run initializer fuel one = leftRun at initial ⊢
    generalize rightInit : Solidity.Yul.LocalBoolInitialization.run initializer fuel two = rightRun at initial ⊢
    cases initial with
    | @normal left right states =>
      exact Solidity.Yul.LocalBoolForRepresentation.close env types _ _
        (Solidity.Yul.LocalBoolWhileRepresentation.whileLoop
          env returns modifier u (.bool :: types) out condition test body proof fuel left right states)
    | halted halt states => exact .halted halt states

end Solidity.Yul.LocalBoolForRepresentation
