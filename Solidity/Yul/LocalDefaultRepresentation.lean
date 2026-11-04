import Solidity.Yul.LocalBoolScopeRepresentation
import Solidity.Yul.LocalDefaultUnchecked

/-! Exact-word congruence for existing heterogeneous default and unchecked scopes.
Proof-only, with no clean projection or admission equivalence. -/
namespace Solidity.Yul.LocalDefaultRepresentation

theorem items : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (body : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control body)
 (fuel : Nat) (one two : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolRepresentation.State one two →
 Solidity.Yul.LocalBoolItemRepresentation.Items env out
 (Solidity.Yul.LocalDefaultItems.run proof fuel one)
 (Solidity.Yul.LocalDefaultItems.run proof fuel two) := by

  intro env returns modifier control types out body proof
  induction proof with
  | body child =>
    exact Solidity.Yul.LocalBoolItemRepresentation.items env returns modifier control _ _ _ child
  | declaration value tail ih =>
    intro fuel one two given
    cases fuel with
    | zero => exact .halted .timeout given
    | succ fuel =>
      cases fuel with
      | zero => exact .halted .timeout given
      | succ fuel =>
        cases fuel with
        | zero => exact .halted .timeout given
        | succ fuel =>
          exact ih (fuel+2) ((.clean value.value,one.1),one.2)
            ((.clean value.value,two.1),two.2) ⟨.cons (.same _) given.1,given.2⟩

theorem restore : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (body : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control body)
 (one two : Solidity.Yul.LocalState env out),
 Solidity.Yul.LocalBoolRepresentation.State one two →
 Solidity.Yul.LocalBoolRepresentation.State
 (Solidity.Yul.LocalDefaultItems.restore proof one)
 (Solidity.Yul.LocalDefaultItems.restore proof two) := by

  intro env returns modifier control types out body proof one two given
  exact ⟨Solidity.Yul.LocalBoolScopeRepresentation.cast env _ _
    (Solidity.Yul.LocalDefaultItems.context env returns modifier control types out body proof).2
    _ _ (Solidity.Yul.LocalBoolScopeRepresentation.drop env (out.length-types.length)
      out one.1 two.1 given.1),given.2⟩

theorem close : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (body : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control body)
 (one two : Solidity.Yul.LocalBoolItems.Result env out),
 Solidity.Yul.LocalBoolItemRepresentation.Items env out one two →
 Solidity.Yul.LocalBoolItemRepresentation.Items env types
 (Solidity.Yul.LocalDefaultItems.close proof one)
 (Solidity.Yul.LocalDefaultItems.close proof two) := by

  intro env returns modifier control types out body proof one two given
  cases given with
  | normal states =>
    exact .normal (Solidity.Yul.LocalDefaultRepresentation.restore
      env returns modifier control types out body proof _ _ states)
  | halted halt states => exact .halted halt states

theorem block : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (body : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control body)
 (fuel : Nat) (one two : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolRepresentation.State one two →
 Solidity.Yul.LocalBoolItemRepresentation.Items env types
 (Solidity.Yul.LocalDefaultItems.blockRun proof fuel one)
 (Solidity.Yul.LocalDefaultItems.blockRun proof fuel two) := by

  intro env returns modifier control types out body proof fuel one two given
  cases fuel with
  | zero => exact .halted .timeout given
  | succ fuel =>
    exact Solidity.Yul.LocalDefaultRepresentation.close
      env returns modifier control types out body proof _ _
      (Solidity.Yul.LocalDefaultRepresentation.items
        env returns modifier control types out body proof fuel one two given)

theorem unchecked : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l : Bool) (types middle out : Solidity.Source.RCtx)
 (inner : Solidity.Source.RItems env returns modifier ⟨l,true⟩ types middle)
 (inside : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨l,true⟩ inner)
 (rest : Solidity.Source.RItems env returns modifier ⟨l,false⟩ types out)
 (tail : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨l,false⟩ rest)
 (fuel : Nat) (one two : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolRepresentation.State one two →
 Solidity.Yul.LocalBoolItemRepresentation.Items env out
 (Solidity.Yul.LocalDefaultUnchecked.run inside tail fuel one)
 (Solidity.Yul.LocalDefaultUnchecked.run inside tail fuel two) := by

  intro env returns modifier l types middle out inner inside rest tail fuel one two given
  cases fuel with
  | zero => exact .halted .timeout given
  | succ fuel =>
    have compared := Solidity.Yul.LocalDefaultRepresentation.close
      env returns modifier ⟨l,true⟩ types middle inner inside _ _
      (Solidity.Yul.LocalDefaultRepresentation.items
        env returns modifier ⟨l,true⟩ types middle inner inside fuel one two given)
    simp only [Solidity.Yul.LocalDefaultUnchecked.run]
    generalize leftInner : Solidity.Yul.LocalDefaultItems.close inside
      (Solidity.Yul.LocalDefaultItems.run inside fuel one) = leftResult at compared ⊢
    generalize rightInner : Solidity.Yul.LocalDefaultItems.close inside
      (Solidity.Yul.LocalDefaultItems.run inside fuel two) = rightResult at compared ⊢
    cases compared with
    | @normal left right states =>
      exact Solidity.Yul.LocalDefaultRepresentation.items
        env returns modifier ⟨l,false⟩ types out rest tail fuel left right states
    | halted halt states => exact .halted halt states

theorem uncheckedBlock : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l : Bool) (types middle out : Solidity.Source.RCtx)
 (inner : Solidity.Source.RItems env returns modifier ⟨l,true⟩ types middle)
 (inside : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨l,true⟩ inner)
 (rest : Solidity.Source.RItems env returns modifier ⟨l,false⟩ types out)
 (tail : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨l,false⟩ rest)
 (fuel : Nat) (one two : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalBoolRepresentation.State one two →
 Solidity.Yul.LocalBoolItemRepresentation.Items env types
 (Solidity.Yul.LocalDefaultUnchecked.blockRun inside tail fuel one)
 (Solidity.Yul.LocalDefaultUnchecked.blockRun inside tail fuel two) := by

  intro env returns modifier l types middle out inner inside rest tail fuel one two given
  cases fuel with
  | zero => exact .halted .timeout given
  | succ fuel =>
    exact Solidity.Yul.LocalDefaultRepresentation.close
      env returns modifier ⟨l,false⟩ types out rest tail _ _
      (Solidity.Yul.LocalDefaultRepresentation.unchecked
        env returns modifier l types middle out inner inside rest tail fuel one two given)

end Solidity.Yul.LocalDefaultRepresentation
