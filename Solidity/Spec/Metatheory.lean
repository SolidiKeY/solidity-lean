import Solidity.Spec.Assertion

/-!
# What the SolSpec modalities mean relative to each other

Two sanity results about `Spec.vc`, kept out of `Assertion.lean` on
purpose: `Assertion.lean` is what the `sol_spec` tactic — and therefore
the VS Code extension — depends on, and it should carry only definitions
and their computation rules. The relating theorems belong to the
`SoliditySpec` target instead, where nothing but the documentation
rests on them.

* `totalVC_imp_partialVC`: proving a total specification proves the
  partial one. So `@custom:partial` is genuinely a weakening, and a
  contract cannot gain anything by dropping it.
* `not_totalVC_of_revertsVC`: on bodies with no ghost `assume`, a body
  that must revert satisfies no total specification. So
  `@custom:reverts_when` and a total `@custom:ensures` cannot both hold —
  a specification cannot quietly claim both.

The `assume`-free side condition on the second is real, not an artifact
of the proof: `@custom:assume False` discharges everything after it, so
both obligations become vacuous together. That is exactly why Dafny
treats `assume` as an unchecked escape hatch, and why
`docs/spec-language.md` says so out loud.
-/

namespace Solidity
namespace Spec

open Semantics

/-- Bodies that contain no ghost `assume`. -/
def NoAssume : List Ann -> Prop
  | [] => True
  | Ann.assume _ :: _ => False
  | Ann.assert _ :: rest => NoAssume rest
  | Ann.stmt _ :: rest => NoAssume rest

theorem totalVC_imp_partialVC (Q : State -> Prop) :
    ∀ (body : List Ann) (s : State),
      totalVC s body Q -> partialVC s body Q := by
  intro body
  induction body with
  | nil => intro s h; exact h
  | cons a rest ih =>
      intro s h
      cases a with
      | stmt st =>
          cases hr : Semantics.execStmt s st with
          | ok s' =>
              simp only [totalVC, vc, hr] at h
              simp only [partialVC, vc, hr]
              exact ih s' h
          | error e => exact absurd h (by simp [totalVC, vc, hr])
      | «assert» phi =>
          simp only [totalVC, vc] at h
          simp only [partialVC, vc]
          exact ⟨h.1, ih s h.2⟩
      | «assume» phi =>
          simp only [totalVC, vc] at h
          simp only [partialVC, vc]
          exact fun hphi => ih s (h hphi)

theorem not_totalVC_of_revertsVC (Q : State -> Prop) :
    ∀ (body : List Ann) (s : State),
      NoAssume body -> revertsVC s body -> ¬ totalVC s body Q := by
  intro body
  induction body with
  | nil => intro s _ hrev; exact absurd hrev (by simp [revertsVC])
  | cons a rest ih =>
      intro s hna hrev hall
      cases a with
      | stmt st =>
          cases hr : Semantics.execStmt s st with
          | ok s' =>
              simp only [revertsVC, hr] at hrev
              simp only [totalVC, vc, hr] at hall
              exact ih s' hna hrev hall
          | error e => exact absurd hall (by simp [totalVC, vc, hr])
      | «assert» phi =>
          simp only [revertsVC] at hrev
          simp only [totalVC, vc] at hall
          exact ih s hna hrev hall.2
      | «assume» phi => exact absurd hna (by simp [NoAssume])

end Spec
end Solidity
