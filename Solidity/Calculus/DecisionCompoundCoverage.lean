import Solidity.Calculus.Decision
import Solidity.Calculus.DecisionUIntGrammar

/-! # Actual coverage and refutation of closed compound-field sources
Every route fact follows from the exact intrinsic source witness. The returned
refutation is certified under the unchanged hash reading; exact chosen-state
identity is a separate concrete control.
-/
namespace Solidity.Decide.ResidueReason

theorem NonliteralUIntFreshField.prepared_body {C : Contract} {φ : Fml C []}
    (w : NonliteralUIntFreshField φ) : (mxNegativePrepare φ).body = φ := by
  rcases w with ⟨x, s, f, hf, rhs, hl, hn, hm, heq⟩
  subst φ
  rfl

theorem NonliteralUIntFreshField.hoisted {C : Contract} {φ : Fml C []}
    (w : NonliteralUIntFreshField φ) : ((mxNegativePrepare φ).body.hoist 1024) = φ := by
  rcases w with ⟨x, s, f, hf, rhs, hl, hn, hm, heq⟩
  subst φ
  rfl

theorem NonliteralUIntFreshField.cut_none {C : Contract} {φ : Fml C []}
    (w : NonliteralUIntFreshField φ) : ((mxNegativePrepare φ).body.hoist 1024).mxTop = none := by
  rcases w with ⟨x, s, f, hf, rhs, hl, hn, hm, heq⟩
  subst φ
  rfl

theorem NonliteralUIntFreshField.hasAllocAll {C : Contract} {φ : Fml C []}
    (w : NonliteralUIntFreshField φ) : φ.hasAllocAll = true := by
  rcases w with ⟨x, s, f, hf, rhs, hl, hn, hm, heq⟩
  subst φ
  rfl

theorem NonliteralUIntFreshField.notGiven {C : Contract} {φ : Fml C []}
    (w : NonliteralUIntFreshField φ) : φ.givenHeapLiteralReadReflexive = false := by
  rcases w with ⟨x, s, f, hf, rhs, hl, hn, hm, heq⟩
  subst φ
  rfl

/-- The real preparation/cut path reaches the combined certified answer. -/
theorem NonliteralUIntFreshField.memCovered {C : Contract} {φ : Fml C []}
    (w : NonliteralUIntFreshField φ) : φ.memCovered = true := by
  unfold Fml.memCovered
  rw [w.hasAllocAll, w.cut_none, w.notGiven, Bool.or_false]
  simp only [Bool.not_true, Bool.false_and, Bool.or_false, Bool.true_and]
  rw [Bool.or_eq_true]
  apply Or.inl
  change (structAnswerWithCompound φ).isSome = true
  exact structAnswerWithCompound_source (nonliteralUIntFreshField_complete w)

theorem NonliteralUIntFreshField.covered {C : Contract} {φ : Fml C []}
    (w : NonliteralUIntFreshField φ) : φ.Covered = true := by
  simp only [Fml.Covered, w.memCovered, Bool.or_true, Bool.true_or]

/-- Source admission holds under every existing waiver setting. -/
theorem NonliteralUIntFreshField.target {C : Contract} {φ : Fml C []}
    (w : NonliteralUIntFreshField φ) (waivers : Waivers) : φ.inTarget waivers = true := by
  rcases w with ⟨x, s, f, hf, rhs, hl, hn, hm, heq⟩
  subst φ
  change (rhs.inTarget waivers false && keysAgree rhs.mapKeys) && true = true
  rw [uintLinear_admitted hl waivers, uintLinear_mapKeys hl]
  rfl

/-- The actual global route answers without supplied coverage or verdict hypotheses. -/
theorem NonliteralUIntFreshField.answered {C : Contract} {φ : Fml C []}
    (w : NonliteralUIntFreshField φ) : decideGoal φ ≠ .unknown :=
  decideGoal_complete w.covered w.hashFree

/-- The actual returned state refutes the existing hash reading. This existential
claim does not identify it with a separately constructed countermodel. -/
theorem NonliteralUIntFreshField.refuted {C : Contract} {φ : Fml C []}
    (w : NonliteralUIntFreshField φ) :
    ∃ σ : State C [], decideGoal φ = .refuted σ ∧ ¬ Fml.holdsH σ φ := by
  have hd : decideGoal φ ≠ .unknown := w.answered
  cases he : decideGoal φ with
  | proved =>
    exact False.elim (w.counterState_refutesH (State.init C)
      ((decideGoal_sound he) (w.counterState (State.init C))))
  | refuted σ => exact ⟨σ, rfl, decideGoal_refutes he⟩
  | unknown => exact False.elim (hd he)

end Solidity.Decide.ResidueReason
