import Solidity.Calculus.Decision

/-! # Coverage of the actual reversed-field memory route
Closed single fresh-struct equations only. The array-cut route and all frozen
declarations remain unchanged; coverage expands via the certified fallback.
-/
namespace Solidity.Decide.ResidueReason

theorem ReversedFreshField.prepared_body {C : Contract} {φ : Fml C []}
    (w : ReversedFreshField φ) : (mxNegativePrepare φ).body = φ := by
  rcases w with ⟨x, s, f, p, value, hf, hm, heq⟩
  subst φ
  rfl

theorem ReversedFreshField.hoisted {C : Contract} {φ : Fml C []}
    (w : ReversedFreshField φ) : ((mxNegativePrepare φ).body.hoist 1024) = φ := by
  rcases w with ⟨x, s, f, p, value, hf, hm, heq⟩
  subst φ
  rfl

theorem ReversedFreshField.cut_none {C : Contract} {φ : Fml C []}
    (w : ReversedFreshField φ) : ((mxNegativePrepare φ).body.hoist 1024).mxTop = none := by
  rcases w with ⟨x, s, f, p, value, hf, hm, heq⟩
  subst φ
  rfl

theorem ReversedFreshField.hasAllocAll {C : Contract} {φ : Fml C []}
    (w : ReversedFreshField φ) : φ.hasAllocAll = true := by
  rcases w with ⟨x, s, f, p, value, hf, hm, heq⟩
  subst φ
  rfl

/-- The recognized source actually reaches the certified fallback. -/
theorem ReversedFreshField.memCovered {C : Contract} {φ : Fml C []}
    (w : ReversedFreshField φ) : φ.memCovered = true := by
  have hgiven : φ.givenHeapLiteralReadReflexive = false := by
    rcases w with ⟨x, s, f, p, value, hf, hm, heq⟩
    subst φ
    rfl
  unfold Fml.memCovered
  rw [w.hasAllocAll, w.cut_none, hgiven, Bool.or_false]
  change (structAnswerWithReversed φ).isSome = true
  exact structAnswerWithReversed_reversed (reversedFreshField_complete w)

theorem ReversedFreshField.covered {C : Contract} {φ : Fml C []}
    (w : ReversedFreshField φ) : φ.Covered = true := by
  simp only [Fml.Covered, w.memCovered, Bool.or_true, Bool.true_or]

/-- This exact literal/field source class is admitted under every waiver setting. -/
theorem ReversedFreshField.target {C : Contract} {φ : Fml C []}
    (w : ReversedFreshField φ) (waivers : Waivers) : φ.inTarget waivers = true := by
  rcases w with ⟨x, s, f, p, value, hf, hm, heq⟩
  subst φ
  cases p <;> rfl

theorem ReversedFreshField.answered {C : Contract} {φ : Fml C []}
    (w : ReversedFreshField φ) : decideGoal φ ≠ .unknown :=
  decideGoal_complete w.covered w.hashFree

/-- The actual returned refutation is certified under the unchanged hash reading.
This does not identify its state with a separately constructed countermodel. -/
theorem ReversedFreshField.refuted {C : Contract} {φ : Fml C []}
    (w : ReversedFreshField φ) : ∃ σ : State C [], decideGoal φ = .refuted σ ∧ ¬ Fml.holdsH σ φ := by
  have hd : decideGoal φ ≠ .unknown := w.answered
  cases he : decideGoal φ with
  | proved =>
    exact False.elim (w.counterState_refutesH (State.init C)
      ((decideGoal_sound he) (w.counterState (State.init C))))
  | refuted σ => exact ⟨σ, rfl, decideGoal_refutes he⟩
  | unknown => exact False.elim (hd he)

end Solidity.Decide.ResidueReason
