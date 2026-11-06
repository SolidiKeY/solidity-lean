import Solidity.Calculus.DecisionResidueReasons

/-! # Certified lazy extension of the fresh-struct fallback
Preserve the producer answer exactly on success, including its state function.
Only its absent-answer branch searches the checked reversed-field source family.
-/
namespace Solidity.Decide

/-- The existing producer is authoritative whenever it returns an answer. -/
def structAnswerWithReversed {C : Contract} {Γ : Ctx} (φ : Fml C Γ) :
    Option (MemoryWitness.Answer φ) :=
  (MemoryWitness.structAnswer φ).orElse
    (fun _ => (ResidueReason.reversedFreshField? φ).map (fun w => w.answer))

/-- Exact preservation includes counterstate transformers, not just verdict tags. -/
theorem structAnswerWithReversed_preserves {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    {a : MemoryWitness.Answer φ} (h : MemoryWitness.structAnswer φ = some a) :
    structAnswerWithReversed φ = some a := by
  unfold structAnswerWithReversed
  rw [h]
  rfl

theorem structAnswerWithReversed_original {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (h : (MemoryWitness.structAnswer φ).isSome = true) :
    (structAnswerWithReversed φ).isSome = true := by
  cases he : MemoryWitness.structAnswer φ with
  | none => rw [he] at h; cases h
  | some a => rw [structAnswerWithReversed_preserves he]; rfl

theorem structAnswerWithReversed_reversed {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (h : φ.freshStructReversedPrimitiveEquation = true) :
    (structAnswerWithReversed φ).isSome = true := by
  cases he : MemoryWitness.structAnswer φ with
  | some a => rw [structAnswerWithReversed_preserves he]; rfl
  | none =>
    unfold structAnswerWithReversed
    rw [he]
    change ((ResidueReason.reversedFreshField? φ).map (fun w => w.answer)).isSome = true
    simpa only [Option.isSome_map] using h

/-- On a producer miss, the new component retains its exact typed counterstate. -/
theorem structAnswerWithReversed_fallback {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (h : MemoryWitness.structAnswer φ = none) (w : ResidueReason.ReversedFreshField φ)
    (hw : ResidueReason.reversedFreshField? φ = some w) :
    structAnswerWithReversed φ = some w.answer := by
  unfold structAnswerWithReversed
  rw [h]
  change (ResidueReason.reversedFreshField? φ).map (fun v => v.answer) = some w.answer
  rw [hw]
  rfl

end Solidity.Decide
