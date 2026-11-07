import Solidity.Calculus.DecisionMemoryExtension
import Solidity.Calculus.DecisionCompoundCertificate

/-! # Lazy compound-field certificate composition
Original producer and reversed-field answers stay authoritative, including
all returned state functions. Only their miss consults the exact closed
compound-field source certificate.
-/
namespace Solidity.Decide

/-- Preserve all existing struct answers before consulting the compound source. -/
def structAnswerWithCompound {C : Contract} (φ : Fml C []) :
    Option (MemoryWitness.Answer φ) :=
  (structAnswerWithReversed φ).orElse
    (fun _ => (ResidueReason.nonliteralUIntFreshField? φ).map (fun w => w.answer))

/-- Exact preservation includes the old counterstate transformer. -/
theorem structAnswerWithCompound_preserves {C : Contract} {φ : Fml C []}
    {a : MemoryWitness.Answer φ} (h : structAnswerWithReversed φ = some a) :
    structAnswerWithCompound φ = some a := by
  unfold structAnswerWithCompound
  rw [h]
  rfl

/-- The old completeness premise remains sufficient. -/
theorem structAnswerWithCompound_original {C : Contract} {φ : Fml C []}
    (h : (structAnswerWithReversed φ).isSome = true) :
    (structAnswerWithCompound φ).isSome = true := by
  cases he : structAnswerWithReversed φ with
  | none => rw [he] at h; cases h
  | some a => rw [structAnswerWithCompound_preserves he]; rfl

/-- Exact typed compound-source recognition produces an actual Answer. -/
theorem structAnswerWithCompound_source {C : Contract} {φ : Fml C []}
    (h : φ.freshStructNonliteralUIntEquation = true) :
    (structAnswerWithCompound φ).isSome = true := by
  cases he : structAnswerWithReversed φ with
  | some a => rw [structAnswerWithCompound_preserves he]; rfl
  | none =>
    unfold structAnswerWithCompound
    rw [he]
    change ((ResidueReason.nonliteralUIntFreshField? φ).map (fun w => w.answer)).isSome = true
    simpa only [Option.isSome_map] using h

end Solidity.Decide
