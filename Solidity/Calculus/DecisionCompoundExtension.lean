import Solidity.Calculus.DecisionMemoryExtension
import Solidity.Calculus.DecisionCompoundCertificate
import Solidity.Calculus.DecisionMappingStruct

/-! # Lazy compound-field certificate composition
Original producer and reversed-field answers stay authoritative, including
all returned state functions. Only their miss consults the exact closed
compound-field source certificate; only a miss of that consults the
vacuous void-type binder (`Calculus/DecisionMappingStruct.lean`).
-/
namespace Solidity.Decide

/-- Preserve all existing struct answers before consulting the compound source. -/
def structAnswerWithCompound {C : Contract} (φ : Fml C []) :
    Option (MemoryWitness.Answer φ) :=
  ((structAnswerWithReversed φ).orElse
    (fun _ => (ResidueReason.nonliteralUIntFreshField? φ).map (fun w => w.answer))).orElse
    (fun _ => MappingStruct.voidAnswer? φ)

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
    change (((ResidueReason.nonliteralUIntFreshField? φ).map (fun w => w.answer)).orElse
      (fun _ => MappingStruct.voidAnswer? φ)).isSome = true
    have hs : ((ResidueReason.nonliteralUIntFreshField? φ).map (fun w => w.answer)).isSome = true := by
      simpa only [Option.isSome_map] using h
    cases hc : (ResidueReason.nonliteralUIntFreshField? φ).map (fun w => w.answer) with
    | none => rw [hc] at hs; cases hs
    | some a => rfl

/-- A fresh binder of a type with no memory object is answered. -/
theorem structAnswerWithCompound_void {C : Contract} {φ : Fml C []}
    (h : φ.freshVoidBinder = true) : (structAnswerWithCompound φ).isSome = true := by
  unfold structAnswerWithCompound
  cases hc : (structAnswerWithReversed φ).orElse
      (fun _ => (ResidueReason.nonliteralUIntFreshField? φ).map (fun w => w.answer)) with
  | some a => rfl
  | none => exact MappingStruct.voidAnswer_isSome h

end Solidity.Decide
