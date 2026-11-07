import Solidity.Calculus.DecisionNumericNormalization
import Solidity.Calculus.DecisionUIntFormulaRecognizer

/-! # Decidable source-work residue for arbitrary primitive prefixes
The predicate inspects the intrinsic prefix/body grammar and source visits only.
It identifies a normalizer-stage gap, not an exhaustive public unknown class.
-/
namespace Solidity.Decide.ResidueReason

private def prefixBaseDecidable {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (back : φ.NumericPrimitivePrefix → φ.QFUIntLinear) : Decidable φ.NumericPrimitivePrefix :=
  match φ.qfUIntLinearDecidable with
  | .isTrue grammar => .isTrue (.body grammar)
  | .isFalse noGrammar => .isFalse (fun h => noGrammar (back h))

/-- Constructive recognition of the original source prefix and body constructors. -/
def _root_.Solidity.Fml.numericPrimitivePrefixDecidable {C : Contract} {Γ : Ctx}
    (φ : Fml C Γ) : Decidable φ.NumericPrimitivePrefix := by
  apply @Fml.casesOn C (fun Γ φ => Decidable φ.NumericPrimitivePrefix) Γ φ
  case all =>
    intro Γ name p body
    exact match body.numericPrimitivePrefixDecidable with
    | .isTrue grammar => .isTrue (.all name p grammar)
    | .isFalse noGrammar => .isFalse (fun h => by
        cases h with
        | body grammar => cases grammar
        | all _ _ grammar => exact noGrammar grammar)
  all_goals
    intros
    exact prefixBaseDecidable (fun h => by cases h with | body grammar => exact grammar)
termination_by structural φ

instance {C : Contract} {Γ : Ctx} (φ : Fml C Γ) :
    Decidable φ.NumericPrimitivePrefix := φ.numericPrimitivePrefixDecidable

/-- Separately named syntactic gap: real primitive prefixes and numeric bodies
whose source visits exceed the unchanged normalizer budget. -/
def _root_.Solidity.Fml.PrimitivePrefixNormalizationResidue {C : Contract} {Γ : Ctx}
    (φ : Fml C Γ) : Prop := φ.NumericPrimitivePrefix ∧ 2048 < φ.normalizationWork

instance {C : Contract} {Γ : Ctx} (φ : Fml C Γ) :
    Decidable φ.PrimitivePrefixNormalizationResidue :=
  inferInstanceAs (Decidable (φ.NumericPrimitivePrefix ∧ 2048 < φ.normalizationWork))

/-- One-line reason, independent of coverage, target and every verdict route. -/
def primitivePrefixNormalizationReason : String :=
  "The actual primitive prefixes and numeric body require more than 2048 normalizer visits."

/-- Interpret the actual source-syntax and work certificate against the real
normalizer, without assuming coverage failure or public unknown. -/
theorem primitivePrefixNormalizationResidue_normalizer_none
    {C : Contract} {Γ : Ctx} {φ : Fml C Γ} (h : φ.PrimitivePrefixNormalizationResidue) :
    ProgramNormalization.ofFormula? 2048 φ = none := by
  cases he : ProgramNormalization.ofFormula? 2048 φ with
  | none => rfl
  | some d =>
    have success : (ProgramNormalization.ofFormula? 2048 φ).isSome = true := by
      rw [he]
      rfl
    have work : φ.normalizationWork ≤ 2048 :=
      (numericPrimitivePrefix_normalization_iff_work h.1 2048).mp success
    have over : 2048 < φ.normalizationWork := h.2
    omega

end Solidity.Decide.ResidueReason
