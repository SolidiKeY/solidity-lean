import Solidity.Calculus.DecisionNumericNormalization
import Solidity.Calculus.DecisionUIntFormulaRecognizer

/-! # A source-syntax reason for exhausting the public normalizer
The class retains two actual uint binders, numeric body grammar and structural
work. It classifies a normalization-stage resource gap, not public unknown or
coverage. No budget, target predicate or exclusion is changed.
-/
namespace Solidity.Decide.ResidueReason

/-- Two uint binders whose numeric body requires more than the unchanged public
normalizer budget. The constructor fixes the complete intrinsic source shape. -/
inductive TwoUIntPrefixOverNormalizationBudget {C : Contract} {Γ : Ctx} :
    Fml C Γ → Type where
  | mk (x y : Var) (body : Fml C (.val .uint :: .val .uint :: Γ))
      (grammar : body.QFUIntLinear) (overBudget : 2048 < body.normalizationWork + 2) :
      TwoUIntPrefixOverNormalizationBudget (.all x .uint (.all y .uint body))

/-- Recognize only the explicit binder/body syntax and its formula-visit count. -/
def twoUIntPrefixOverNormalizationBudget? {C : Contract} {Γ : Ctx} (φ : Fml C Γ) :
    Option (TwoUIntPrefixOverNormalizationBudget φ) :=
  match φ with
  | .all x .uint (.all y .uint body) =>
    if hg : body.QFUIntLinear then
      if ho : 2048 < body.normalizationWork + 2 then
        some (.mk x y body hg ho)
      else none
    else none
  | _ => none

/-- Independently computable source-reason tag; it never evaluates a verdict. -/
def _root_.Solidity.Fml.twoUIntPrefixOverNormalizationBudget {C : Contract} {Γ : Ctx}
    (φ : Fml C Γ) : Bool := (twoUIntPrefixOverNormalizationBudget? φ).isSome

/-- One-line reason attached to this exact source family. -/
def twoUIntPrefixOverNormalizationBudgetReason : String :=
  "Both uint binders and the numeric body need more than 2048 normalizer visits."

/-- Every member exhausts the existing normalizer at its unchanged public
budget. This says nothing about later fallback routes or public verdicts. -/
theorem TwoUIntPrefixOverNormalizationBudget.normalizer_none
    {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : TwoUIntPrefixOverNormalizationBudget φ) :
    ProgramNormalization.ofFormula? 2048 φ = none := by
  cases w with
  | mk x y body grammar overBudget =>
    cases he : ProgramNormalization.ofFormula? 2048 (.all x .uint (.all y .uint body)) with
    | none => rfl
    | some d =>
      have hs : (ProgramNormalization.ofFormula? 2048
          (.all x .uint (.all y .uint body))).isSome = true := by
        rw [he]
        rfl
      have hw : body.normalizationWork + 2 ≤ 2048 :=
        (qfUIntTwoPrefix_normalization_iff_work x y grammar 2048).mp hs
      omega

#print axioms TwoUIntPrefixOverNormalizationBudget.normalizer_none

/-- A decidable source-syntax class, independent of every decision route. -/
def _root_.Solidity.Fml.NormalizationBudgetResidue {C : Contract} {Γ : Ctx}
    (φ : Fml C Γ) : Prop := φ.twoUIntPrefixOverNormalizationBudget = true

instance {C : Contract} {Γ : Ctx} (φ : Fml C Γ) :
    Decidable φ.NormalizationBudgetResidue :=
  inferInstanceAs (Decidable (φ.twoUIntPrefixOverNormalizationBudget = true))

/-- Interpret the recognizer's actual typed witness using the checked resource
argument. No unproved coverage or public-unknown premise is used. -/
theorem normalizationBudgetResidue_normalizer_none
    {C : Contract} {Γ : Ctx} {φ : Fml C Γ} (h : φ.NormalizationBudgetResidue) :
    ProgramNormalization.ofFormula? 2048 φ = none := by
  exact ((twoUIntPrefixOverNormalizationBudget? φ).get h).normalizer_none

#print axioms normalizationBudgetResidue_normalizer_none

end Solidity.Decide.ResidueReason
