import Solidity.Calculus.DecisionNumericTraversal
import Solidity.Examples.DecisionNumericLogic

/-! # Actual numeric logical source traversal controls
Source weight is sufficient, not a minimal-fuel test or verdict classifier.
-/
namespace Solidity.Examples.DecisionNumericTraversal
open Solidity.Decide
open Solidity.Examples.DecisionCoefficientBoundary (Bank)
open Solidity.Examples.DecisionNumericLogic
set_option Elab.async false

def scope : SymS Bank [.val .uint] := (SymS.init (C := Bank)).pushQ .uint

/-- Nontrivial public-source traversal with exact original source terms. -/
theorem positive_source_certificate : ∃ ψ : LFml Bank,
    (sourceReduction? positive).map (·.leaf) = some (.all 0 .uint ψ) ∧
    positiveBody.toLS true scope = some ψ ∧ positiveBody.toLS false scope = some ψ :=
  qfUIntPrefix_sourceReduction _ positive_grammar (by decide +kernel)

theorem negative_source_certificate : ∃ ψ : LFml Bank,
    (sourceReduction? negative).map (·.leaf) = some (.all 0 .uint ψ) ∧
    negativeBody.toLS true scope = some ψ ∧ negativeBody.toLS false scope = some ψ :=
  qfUIntPrefix_sourceReduction _ negative_grammar (by decide +kernel)

theorem source_certificate_has_actual_leaf :
    (sourceReduction? positive).map (·.leaf) = some (.all 0 .uint positiveLower) := by
  obtain ⟨ψ, hr, hp, hn⟩ := positive_source_certificate
  have hψ : ψ = positiveLower := Option.some.inj (hp.symm.trans positive_translation)
  exact hψ ▸ hr

/-- The source-derived weight produces a real checked certificate at that fuel. -/
theorem source_weight_certificate : ∃ r : ExactAt scope positiveBody,
    ExactAt.ofFormula? positiveBody.uintQFWeight scope positiveBody = some r := by
  obtain ⟨r, ψ, hr, hl, hp, hn⟩ := qfUIntLinear_exact_source positiveBody.uintQFWeight
    positive_grammar (Nat.le_refl _)
  exact ⟨r, hr⟩

/-- A smaller traversal fuel genuinely refuses the logical nesting. -/
theorem too_small_fuel : ExactAt.ofFormula? 3 scope positiveBody = none := by rfl

/-- The sufficient source weight is not a necessary or minimal traversal budget. -/
theorem smaller_than_weight_succeeds :
    (ExactAt.ofFormula? 4 scope positiveBody).isSome = true ∧ 4 < positiveBody.uintQFWeight := by
  decide +kernel

theorem zero_fuel_refuses : ExactAt.ofFormula? 0 scope negativeBody = none := by rfl

/-- Proved/refuted semantics and exact source verdict certificates remain intact. -/
theorem positive_verdict_retained : decideGoal positive = .proved := positive_verdict

theorem negative_verdict_retained : ∃ σ : State Bank [], decideGoal negative = .refuted σ ∧
    ¬ Fml.holdsH σ negative := negative_verdict

end Solidity.Examples.DecisionNumericTraversal
