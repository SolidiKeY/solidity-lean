import Solidity.Calculus.DecisionNumericCoverage
import Solidity.Examples.DecisionNumericBounds
import Solidity.Examples.DecisionGapCensus

/-!
# Source coverage bridge controls
Generic theorem applications, strict and optional equality, positive/refuted
certificates, and preserved countercontrols outside the sufficient source class.
-/
namespace Solidity.Examples.DecisionNumericCoverage
open Solidity.Decide
open Solidity.Examples.DecisionCoefficientBoundary (Bank)
open Solidity.Examples.DecisionUIntBridge
open Solidity.Examples.DecisionNumericFormula (literalLeaf literalTerm)
open Solidity.Examples.DecisionNumericBounds
set_option Elab.async false

theorem near_limit_generic_coverage : nearLimit.Covered = true :=
  uintPrefix_Covered (.user "x") (symbolicChain_grammar 17) (symbolicChain_grammar 17)
    (by decide +kernel)

theorem near_limit_generic_decided : decideGoal nearLimit ≠ .unknown :=
  uintPrefix_decided (.user "x") (symbolicChain_grammar 17) (symbolicChain_grammar 17)
    (by decide +kernel)

theorem strict_unused_binder_generic_coverage : literalLeaf.Covered = true :=
  uintPrefix_Covered (.user "unused") (.lit _) (.lit _) (by decide +kernel)

theorem strict_positive_certificate : decideGoal literalLeaf = .proved ∧ Fml.ValidH literalLeaf :=
  ⟨Solidity.Examples.DecisionNumericFormula.literal_proved,
    Solidity.Examples.DecisionNumericFormula.literal_validH⟩

theorem partial_generic_coverage : partialLeaf.Covered = true :=
  uintPrefix_Covered (.user "x") decrement1_grammar decrement2_grammar (by decide +kernel)

theorem partial_generic_certificate :
    (decideGoal partialLeaf = .proved ∧ Fml.ValidH partialLeaf) ∨
      ∃ σ : State Bank [], decideGoal partialLeaf = .refuted σ ∧ ¬ Fml.holdsH σ partialLeaf :=
  uintPrefix_certified (.user "x") decrement1_grammar decrement2_grammar (by decide +kernel)

theorem partial_actual_refutation : ∃ σ : State Bank [],
    decideGoal partialLeaf = .refuted σ ∧ ¬ Fml.holdsH σ partialLeaf := partialLeaf_refuted

theorem partial_definedness_control : holds zeroState partialBody ∧ ¬ holds oneState partialBody :=
  ⟨both_halting_equal, one_halting_unequal⟩

theorem both_failed_generic_coverage : bothFailed.Covered = true :=
  uintPrefix_Covered (.user "unused") fails_grammar fails_grammar (by decide +kernel)

theorem false_generic_coverage : oneFailed.Covered = true :=
  uintPrefix_Covered (.user "unused") fails_grammar (.lit _) (by decide +kernel)

theorem false_actual_refutation : ∃ σ : State Bank [],
    decideGoal oneFailed = .refuted σ ∧ ¬ Fml.holdsH σ oneFailed := oneFailed_refuted

/-- Exceeding the sufficient source criterion is not a refusal or Residue classifier. -/
theorem larger_uncovered_still_proved : overRawBound.Covered = false ∧
    overRawBound.hashCovered = false ∧ decideGoal overRawBound = .proved :=
  ⟨overRawBound_notCovered, overRawBound_notHashCovered, overRawBound_proved⟩

theorem larger_source_folds_to_covered :
    71 < (literalChain 20).size + (literalChain 20).size ∧ foldedLarge.Covered = true :=
  ⟨foldedLarge_exceeds_criterion, foldedLarge_covered⟩

/-- An independently known target gap remains unknown, without any new exclusion. -/
theorem preserved_memory_unknown : Solidity.Examples.Decision.memParamSame.inTarget {} = true ∧
    decideGoal Solidity.Examples.Decision.memParamSame = .unknown :=
  ⟨Solidity.Examples.DecisionGapCensus.hiddenParameter_target,
    Solidity.Examples.DecisionGapCensus.hiddenParameter_unknown⟩

end Solidity.Examples.DecisionNumericCoverage
