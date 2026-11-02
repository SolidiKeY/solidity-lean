import Solidity.Calculus.DecisionNumericNormalization
import Solidity.Examples.DecisionNumericLogic
import Solidity.Examples.DecisionArrayGaps

/-! # Actual normalizer and source-bound coverage clients
Truth simplification is observed, not suppressed. Kernel certificates remain
separate from executable verdict observations and the unclosed global theorem.
-/
namespace Solidity.Examples.DecisionNumericNormalization
open Solidity.Decide
open Solidity.Examples.DecisionCoefficientBoundary (Bank)
set_option Elab.async false

def collapsed : Fml Bank [] := .and .tt (.and .tt .tt)

theorem collapsed_grammar : collapsed.QFUIntLinear := .and .tt (.and .tt .tt)

theorem collapsed_source_weight : collapsed.uintQFWeight = 5 := by rfl

/-- Depth4 is enough for this depth3 formula, but its shared5-node traversal
cannot run with budget4 even though the eventual output has only one node. -/
theorem shared_budget_refusal : ProgramNormalization.ofFormula? 4 collapsed = none := by rfl

theorem shared_budget_sufficient :
    (ProgramNormalization.ofFormula? 5 collapsed).map (·.formula) = some .tt := by rfl

/-- A kernel counterexample to the abandoned identity proof plan. -/
theorem normalization_changes_syntax :
    (ProgramNormalization.ofFormula? 2048 collapsed).map (·.formula) ≠ some collapsed := by
  change some (Fml.tt : Fml Bank []) ≠ some (.and .tt (.and .tt .tt))
  intro h
  cases h

def positiveBody : Fml Bank [.val .uint] := .and .tt DecisionNumericLogic.positiveBody
def negativeBody : Fml Bank [.val .uint] := .imp .tt DecisionNumericLogic.negativeBody

theorem positive_grammar : positiveBody.QFUIntLinear := .and .tt DecisionNumericLogic.positive_grammar

theorem negative_grammar : negativeBody.QFUIntLinear := .imp .tt DecisionNumericLogic.negative_grammar

def positive : Fml Bank [] := .all (.user "x") .uint positiveBody
def negative : Fml Bank [] := .all (.user "x") .uint negativeBody

/-- Both smart constructors actually remove their tt operand in the real public computation. -/
theorem actual_positive_normalization :
    (ProgramNormalization.ofFormula? 2048 positive).map (·.formula) =
      some DecisionNumericLogic.positive := by rfl

theorem actual_negative_normalization :
    (ProgramNormalization.ofFormula? 2048 negative).map (·.formula) =
      some DecisionNumericLogic.negative := by rfl

theorem source_weights : positiveBody.uintQFWeight = 143 ∧ negativeBody.uintQFWeight = 199 := by
  decide +kernel

/-- These clients use the syntax theorem, with no supplied leaf or normalizer equation. -/
theorem positive_boundary (w : Waivers) :
    positive.inTarget w = true ∧ positive.Covered = true ∧ positive.hasHash = false :=
  qfUIntPrefix_logic_boundary (.user "x") w positive_grammar (by decide +kernel)

theorem negative_boundary (w : Waivers) :
    negative.inTarget w = true ∧ negative.Covered = true ∧ negative.hasHash = false :=
  qfUIntPrefix_logic_boundary (.user "x") w negative_grammar (by decide +kernel)

theorem positive_valid : Fml.Valid positive := by
  intro σ x
  exact ⟨trivial, DecisionNumericLogic.positive_valid σ x⟩

theorem negative_countermodel : ¬ holds (State.init Bank) negative := by
  intro h
  apply DecisionNumericLogic.negative_countermodel
  intro x
  exact h x trivial

theorem positive_verdict : decideGoal positive = .proved := by
  have hh : positive.hasHash = false := (positive_boundary {}).2.2
  have hd : decideGoal positive ≠ .unknown := qfUIntPrefix_logic_answered _ positive_grammar (by decide +kernel)
  have hv : Fml.ValidH positive := (Fml.validH_iff hh).mpr positive_valid
  cases he : decideGoal positive with
  | proved => rfl
  | refuted σ => exact False.elim (decideGoal_refutes he (hv σ))
  | unknown => exact False.elim (hd he)

theorem negative_verdict : ∃ σ : State Bank [], decideGoal negative = .refuted σ ∧
    ¬ Fml.holdsH σ negative := by
  have hh : negative.hasHash = false := (negative_boundary {}).2.2
  have hd : decideGoal negative ≠ .unknown := qfUIntPrefix_logic_answered _ negative_grammar (by decide +kernel)
  cases he : decideGoal negative with
  | proved =>
    have hv : Fml.Valid negative := (Fml.validH_iff hh).mp (decideGoal_sound he)
    exact False.elim (negative_countermodel (hv (State.init Bank)))
  | refuted σ => exact ⟨σ, rfl, decideGoal_refutes he⟩
  | unknown => exact False.elim (hd he)

theorem remaining_unknown : decideGoal DecisionArrayGaps.belowKey = .unknown :=
  DecisionArrayGaps.belowKey_unknown

def shortBody : Fml Bank [.val .uint] :=
  .imp .tt (.eq DecisionUIntBridge.current DecisionUIntBridge.current)

theorem short_grammar : shortBody.QFUIntLinear :=
  .imp .tt (.eq DecisionUIntBridge.current_grammar DecisionUIntBridge.current_grammar)

/-- The source-derived sufficient bound deliberately need not be minimal. -/
theorem sufficient_not_minimal : shortBody.uintQFWeight > 3 ∧
    (ProgramNormalization.ofFormula? 3 shortBody).isSome = true := by
  exact ⟨by decide +kernel, by rfl⟩

theorem zero_budget_refusal : ProgramNormalization.ofFormula? 0 positive = none := by rfl

/-- Formula work counts actual visits, separately from arithmetic/source weights. -/
theorem exact_work_counts : collapsed.normalizationWork = 5 ∧
    shortBody.normalizationWork = 3 ∧ positiveBody.normalizationWork = 9 ∧
    negativeBody.normalizationWork = 11 := by decide +kernel

/-- The formula-derived theorem supplies real certificates, not an assumed output. -/
theorem derived_work_certificates :
    (∃ d : DeclarationReduction collapsed,
      ProgramNormalization.ofFormula? collapsed.normalizationWork collapsed = some d) ∧
    (∃ d : DeclarationReduction positive,
      ProgramNormalization.ofFormula? (positiveBody.normalizationWork + 1) positive = some d) ∧
    (∃ d : DeclarationReduction negative,
      ProgramNormalization.ofFormula? (negativeBody.normalizationWork + 1) negative = some d) :=
  ⟨qfUIntLinear_normalization_at_work collapsed_grammar,
    qfUIntPrefix_normalization_by_work (.user "x") positive_grammar,
    qfUIntPrefix_normalization_by_work (.user "x") negative_grammar⟩

/-- Both truth branches are visited even when the output collapses to one node. -/
theorem exact_work_boundary :
    ProgramNormalization.ofFormula? (collapsed.normalizationWork - 1) collapsed = none ∧
    (ProgramNormalization.ofFormula? collapsed.normalizationWork collapsed).map (·.formula) =
      some .tt := ⟨shared_budget_refusal, shared_budget_sufficient⟩

/-- Term complexity does not consume these formula visits, while the real
prefix does. This does not change any later arithmetic source/cut bound. -/
theorem arithmetic_and_prefix_controls :
    shortBody.normalizationWork < shortBody.uintQFWeight ∧
    (ProgramNormalization.ofFormula? shortBody.normalizationWork shortBody).isSome = true ∧
    ProgramNormalization.ofFormula? positiveBody.normalizationWork positive = none ∧
    (ProgramNormalization.ofFormula? (positiveBody.normalizationWork + 1) positive).isSome = true ∧
    ProgramNormalization.ofFormula? negativeBody.normalizationWork negative = none ∧
    (ProgramNormalization.ofFormula? (negativeBody.normalizationWork + 1) negative).isSome = true := by
  exact ⟨by decide +kernel, by rfl, by rfl, by rfl, by rfl, by rfl⟩

/-- A complete threshold statement for the actual shared-budget normalizer,
including every insufficient and surplus budget, despite truth collapse. -/
theorem collapsed_threshold (budget : Nat) :
    (ProgramNormalization.ofFormula? budget collapsed).isSome = true ↔ 5 ≤ budget :=
  qfUIntLinear_normalization_iff_work collapsed_grammar budget

/-- Larger arithmetic source weights do not alter the exact formula threshold. -/
theorem numeric_thresholds (budget : Nat) :
    ((ProgramNormalization.ofFormula? budget positiveBody).isSome = true ↔ 9 ≤ budget) ∧
    ((ProgramNormalization.ofFormula? budget negativeBody).isSome = true ↔ 11 ≤ budget) :=
  ⟨qfUIntLinear_normalization_iff_work positive_grammar budget,
    qfUIntLinear_normalization_iff_work negative_grammar budget⟩

/-- A generic insufficient-budget refusal supplies the concrete branching
negative control without executing a decision verdict. -/
theorem branching_refusal_from_work : ProgramNormalization.ofFormula? 4 collapsed = none :=
  qfUIntLinear_normalization_below_work collapsed_grammar 4 (by decide +kernel)

/-- info: ["proved", "refuted"] -/
#guard_msgs in #eval [positive, negative].map (fun φ => match decideGoal φ with
  | .proved => "proved" | .refuted _ => "refuted" | .unknown => "unknown")

end Solidity.Examples.DecisionNumericNormalization
