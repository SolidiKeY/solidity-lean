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

/-- info: ["proved", "refuted"] -/
#guard_msgs in #eval [positive, negative].map (fun φ => match decideGoal φ with
  | .proved => "proved" | .refuted _ => "refuted" | .unknown => "unknown")

end Solidity.Examples.DecisionNumericNormalization
