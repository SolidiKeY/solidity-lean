import Solidity.Calculus.DecisionNormalizationResidue
import Solidity.Examples.Decision

/-! # Inhabited source-budget controls
The large body uses both actual uint locals. Normalizer-stage results and public
verdicts are observed separately; a sibling may clear one stage and fail another.
-/
namespace Solidity.Examples.DecisionNormalizationResidue
open Solidity.Decide Solidity.Decide.ResidueReason Solidity.Examples.Decision

def repeated {Γ : Ctx} (atom : Fml Gaps Γ) : Nat → Fml Gaps Γ
  | 0 => atom
  | n + 1 => .and (repeated atom n) (repeated atom n)

def numericAtom : Fml Gaps [.val .uint, .val .uint] :=
  .eq (.app2 (.binop .add rfl) (.pvV .here) (.pvV (.there .here)))
    (.app0 (.lit (uintOfNat 5)))
def exhaustedBody : Fml Gaps [.val .uint, .val .uint] := repeated numericAtom 10
def siblingBody : Fml Gaps [.val .uint, .val .uint] := repeated numericAtom 9

def exhausted : Fml Gaps [] :=
  .all (.user "x") .uint (.all (.user "y") .uint exhaustedBody)
def sibling : Fml Gaps [] :=
  .all (.user "x") .uint (.all (.user "y") .uint siblingBody)
def small : Fml Gaps [] :=
  .all (.user "x") .uint (.all (.user "y") .uint numericAtom)
def wrongSort : Fml Gaps [] :=
  .all (.user "x") .bool (.all (.user "y") .uint (repeated .tt 10))
def extraBinder : Fml Gaps [] :=
  .all (.user "x") .uint (.all (.user "y") .uint
    (.all (.user "z") .uint (repeated .tt 10)))
def outsideGrammar : Fml Gaps [] :=
  .all (.user "x") .uint (.all (.user "y") .uint (.havoc (repeated .tt 10)))
def reflexive : Fml Gaps [] :=
  .all (.user "x") .uint (.eq (.pvV .here) (.pvV .here))

/-- info: [2049, 1025] -/
#guard_msgs in
#eval [exhaustedBody.normalizationWork + 2, siblingBody.normalizationWork + 2]
/-- info: [true, false, false, false, false] -/
#guard_msgs in
#eval [exhausted.twoUIntPrefixOverNormalizationBudget,
  sibling.twoUIntPrefixOverNormalizationBudget, wrongSort.twoUIntPrefixOverNormalizationBudget,
  extraBinder.twoUIntPrefixOverNormalizationBudget, outsideGrammar.twoUIntPrefixOverNormalizationBudget]
/-- info: [true, true, false] -/
#guard_msgs in
#eval [exhausted.inTarget {}, sibling.inTarget {}, exhausted.hasHash]
/-- info: [false, true] -/
#guard_msgs in
#eval [(ProgramNormalization.ofFormula? 2048 exhausted).isSome,
  (ProgramNormalization.ofFormula? 2048 sibling).isSome]
/-- info: ["unknown", "unknown", "refuted", "proved", "unknown"] -/
#guard_msgs in
#eval [verdict exhausted, verdict sibling, verdict small, verdict reflexive, verdict gapHashNegForall]

theorem exhausted_sourceFacts : exhaustedBody.QFUIntLinear ∧
    2048 < exhaustedBody.normalizationWork + 2 ∧ exhausted.NormalizationBudgetResidue := by
  decide +kernel

theorem classifier_controls : exhausted.twoUIntPrefixOverNormalizationBudget = true ∧
    sibling.twoUIntPrefixOverNormalizationBudget = false ∧
    wrongSort.twoUIntPrefixOverNormalizationBudget = false ∧
    extraBinder.twoUIntPrefixOverNormalizationBudget = false ∧
    outsideGrammar.twoUIntPrefixOverNormalizationBudget = false := by
  decide +kernel

theorem target_controls : exhausted.inTarget {} = true ∧
    sibling.inTarget {} = true ∧ exhausted.hasHash = false := by
  decide +kernel

theorem sibling_normalizes : (ProgramNormalization.ofFormula? 2048 sibling).isSome = true := by
  decide +kernel

/-- A concrete typed member whose source uses both actual uint locals. -/
def exhaustedWitness : TwoUIntPrefixOverNormalizationBudget exhausted :=
  .mk (.user "x") (.user "y") exhaustedBody exhausted_sourceFacts.1 exhausted_sourceFacts.2.1

theorem exhausted_normalizer_none : ProgramNormalization.ofFormula? 2048 exhausted = none := by
  exact exhaustedWitness.normalizer_none

theorem nonresidual_targets : small.inTarget {} = true ∧ reflexive.inTarget {} = true ∧
    ¬ small.NormalizationBudgetResidue ∧ ¬ reflexive.NormalizationBudgetResidue := by
  decide +kernel

def smallCounterexample : State Gaps [] :=
  match decideGoal small with
  | .refuted σ => σ
  | _ => State.init Gaps

theorem reflexive_proved : decideGoal reflexive = .proved := by
  rfl

theorem small_decision_refuted : decideGoal small = .refuted smallCounterexample := by
  rfl

/-- Validity uses the existing exact goal hash premise. -/
theorem reflexive_validH : Fml.ValidH reflexive := decideGoal_sound reflexive_proved

/-- The state returned by the actual decision refutes this quantified source. -/
theorem small_countermodel : ¬ Fml.holdsH smallCounterexample small :=
  decideGoal_refutes small_decision_refuted

#print axioms exhausted_sourceFacts
#print axioms exhausted_normalizer_none
#print axioms nonresidual_targets
#print axioms reflexive_validH
#print axioms small_countermodel

end Solidity.Examples.DecisionNormalizationResidue
