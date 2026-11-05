import Solidity.Calculus.DecisionPrefixNormalizationResidue
import Solidity.Calculus.DecisionNormalizationResidue
import Solidity.Examples.Decision

/-! # Inhabited arbitrary-prefix source-work controls
All three uint locals occur in the numeric atom. Source-stage refusal and
public decisions are separate; these certificates do not extend coverage.
-/
namespace Solidity.Examples.DecisionPrefixNormalizationResidue
open Solidity.Decide Solidity.Decide.ResidueReason Solidity.Examples.Decision
set_option Elab.async false

def atom : Fml Gaps [.val .uint, .val .uint, .val .uint] :=
  .eq (.app2 (.binop .add rfl) (.pvV .here) (.pvV (.there .here)))
    (.pvV (.there (.there .here)))

def branching {Γ : Ctx} (body : Fml Gaps Γ) : Nat → Fml Gaps Γ
  | 0 => body
  | depth + 1 => .and (branching body depth) (branching body depth)

def prefixed (depth : Nat) : Fml Gaps [] :=
  .all (.user "x") .uint (.all (.user "y") .uint
    (.all (.user "z") .uint (branching atom depth)))

def exhausted : Fml Gaps [] := prefixed 10
def sibling : Fml Gaps [] := prefixed 9
def mixed : Fml Gaps [] := .all (.user "flag") .bool
  (.all (.user "x") .uint (.eq (.pvV .here) (.pvV .here)))
def outside : Fml Gaps [] := .havoc (.tt)

/-- info: [2050, 1026, 3] -/
#guard_msgs in
#eval [exhausted.normalizationWork, sibling.normalizationWork, mixed.normalizationWork]

/-- Genuine three-binder membership, beyond the previous two-binder reason. -/
theorem exhausted_sourceFacts : exhausted.NumericPrimitivePrefix ∧
    exhausted.PrimitivePrefixNormalizationResidue ∧
    exhausted.twoUIntPrefixOverNormalizationBudget = false ∧
    exhausted.inTarget {} = true ∧ exhausted.hasHash = false := by
  decide +kernel

/-- A nearby numeric prefix fits the original budget, and a non-prefix is rejected. -/
theorem classification_controls : sibling.NumericPrimitivePrefix ∧
    ¬ sibling.PrimitivePrefixNormalizationResidue ∧ mixed.NumericPrimitivePrefix ∧
    ¬ mixed.PrimitivePrefixNormalizationResidue ∧ ¬ outside.NumericPrimitivePrefix := by
  decide +kernel

/-- The actual over-budget source fails normalization, using the structural proof. -/
theorem exhausted_normalizer_none : ProgramNormalization.ofFormula? 2048 exhausted = none :=
  primitivePrefixNormalizationResidue_normalizer_none exhausted_sourceFacts.2.1

/-- The sibling succeeds by the exact formula-derived work boundary. -/
theorem sibling_normalizes : (ProgramNormalization.ofFormula? 2048 sibling).isSome = true :=
  (numericPrimitivePrefix_normalization_iff_work classification_controls.1 2048).mpr
    (by decide +kernel)

/-- Non-uint primitive binders contribute exactly one source visit too. -/
theorem mixed_exact_budget : (ProgramNormalization.ofFormula? 3 mixed).isSome = true ∧
    (ProgramNormalization.ofFormula? 2 mixed).isSome = false := by
  decide +kernel

/-- info: ["unknown", "unknown", "proved", "refuted"] -/
#guard_msgs in
#eval [verdict exhausted, verdict sibling, verdict mixed, verdict (prefixed 0)]

/-- The actual public positive verdict, separate from the normalization certificate. -/
theorem mixed_proved : decideGoal mixed = .proved := by
  rfl

/-- The positive result uses the existing exact hash-premised semantics. -/
theorem mixed_validH : Fml.ValidH mixed := decideGoal_sound mixed_proved

def small : Fml Gaps [] := prefixed 0

def smallCountermodel : State Gaps [] :=
  match decideGoal small with
  | .refuted state => state
  | _ => State.init Gaps

/-- The actual returned negative certificate for the small three-local source. -/
theorem small_refuted : decideGoal small = .refuted smallCountermodel := by
  rfl

/-- Refutation retains the unchanged goal hash premise. -/
theorem small_countermodel : ¬ Fml.holdsH smallCountermodel small :=
  decideGoal_refutes small_refuted

end Solidity.Examples.DecisionPrefixNormalizationResidue
