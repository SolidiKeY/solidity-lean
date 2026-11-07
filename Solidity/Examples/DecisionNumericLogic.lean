import Solidity.Calculus.DecisionNumericLogic
import Solidity.Examples.DecisionUIntBridge

/-! # Numeric logical source, size and actual-leaf controls
The general leaf traversal obligation stays explicit in the conditional API;
these clients discharge it with actual source terms and kernel equations.
-/
namespace Solidity.Examples.DecisionNumericLogic
open Solidity.Decide
open Solidity.Examples.DecisionCoefficientBoundary (Bank)
open Solidity.Examples.DecisionUIntBridge
set_option Elab.async false

def reflexiveBody : Fml Bank [.val .uint] := .eq current current
def positiveBody : Fml Bank [.val .uint] :=
  .and (.imp partialBody partialBody) (.not (.not reflexiveBody))
def negativeBody : Fml Bank [.val .uint] := .and positiveBody partialBody

theorem reflexive_grammar : reflexiveBody.QFUIntLinear := .eq current_grammar current_grammar

theorem positive_grammar : positiveBody.QFUIntLinear :=
  .and (.imp partialBody_grammar partialBody_grammar) (.not (.not reflexive_grammar))

theorem negative_grammar : negativeBody.QFUIntLinear := .and positive_grammar partialBody_grammar

def positive : Fml Bank [] := .all (.user "x") .uint positiveBody
def negative : Fml Bank [] := .all (.user "x") .uint negativeBody

def partialLower : LFml Bank := LFml.optEq (lowered 1) (lowered 2)
def positiveLower : LFml Bank :=
  .and (.imp partialLower partialLower) (.not (.not (.eq (p := .uint) (.var 0) (.var 0))))
def negativeLower : LFml Bank := .and positiveLower partialLower

theorem partial_lower_grammar : partialLower.UIntQF (fun q => q = ⟨.uint, 0⟩) (fun _ => False) :=
  .optEq (.sub rfl (.var 0 rfl) (.lit _)) (.sub rfl (.var 0 rfl) (.lit _))

theorem positive_lower_grammar : positiveLower.UIntQF (fun q => q = ⟨.uint, 0⟩) (fun _ => False) :=
  .and (.imp partial_lower_grammar partial_lower_grammar) (.not (.not (.eq (.var 0 rfl) (.var 0 rfl))))

theorem negative_lower_grammar : negativeLower.UIntQF (fun q => q = ⟨.uint, 0⟩) (fun _ => False) :=
  .and positive_lower_grammar partial_lower_grammar

theorem positive_actual_leaf : leafOf? positive = some (.all 0 .uint positiveLower) := by rfl

theorem negative_actual_leaf : leafOf? negative = some (.all 0 .uint negativeLower) := by rfl

theorem positive_translation : positiveBody.toLS true ((SymS.init (C := Bank)).pushQ .uint) =
    some positiveLower := by rfl

theorem negative_translation : negativeBody.toLS true ((SymS.init (C := Bank)).pushQ .uint) =
    some negativeLower := by rfl

/-- Coverage uses a bound derived from the original source, not an assumed prepared budget. -/
theorem positive_nodes_from_source : positiveLower.nodes ≤ 511 := by
  obtain ⟨ψ, hp, hn, hf, hb, hi, he⟩ :=
    qfUIntLinear_formula_bound positive_grammar (by decide +kernel)
  have hψ : ψ = positiveLower := Option.some.inj (hp.symm.trans positive_translation)
  exact hψ ▸ hb

theorem negative_nodes_from_source : negativeLower.nodes ≤ 511 := by
  obtain ⟨ψ, hp, hn, hf, hb, hi, he⟩ :=
    qfUIntLinear_formula_bound negative_grammar (by decide +kernel)
  have hψ : ψ = negativeLower := Option.some.inj (hp.symm.trans negative_translation)
  exact hψ ▸ hb

theorem positive_covered : positive.Covered = true :=
  qfUIntLogic_Covered_of_leaf positive_lower_grammar positive_nodes_from_source positive_actual_leaf

theorem negative_covered : negative.Covered = true :=
  qfUIntLogic_Covered_of_leaf negative_lower_grammar negative_nodes_from_source negative_actual_leaf

theorem positive_target : positive.inTarget {} = true := qfUIntPrefix_inTarget _ positive_grammar _

theorem negative_target : negative.inTarget {} = true := qfUIntPrefix_inTarget _ negative_grammar _

theorem positive_valid : Fml.Valid positive := by
  intro σ x
  exact ⟨fun h => h, fun h => h rfl⟩

theorem negative_countermodel : ¬ holds (State.init Bank) negative := by
  intro h
  exact one_halting_unequal (h (uintOfNat 1)).2

/-- Kernel verdict certificate, separate from the executable output observation. -/
theorem positive_verdict : decideGoal positive = .proved := by
  have hh : positive.hasHash = false := qfUIntPrefix_hashFree _ positive_grammar
  have hd : decideGoal positive ≠ .unknown := decideGoal_complete positive_covered hh
  have hv : Fml.ValidH positive := (Fml.validH_iff hh).mpr positive_valid
  cases he : decideGoal positive with
  | proved => rfl
  | refuted σ => exact False.elim (decideGoal_refutes he (hv σ))
  | unknown => exact False.elim (hd he)

theorem negative_verdict : ∃ σ : State Bank [], decideGoal negative = .refuted σ ∧
    ¬ Fml.holdsH σ negative := by
  have hh : negative.hasHash = false := qfUIntPrefix_hashFree _ negative_grammar
  have hd : decideGoal negative ≠ .unknown := decideGoal_complete negative_covered hh
  cases he : decideGoal negative with
  | proved =>
    have hv : Fml.Valid negative := (Fml.validH_iff hh).mp (decideGoal_sound he)
    exact False.elim (negative_countermodel (hv (State.init Bank)))
  | refuted σ => exact ⟨σ, rfl, decideGoal_refutes he⟩
  | unknown => exact False.elim (hd he)

/-- The compositional source bound is inhabited by logical combinations. -/
theorem negative_source_weight : negativeBody.uintQFWeight ≤ 511 := by decide +kernel

/-- info: ["proved", "refuted"] -/
#guard_msgs in #eval [positive, negative].map (fun φ => match decideGoal φ with
  | .proved => "proved" | .refuted _ => "refuted" | .unknown => "unknown")

/-- The empty logical body has conditional weight zero, not the equality weight two. -/
theorem tt_exact : (LFml.all 0 .uint (.tt : LFml Bank)).inExact = true ∧
    (LFml.all 0 .uint (.tt : LFml Bank)).exactBounded = true :=
  LFml.UIntQF.exact_tests (.tt : LFml.UIntQF (fun q => q = ⟨.uint, 0⟩) (fun _ => False) .tt)
    (by decide +kernel)

/-- The source bound includes all logical constructors and optional copies. -/
theorem exact_source_weights : positiveBody.uintQFWeight = 141 ∧ negativeBody.uintQFWeight = 197 := by
  decide +kernel

theorem actual_lowered_nodes : positiveLower.nodes = 117 ∧ negativeLower.nodes = 173 := by
  decide +kernel

def foreign : LFml Bank := .eq (p := .uint) (.var 1) (.var 1)

theorem foreign_numeric : foreign.UIntQF (fun q => q = ⟨.uint, 1⟩) (fun _ => False) :=
  .eq (.var 1 rfl) (.var 1 rfl)

/-- Numeric shape alone does not discharge the unchanged closed-prefix premise. -/
theorem foreign_parameter_refused : (LFml.all 0 .uint foreign).inExact = false := by
  decide +kernel

end Solidity.Examples.DecisionNumericLogic
