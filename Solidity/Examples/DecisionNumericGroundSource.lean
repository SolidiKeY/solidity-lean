import Solidity.Calculus.DecisionNumericGroundSource
import Solidity.Examples.DecisionNumericGround

/-! # Source-derived ground boundary and actual verdict clients -/
namespace Solidity.Examples.DecisionNumericGroundSource
open Solidity.Decide
open Solidity.Examples.DecisionCoefficientBoundary (Bank)
set_option Elab.async false

def zero : Tm Bank [] (.val .uint) := .app0 (.lit (uintOfNat 0))
def one : Tm Bank [] (.val .uint) := .app0 (.lit (uintOfNat 1))
def partialTerm : Tm Bank [] (.val .uint) := .app2 (.binop .sub rfl) zero one
def bothFailed : Fml Bank [] := .eq partialTerm partialTerm
def mismatched : Fml Bank [] := .eq partialTerm zero
def combined : Fml Bank [] := .and (.imp mismatched mismatched) bothFailed

theorem partial_grammar : partialTerm.UIntLinear := .sub (.lit _) (.lit _)
theorem both_grammar : bothFailed.QFUIntLinear := .eq partial_grammar partial_grammar
theorem mismatched_grammar : mismatched.QFUIntLinear := .eq partial_grammar (.lit _)
theorem combined_grammar : combined.QFUIntLinear :=
  .and (.imp mismatched_grammar mismatched_grammar) both_grammar

theorem source_weights : bothFailed.uintQFWeight = 55 ∧
    mismatched.uintQFWeight = 41 ∧ combined.uintQFWeight = 139 := by
  decide +kernel

theorem all_waiver_boundary (w : Waivers) :
    bothFailed.inTarget w = true ∧ bothFailed.Covered = true ∧ bothFailed.hasHash = false :=
  qfUIntGround_logic_boundary w both_grammar (by decide +kernel)

theorem combination_covered : combined.Covered = true :=
  qfUIntGround_logic_Covered combined_grammar (by decide +kernel)

theorem positive_result : decideGoal bothFailed = .proved := by rfl

theorem negative_result : ∃ σ : State Bank [], decideGoal mismatched = .refuted σ := by
  exact ⟨(State.init Bank), by rfl⟩

theorem positive_certificate : Fml.ValidH bothFailed := decideGoal_sound positive_result

theorem negative_certificate : ∃ σ : State Bank [],
    decideGoal mismatched = .refuted σ ∧ ¬ Fml.holdsH σ mismatched := by
  obtain ⟨σ, hσ⟩ := negative_result
  exact ⟨σ, hσ, decideGoal_refutes hσ⟩

theorem combined_answered : decideGoal combined ≠ .unknown :=
  qfUIntGround_logic_answered combined_grammar (by decide +kernel)

end Solidity.Examples.DecisionNumericGroundSource
