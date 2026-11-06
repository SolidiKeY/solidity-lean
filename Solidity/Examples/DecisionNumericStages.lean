import Solidity.Calculus.DecisionNumericStages
import Solidity.Examples.DecisionNumericBounds
import Solidity.Examples.DecisionNumericGroundSource

/-! # Source-derived numeric stage clients above the global cap -/
namespace Solidity.Examples.DecisionNumericStages
open Solidity.Decide
open Solidity.Examples.DecisionCoefficientBoundary (Bank)
open Solidity.Examples.DecisionNumericBounds
set_option Elab.async false

def largeBody : Fml Bank [.val .uint] := .eq (symbolicChain 18) (symbolicChain 17)

theorem largeBody_grammar : largeBody.QFUIntLinear :=
  .eq (symbolicChain_grammar 18) (symbolicChain_grammar 17)

theorem source_weight : largeBody.uintQFWeight = 517 := by decide +kernel

theorem original_source : overRawBound = .all (.user "x") .uint largeBody := by rfl

/-- The original517-node source passes every actual stage up to flattening.
No intermediate normalization/leaf equation is supplied by the caller. -/
theorem original_source_actual_stages : ∃ ψ : LFml Bank,
    leafOf? overRawBound = some (.all 0 .uint ψ) ∧ ψ.nodes = 517 ∧
      ∃ a : FlattenedFormula ψ 0, flattenFormulaAt? ψ.nodes 0 ψ = some a ∧
        a.formula = ψ ∧ a.reads = [] := by
  obtain ⟨ψ, hl, hg, hn, a, ha, hf, hr⟩ :=
    qfUIntPrefix_flatten_stage (.user "x") largeBody_grammar (by decide +kernel) 0
  have hm : (leafOf? overRawBound).map (fun ψ => ψ.stripAll.2.nodes) = some 517 :=
    overRawBound_body_nodes
  change leafOf? overRawBound = some (.all 0 .uint ψ) at hl
  have hshape : ψ.allDepth = 0 ∧ ψ.stripAll = ([], ψ) := source_body_shape (hg.source false true)
  rw [hl] at hm
  simp only [Option.map_some, LFml.stripAll, hshape.2] at hm
  exact ⟨ψ, hl, Option.some.inj hm, a, ha, hf, hr⟩

theorem closed_negative_actual_stages : ∃ ψ : LFml Bank,
    leafOf? DecisionNumericGroundSource.mismatched = some ψ ∧
      ∃ a : FlattenedFormula ψ 0, flattenFormulaAt? ψ.nodes 0 ψ = some a ∧
        a.formula = ψ ∧ a.reads = [] := by
  obtain ⟨ψ, hl, hg, hn, a, ha, hf, hr⟩ := qfUIntGround_flatten_stage
    DecisionNumericGroundSource.mismatched_grammar (by decide +kernel) 0
  exact ⟨ψ, hl, a, ha, hf, hr⟩

theorem actual_semantic_controls : Fml.ValidH overRawBound ∧
    ∃ σ : State Bank [], decideGoal DecisionNumericGroundSource.mismatched = .refuted σ ∧
      ¬ Fml.holdsH σ DecisionNumericGroundSource.mismatched :=
  ⟨overRawBound_validH, DecisionNumericGroundSource.negative_certificate⟩

theorem unchanged_global_cap : overRawBound.Covered = false ∧
    overRawBound.hashCovered = false ∧ decideGoal overRawBound = .proved :=
  ⟨overRawBound_notCovered, overRawBound_notHashCovered, overRawBound_proved⟩

end Solidity.Examples.DecisionNumericStages
