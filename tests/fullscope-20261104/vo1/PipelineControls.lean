import Solidity.Optimizer.Laws

/-! Finite pipeline controls. Parity is a test observation, not the D6 contract.
An accepted first stage, rejected middle stage and accepted final stage distinguish
per-stage fallback from rolling back the whole pipeline or admitting the mutation. -/
namespace Solidity.Optimizer.PipelineControls

def SameParity (p q : Nat) : Prop := p % 2 = q % 2

def parityValidator : Validator SameParity where
  validate p q := decide (p % 2 = q % 2)
  sound p q accepted := @of_decide_eq_true (p % 2 = q % 2) _ accepted

def proposals : List (Pass Nat) :=
  [fun n => n + 2, fun n => n + 1, fun n => n * 3]

theorem stages_preserve : Preserves SameParity
    (guardedPipeline parityValidator proposals) :=
  guardedPipeline_preserves (Related := SameParity) (fun _ => rfl) (fun a b => a.trans b)
    parityValidator proposals

theorem first_accepted : parityValidator.validate 37 39 = true := rfl

theorem middle_rejected : parityValidator.validate 39 40 = false := rfl

theorem final_accepted : parityValidator.validate 39 117 = true := rfl

theorem intermediate_fallback :
    guardedPipeline parityValidator proposals 37 = 117 := rfl

theorem empty_pipeline : guardedPipeline parityValidator [] 37 = 37 := rfl

#print axioms Pass.pipeline_append
#print axioms Preserves.pipeline
#print axioms guardedPipeline_preserves
#print axioms parityValidator
#print axioms stages_preserve
#print axioms first_accepted
#print axioms middle_rejected
#print axioms final_accepted
#print axioms intermediate_fallback
#print axioms empty_pipeline
end Solidity.Optimizer.PipelineControls
