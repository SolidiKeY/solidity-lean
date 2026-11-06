import Solidity.Source.FailureFrameHorizon
import Solidity.Source.FailureRequest

/-! Actual scope transport for full-result equality or timeout. Capturing a
halt alone is not Below-preserving; cleanup must rethrow timeouts. These
laws introduce no evaluator, resource representation or session claim. -/
namespace Solidity.Source.FailureExecution
open EM
variable {E : Env} {Γ : RCtx} {α : Type}

theorem frame_below (plan : RuntimePlan) {body later : EM E Γ α}
    (h : Below body later) : Below (frame plan body) (frame plan later) := by
  cases plan with
  | none => exact h
  | some points =>
    simp only [frame]
    refine Below.bind (Below.refl _) fun _ => ?_
    refine Below.bind (Below.refl _) fun _ => ?_
    refine Below.attempt_bind ?_ (fun _ => Below.refl _) (fun _ => rfl)
    below_go [h]

theorem requestScope_below (points : Roadmap.Evm.FailurePoints)
    {body later : Nat → EM E Γ α} (h : ∀ balance, Below (body balance) (later balance)) :
    Below (requestScope points body) (requestScope points later) := by
  unfold requestScope
  refine Below.bind (Below.refl _) fun state => ?_
  by_cases quiet : state.resource.quiescent = true
  · simp only [dif_pos quiet]
    refine Below.bind (Below.refl _) fun _ => ?_
    split
    · exact Below.refl _
    · refine Below.attempt_bind ?_ (fun _ => Below.refl _) (fun _ => rfl)
      below_go [h]
  · simp only [dif_neg quiet]
    exact Below.refl _

end Solidity.Source.FailureExecution
