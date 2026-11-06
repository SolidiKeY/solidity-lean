import Solidity.Source.FailureEvaluatorApprox
import Solidity.Source.FailureTransactionGrowth

/-! Fixed-plan actual root event approximation at every larger horizon,
including timeouts. No fee/session, deployment or P8 realization is asserted. -/
namespace Solidity.Source.FailureExecution
open EM
variable {E : Env}

theorem runTxWithPlan_approx (G : Glob E) (horizon : Nat) (request : Roadmap.Request)
    (points : Roadmap.Evm.FailurePoints) :
    Approx (runTxWithPlan G horizon request points) (runTxWithPlan G (horizon+1) request points) := by
  have ih := PlannedApprox.approxAt { G with timestamp := request.timestamp }
    (points := points) horizon
  unfold runTxWithPlan
  refine Approx.bind (Approx.refl (check_grow _)) fun _ => ?_
  refine Approx.bind (Approx.refl mark_grow) fun saved => ?_
  refine Approx.bind (Approx.refl (instanceAt_grow _ _)) fun current => ?_
  split
  · exact Approx.refl (by grow_go [check_grow, emitEvent_grow])
  · refine Approx.attempt_bind ?_ (fun _ => Approx.refl (by grow_go [check_grow, rollbackTo_grow, emitEvent_grow]))
      (fun _ => ⟨rfl,rfl⟩)
    exact frame_approx _ (Approx.bind (Approx.refl (credit_grow _ _)) fun _ => ih.dispatch _ _)

theorem runTxWithPlan_events_mono (G : Glob E) (request : Roadmap.Request)
    (points : Roadmap.Evm.FailurePoints) (locals : Locals E.layout []) (state : St E)
    {horizon later : Nat} (more : horizon ≤ later) :
    ((runTxWithPlan G horizon request points).run (locals,state)).2.2.events <+:
      ((runTxWithPlan G later request points).run (locals,state)).2.2.events := by
  have approx := Approx.mono (fun n => runTxWithPlan_approx G n request points)
    (fun n => runTxWithPlan_grow G n request points) more
  rcases approx.2.2 (locals,state) with cut | same
  · exact cut.2
  · rw [same]
    exact List.prefix_refl _

end Solidity.Source.FailureExecution
