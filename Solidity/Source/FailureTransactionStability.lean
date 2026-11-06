import Solidity.Source.FailureEvaluatorStability

/-! Completed planned transactions have exactly the same full result at
larger horizons. Fixed choices are retained. This is not the missing event
prefix approximation on timeout, session consistency or P8 realization. -/
namespace Solidity.Source.FailureExecution
open EM
variable {E : Env}

theorem runTxWithPlan_below (G : Glob E) (horizon : Nat) (request : Roadmap.Request)
    (points : Roadmap.Evm.FailurePoints) :
    Below (runTxWithPlan G horizon request points) (runTxWithPlan G (horizon+1) request points) := by
  have ih := PlannedBelow.belowAt { G with timestamp := request.timestamp }
    (points := points) horizon
  unfold runTxWithPlan
  refine Below.bind (Below.refl _) fun _ => ?_
  refine Below.bind (Below.refl _) fun saved => ?_
  refine Below.bind (Below.refl _) fun current => ?_
  split
  · exact Below.refl _
  · refine Below.attempt_bind ?_ (fun _ => Below.refl _) (fun _ => rfl)
    exact frame_below _ (Below.bind (Below.refl _) fun _ => ih.dispatch _ _)

theorem runTxWithPlan_stable (G : Glob E) (request : Roadmap.Request)
    (points : Roadmap.Evm.FailurePoints) (locals : Locals E.layout []) (state : St E)
    {horizon later : Nat} (more : horizon ≤ later)
    (completed : ((runTxWithPlan G horizon request points).run (locals,state)).1 ≠ .error .timeout) :
    (runTxWithPlan G later request points).run (locals,state) =
      (runTxWithPlan G horizon request points).run (locals,state) := by
  exact Below.eq_of_done
    (Below.mono (fun n => runTxWithPlan_below G n request points) more) (locals,state) completed

end Solidity.Source.FailureExecution
