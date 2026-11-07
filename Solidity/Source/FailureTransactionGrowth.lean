import Solidity.Source.FailureEvaluatorGrow
import Solidity.Source.Semantics

/-! Actual planned root-transaction event growth from the closed evaluator
induction. No fee installation, NoFail or desired result is assumed. This
is not horizon approximation, fixed-plan session consistency or P8 adequacy. -/
namespace Solidity.Source.FailureExecution
open EM
variable {E : Env}

theorem runTxWithPlan_grow (G : Glob E) (horizon : Nat) (request : Roadmap.Request)
    (points : Roadmap.Evm.FailurePoints) : Grow (runTxWithPlan G horizon request points) := by
  have ih := PlannedGrow.growAt { G with timestamp := request.timestamp }
    (points := points) horizon
  unfold runTxWithPlan
  grow_go [check_grow, frame_grow, ih.dispatch, instanceAt_grow,
    mark_grow, credit_grow, rollbackTo_grow, emitEvent_grow]

end Solidity.Source.FailureExecution

/-- info: 'Solidity.Source.FailureExecution.runTxWithPlan_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.runTxWithPlan_grow
