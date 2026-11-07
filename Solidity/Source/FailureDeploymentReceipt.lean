import Solidity.Source.FailureDeploymentHorizon
import Solidity.Source.Session

/-! Actual enabled-plan deployment receipt transport. Receipt emission is
outside the body-event budget, as in Source.deployRun. No deployment fate
ordinal or post-fee session installation is implemented by these laws. -/
namespace Solidity.Source.FailureExecution.PlannedDeploy
open EM
open Solidity.Roadmap (Address SessionEnv)
variable {E : Env}

theorem deployRun_grow (P : SrcProg E) (env : SessionEnv) (addr : Address)
    (horizon : Nat) (points : Roadmap.Evm.FailurePoints) :
    Grow (deployRun (plan := some points) P env addr horizon) := by
  unfold deployRun
  grow_go [deploy_grow, emitEvent_grow]

theorem deployRun_approx (P : SrcProg E) (env : SessionEnv) (addr : Address)
    (horizon : Nat) (points : Roadmap.Evm.FailurePoints) :
    Approx (deployRun (plan := some points) P env addr horizon)
      (deployRun (plan := some points) P env addr (horizon+1)) := by
  unfold deployRun
  refine Approx.bind (deploy_approx (P.glob env) horizon P.main addr env.deployer env.deployValue env.deployArgs) fun _ => ?_
  exact Approx.refl (by grow_go [emitEvent_grow])

theorem deployRun_events_mono (P : SrcProg E) (env : SessionEnv) (addr : Address)
    (points : Roadmap.Evm.FailurePoints) (locals : Locals E.layout []) (state : St E)
    {horizon later : Nat} (more : horizon ≤ later) :
    ((deployRun (plan := some points) P env addr horizon).run (locals,state)).2.2.events <+:
      ((deployRun (plan := some points) P env addr later).run (locals,state)).2.2.events := by
  have approx := Approx.mono (fun n => deployRun_approx P env addr n points)
    (fun n => deployRun_grow P env addr n points) more
  rcases approx.2.2 (locals,state) with cut | same
  · exact cut.2
  · rw [same]
    exact List.prefix_refl _

end Solidity.Source.FailureExecution.PlannedDeploy
