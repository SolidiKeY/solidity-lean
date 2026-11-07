import Solidity.Source.FailureDeploymentReceipt
import Solidity.Source.FailureConstructorControls

/-! Actual registered initcode and nonempty constructor-body transport under
both Source pipeline settings. Frozen fixture outcomes are reused, not replaced
by desired execution premises. No native comparison/session-fate claim. -/
namespace Solidity.Source.FailureExecution.PlannedDeploy.Controls
open EM SemanticsExamples
open ConstructorControls (E input global points prior callEvent answerEvent)

theorem initializer_prefix (pipeline : Roadmap.Pipeline) (cut : Option Nat)
    {horizon later : Nat} (more : horizon ≤ later) :
    (ConstructorControls.run pipeline cut horizon).2.2.events <+:
      (ConstructorControls.run pipeline cut later).2.2.events :=
  deploy_events_mono (points := points cut) (global pipeline) "C" thisC user (word 0) [] (L0 E) input more

theorem completed_cut_stable (pipeline : Roadmap.Pipeline) (later : Nat) (more : 20 ≤ later) :
    ConstructorControls.run pipeline (some 1) later = ConstructorControls.run pipeline (some 1) := by
  apply deploy_stable (points := points (some 1)) (more := more)
  change (ConstructorControls.run pipeline (some 1)).1 ≠ .error .timeout
  rw [ConstructorControls.cut1_revert]
  intro impossible
  cases impossible

/-- The actual constructor body, not just initializers, invokes runMods. -/
theorem body_cut_stable (pipeline : Roadmap.Pipeline) (later : Nat) (more : 20 ≤ later) :
    (deploy (plan := some (points (some 1))) (ConstructorControls.bodyGlobal pipeline)
      later "C" thisC user (word 0) []).run (L0 E,input) = ConstructorControls.runBody pipeline (some 1) := by
  apply deploy_stable (points := points (some 1)) (more := more)
  change (ConstructorControls.runBody pipeline (some 1)).1 ≠ .error .timeout
  rw [(ConstructorControls.body_cut1 pipeline).1]
  intro impossible
  cases impossible

/-- Propagated ancestor stops retain their complete state and remain
exceptional. Horizon stability does not turn them into completed reverts. -/
theorem ancestor_stop_stable (pipeline : Roadmap.Pipeline) (later : Nat) (more : 20 ≤ later) :
    (deploy (plan := some ConstructorControls.ancestorPlan) (global pipeline)
      later "C" thisC user (word 0) []).run (L0 E,ConstructorControls.ancestorInput) =
      ConstructorControls.runAncestor pipeline := by
  apply deploy_stable (more := more)
  change (ConstructorControls.runAncestor pipeline).1 ≠ .error .timeout
  rw [(ConstructorControls.ancestor_stop_propagates pipeline).1]
  intro impossible
  cases impossible

/-- A real cut before the external return has a shorter trace than the
uncut fixture. Arbitrary changing of plans is not covered by prefix transport. -/
theorem changed_plan_not_prefix (pipeline : Roadmap.Pipeline) :
    ¬ ((ConstructorControls.run pipeline none).2.2.events <+:
      (ConstructorControls.run pipeline (some 1)).2.2.events) := by
  rw [ConstructorControls.uncut_events, (ConstructorControls.cut1_root_state pipeline).2.1]
  intro included
  have size := included.length_le
  change 3 ≤ 2 at size
  omega

end Solidity.Source.FailureExecution.PlannedDeploy.Controls

/-- info: 'Solidity.Source.FailureExecution.PlannedDeploy.runInits_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedDeploy.runInits_grow

/-- info: 'Solidity.Source.FailureExecution.PlannedDeploy.runInits_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedDeploy.runInits_approx

/-- info: 'Solidity.Source.FailureExecution.PlannedDeploy.giveArgs_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedDeploy.giveArgs_grow

/-- info: 'Solidity.Source.FailureExecution.PlannedDeploy.giveArgs_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedDeploy.giveArgs_approx

/-- info: 'Solidity.Source.FailureExecution.PlannedDeploy.collectArgs_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedDeploy.collectArgs_grow

/-- info: 'Solidity.Source.FailureExecution.PlannedDeploy.collectArgs_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedDeploy.collectArgs_approx

/-- info: 'Solidity.Source.FailureExecution.PlannedDeploy.runCtorBody_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedDeploy.runCtorBody_grow

/-- info: 'Solidity.Source.FailureExecution.PlannedDeploy.runCtorBody_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedDeploy.runCtorBody_approx

/-- info: 'Solidity.Source.FailureExecution.PlannedDeploy.construct_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedDeploy.construct_grow

/-- info: 'Solidity.Source.FailureExecution.PlannedDeploy.construct_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedDeploy.construct_approx

/-- info: 'Solidity.Source.FailureExecution.PlannedDeploy.deploy_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedDeploy.deploy_grow

/-- info: 'Solidity.Source.FailureExecution.PlannedDeploy.deploy_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedDeploy.deploy_approx

/-- info: 'Solidity.Source.FailureExecution.PlannedDeploy.deploy_events_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedDeploy.deploy_events_mono

/-- info: 'Solidity.Source.FailureExecution.PlannedDeploy.deploy_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedDeploy.deploy_stable

/-- info: 'Solidity.Source.FailureExecution.PlannedDeploy.deployRun_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedDeploy.deployRun_grow

/-- info: 'Solidity.Source.FailureExecution.PlannedDeploy.deployRun_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedDeploy.deployRun_approx

/-- info: 'Solidity.Source.FailureExecution.PlannedDeploy.deployRun_events_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedDeploy.deployRun_events_mono

/-- info: 'Solidity.Source.FailureExecution.PlannedDeploy.Controls.initializer_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedDeploy.Controls.initializer_prefix

/-- info: 'Solidity.Source.FailureExecution.PlannedDeploy.Controls.completed_cut_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedDeploy.Controls.completed_cut_stable

/-- info: 'Solidity.Source.FailureExecution.PlannedDeploy.Controls.body_cut_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedDeploy.Controls.body_cut_stable

/-- info: 'Solidity.Source.FailureExecution.PlannedDeploy.Controls.ancestor_stop_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedDeploy.Controls.ancestor_stop_stable

/-- info: 'Solidity.Source.FailureExecution.PlannedDeploy.Controls.changed_plan_not_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedDeploy.Controls.changed_plan_not_prefix
