import Solidity.Source.FailureTransactionApprox
import Solidity.Source.FailureTransactionControls
import Solidity.Source.FailureEvaluatorGrowControls

/-! Inhabited event-prefix uses with the existing independently frozen
Source fixture. These do not generate or compare native observations.
A fixed plan is essential; captured timeouts are not completed results. -/
namespace Solidity.Source.FailureExecution.PlannedApprox.Controls
open EM SemanticsExamples
open RuntimeControls (input glob data points priorEvent callEvent answerEvent)

theorem root_prefix (pipeline : Roadmap.Pipeline) (cut : Option Nat)
    {horizon later : Nat} (more : horizon ≤ later) :
    (TransactionControls.run pipeline cut horizon).2.2.events <+:
      (TransactionControls.run pipeline cut later).2.2.events :=
  runTxWithPlan_events_mono (glob pipeline) (tx data) (points cut) (L0 EB) input more

/-- Horizon zero times out after frame entry, before any child events.
The event prefix theorem does not equate its retained state to finalization. -/
theorem timeout_prefix (pipeline : Roadmap.Pipeline) :
    (TransactionControls.run pipeline none 0).1 = .error .timeout ∧
    (TransactionControls.run pipeline none 0).2.2.events = [priorEvent] ∧
    [priorEvent] <+: [priorEvent,callEvent,answerEvent,TransactionControls.receipt (.success [])] := by
  have short := TransactionControls.zero_horizon pipeline
  have long := TransactionControls.uncut pipeline
  refine ⟨short.1,short.2.1,?_⟩
  have included := root_prefix pipeline none (horizon := 0) (later := 20) (by omega)
  rw [short.2.1,long.2.1] at included
  exact included

/-- This is a genuine completed cut, with full state from the frozen fixture,
not timeout evidence relabelled as a successful transaction. -/
theorem completed_cut (pipeline : Roadmap.Pipeline) :
    TransactionControls.run pipeline (some 1) =
      (.ok (.revert []),(.nil,TransactionControls.finalized [priorEvent,callEvent,
        TransactionControls.receipt (.revert [])])) :=
  TransactionControls.own_cut1_full_state pipeline

/-- Event inclusion fails if a consumer silently changes the failure plan. -/
theorem changed_plan_not_prefix (pipeline : Roadmap.Pipeline) :
    ¬ ((TransactionControls.run pipeline none).2.2.events <+:
      (TransactionControls.run pipeline (some 0)).2.2.events) := by
  rw [(TransactionControls.uncut pipeline).2.1,
    (TransactionControls.own_cut0 pipeline).2]
  intro included
  have size := included.length_le
  change 4 ≤ 2 at size
  omega

/-- Capturing timeout changes it into a normal result. Approximation cannot
silently substitute an unrelated completed value in that result. -/
theorem captured_timeout_not_approx :
    ¬ Approx (attempt (halt .timeout : EM EB [] Nat)) (attempt (pure 7)) := by
  intro claimed
  have bad := claimed.2.2 (L0 EB,input)
  rcases bad with timeout | equal
  · cases timeout.1
  · cases equal

end Solidity.Source.FailureExecution.PlannedApprox.Controls

/-- info: 'Solidity.Source.FailureExecution.PlannedApprox.approxAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedApprox.approxAt

/-- info: 'Solidity.Source.FailureExecution.runTxWithPlan_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.runTxWithPlan_approx

/-- info: 'Solidity.Source.FailureExecution.runTxWithPlan_events_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.runTxWithPlan_events_mono

/-- info: 'Solidity.Source.FailureExecution.PlannedApprox.Controls.root_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedApprox.Controls.root_prefix

/-- info: 'Solidity.Source.FailureExecution.PlannedApprox.Controls.timeout_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedApprox.Controls.timeout_prefix

/-- info: 'Solidity.Source.FailureExecution.PlannedApprox.Controls.completed_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedApprox.Controls.completed_cut

/-- info: 'Solidity.Source.FailureExecution.PlannedApprox.Controls.changed_plan_not_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedApprox.Controls.changed_plan_not_prefix

/-- info: 'Solidity.Source.FailureExecution.PlannedApprox.Controls.captured_timeout_not_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedApprox.Controls.captured_timeout_not_approx
