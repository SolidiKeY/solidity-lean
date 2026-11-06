import Solidity.Source.FailureTransactionStability
import Solidity.Source.FailureTransactionControls

/-! Full-state completed-horizon transport of independently frozen Source
fixtures. No fresh native observations or cross-plan equality is claimed. -/
namespace Solidity.Source.FailureExecution.StabilityControls
open EM SemanticsExamples
open RuntimeControls (input glob data points)
open TransactionControls (receipt finalized)

theorem revert_stable (pipeline : Roadmap.Pipeline) (later : Nat) (more : 20 ≤ later) :
    (runTxWithPlan (glob pipeline) later (tx data) (points (some 1))).run (L0 EB,input) =
      (.ok (.revert []),(.nil,finalized [RuntimeControls.priorEvent,
        RuntimeControls.callEvent,receipt (.revert [])])) := by
  have done : ((runTxWithPlan (glob pipeline) 20 (tx data) (points (some 1))).run (L0 EB,input)).1 ≠ .error .timeout := by
    change (TransactionControls.run pipeline (some 1)).1 ≠ .error .timeout
    rw [TransactionControls.own_cut1_full_state]
    intro impossible
    cases impossible
  rw [runTxWithPlan_stable _ _ _ _ _ more done]
  exact TransactionControls.own_cut1_full_state pipeline

theorem stuck_stable (pipeline : Roadmap.Pipeline) (later : Nat) (more : 20 ≤ later) :
    (runTxWithPlan (RuntimeControls.wrongFrameGlob pipeline) later (tx data) (points none)).run
      (L0 EB,input) = (.error (.stuck "call frame"),(.nil,TransactionControls.stuckExpected)) := by
  have done : ((runTxWithPlan (RuntimeControls.wrongFrameGlob pipeline) 20 (tx data) (points none)).run
      (L0 EB,input)).1 ≠ .error .timeout := by
    change (TransactionControls.stuckRun pipeline).1 ≠ .error .timeout
    rw [TransactionControls.stuck_full_state]
    intro impossible
    cases impossible
  rw [runTxWithPlan_stable _ _ _ _ _ more done]
  exact TransactionControls.stuck_full_state pipeline

theorem panic_bytes_stable (pipeline : Roadmap.Pipeline) (later : Nat) (more : 20 ≤ later) :
    (runTxWithPlan (RuntimeControls.panicGlob pipeline) later (tx (selOf "cb()")) (points none)).run
      (L0 EB,input) = (.ok (.revert RuntimeControls.panicBytes),
        (.nil,finalized [RuntimeControls.priorEvent,TransactionControls.panicReceipt])) := by
  have done : ((runTxWithPlan (RuntimeControls.panicGlob pipeline) 20 (tx (selOf "cb()")) (points none)).run
      (L0 EB,input)).1 ≠ .error .timeout := by
    change (TransactionControls.panicRun pipeline).1 ≠ .error .timeout
    rw [TransactionControls.panic_full_state]
    intro impossible
    cases impossible
  rw [runTxWithPlan_stable _ _ _ _ _ more done]
  exact TransactionControls.panic_full_state pipeline

/-- A reached request stop remains exceptional; no receipt is invented. -/
theorem request_stop_stable (pipeline : Roadmap.Pipeline) (later : Nat) (more : 20 ≤ later) :
    (runTxWithPlan (glob pipeline) later (tx data) TransactionControls.entryPoints).run
      (L0 EB,TransactionControls.entryInput) =
      (.error (.revert []),(.nil,TransactionControls.entryExpected)) := by
  have done : ((runTxWithPlan (glob pipeline) 20 (tx data) TransactionControls.entryPoints).run
      (L0 EB,TransactionControls.entryInput)).1 ≠ .error .timeout := by
    change (TransactionControls.entryRun pipeline).1 ≠ .error .timeout
    rw [TransactionControls.entry_stop_full_state]
    intro impossible
    cases impossible
  rw [runTxWithPlan_stable _ _ _ _ _ more done]
  exact TransactionControls.entry_stop_full_state pipeline

/-- Removing the completed-result premise would equate a real timeout with
an actually completed root. This control retains the original horizons. -/
theorem timeout_not_equal_completed (pipeline : Roadmap.Pipeline) :
    (TransactionControls.run pipeline none 0).1 ≠ (TransactionControls.run pipeline none 20).1 := by
  have zero := TransactionControls.zero_horizon pipeline
  have complete := TransactionControls.uncut pipeline
  rw [zero.1, complete.1]
  intro impossible
  cases impossible

/-- Catching timeout turns it into a normal result; blanket Below.attempt
transport is invalid even on an inhabited caller state. -/
theorem attempt_not_below :
    ¬ Below (attempt (halt .timeout : EM EB [] Nat)) (attempt (pure 7)) := by
  intro claimed
  have bad := claimed (L0 EB,input)
  cases bad with
  | inl timeout => cases timeout
  | inr equal => cases equal

end Solidity.Source.FailureExecution.StabilityControls

/-- info: 'Solidity.Source.FailureExecution.frame_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.frame_below
/-- info: 'Solidity.Source.FailureExecution.requestScope_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.requestScope_below
/-- info: 'Solidity.Source.FailureExecution.PlannedBelow.belowAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedBelow.belowAt
/-- info: 'Solidity.Source.FailureExecution.runTxWithPlan_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.runTxWithPlan_below
/-- info: 'Solidity.Source.FailureExecution.runTxWithPlan_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.runTxWithPlan_stable
/-- info: 'Solidity.Source.FailureExecution.StabilityControls.revert_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.StabilityControls.revert_stable
/-- info: 'Solidity.Source.FailureExecution.StabilityControls.stuck_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.StabilityControls.stuck_stable
/-- info: 'Solidity.Source.FailureExecution.StabilityControls.panic_bytes_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.StabilityControls.panic_bytes_stable
/-- info: 'Solidity.Source.FailureExecution.StabilityControls.request_stop_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.StabilityControls.request_stop_stable
/-- info: 'Solidity.Source.FailureExecution.StabilityControls.timeout_not_equal_completed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.StabilityControls.timeout_not_equal_completed
/-- info: 'Solidity.Source.FailureExecution.StabilityControls.attempt_not_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.StabilityControls.attempt_not_below
