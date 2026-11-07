import Solidity.Source.FailureFrameHorizon
import Solidity.Source.FailureMachineControls

/-! Inhabited full-state controls and the attempt/Approx refusal boundary. -/
namespace Solidity.Source.FailureExecution.FrameHorizonControls
open EM Controls

def emitSeven (plan : RuntimePlan) : EM E [.bytes .memory, .bool] Nat := do
  Source.emitEvent event plan
  pure 7

theorem emitSeven_grow (plan : RuntimePlan) : Grow (emitSeven plan) := by
  simp only [emitSeven]
  grow_go [emit_plan_grow]

theorem timeout_to_emit :
    Approx (frame (some childPlan) (halt .timeout))
      (frame (some childPlan) (emitSeven (some childPlan))) := by
  exact frame_approx _ (Approx.timeout (emitSeven_grow _))

theorem completed_state :
    (frame (some childPlan) (emitSeven (some childPlan))).run (caller,seed) =
      (.ok 7,(caller,ownExpected)) := by rfl

theorem timeout_state :
    (frame (some childPlan) (halt .timeout : EM E [.bytes .memory,.bool] Nat)).run
      (caller,seed) = (.error .timeout,(caller,startedExpected)) := by rfl

theorem caller_bytes :
    (heapBytes 0 : EM E [.bytes .memory,.bool] Roadmap.Bytes).run
      ((frame (some childPlan) (emitSeven (some childPlan))).run (caller,seed)).2 =
      (.ok [0xDE,0xAD],(caller,ownExpected)) := by rfl

-- A body ending in pure 7 cannot swallow the actual outer frame's event cut.
theorem outer_cut :
    (frame (some ownPlan) (emitSeven (some ownPlan))).run (caller,seed) =
      (.error (.revert []),(caller,ownExpected)) := by rfl

-- Concrete counterexample: captured timeout is an ordinary result, so a
-- blanket Approx.attempt rule would be unsound even on inhabited callers.
theorem attempt_not_approx :
    ¬ Approx (attempt (halt .timeout : EM E [.bytes .memory,.bool] Nat))
      (attempt (pure 7)) := by
  intro h
  have bad := h.2.2 (caller,seed)
  cases bad with
  | inl bad => cases bad.1
  | inr bad => cases bad

end Solidity.Source.FailureExecution.FrameHorizonControls

/-- info: 'Solidity.Source.FailureExecution.FrameHorizonControls.emitSeven_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.FrameHorizonControls.emitSeven_grow

/-- info: 'Solidity.Source.FailureExecution.FrameHorizonControls.timeout_to_emit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.FrameHorizonControls.timeout_to_emit

/-- info: 'Solidity.Source.FailureExecution.FrameHorizonControls.completed_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.FrameHorizonControls.completed_state

/-- info: 'Solidity.Source.FailureExecution.FrameHorizonControls.timeout_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.FrameHorizonControls.timeout_state

/-- info: 'Solidity.Source.FailureExecution.FrameHorizonControls.caller_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.FrameHorizonControls.caller_bytes

/-- info: 'Solidity.Source.FailureExecution.FrameHorizonControls.outer_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.FrameHorizonControls.outer_cut

/-- info: 'Solidity.Source.FailureExecution.FrameHorizonControls.attempt_not_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.FrameHorizonControls.attempt_not_approx
