import Solidity.Source.FailureRequestHorizon
import Solidity.Source.FailureMachineControls

/-! Actual request-scope horizon controls with full caller state and bytes.
The exact post-fee Nat is a body argument, not installed money or a receipt. -/
namespace Solidity.Source.FailureExecution.RequestHorizonControls
open EM Controls

def points (cut : Option Nat) : Roadmap.Evm.FailurePoints :=
  constantRequestPlan (.runs (2^256) cut)

def body (cut : Option Nat) (balance : Nat) : EM E [.bytes .memory,.bool] (Nat × Roadmap.Bytes) := do
  Source.emitEvent event (some (points cut))
  pure (balance,[0xDE,0xAD])

def family (cut : Option Nat) : Nat → Nat → EM E [.bytes .memory,.bool] (Nat × Roadmap.Bytes)
  | 0, _ => halt .timeout
  | _+1, balance => body cut balance

theorem body_grow (cut : Option Nat) (balance : Nat) : Grow (body cut balance) := by
  unfold body
  grow_go [emit_plan_grow]

theorem family_step (cut : Option Nat) (horizon balance : Nat) :
    Approx (family cut horizon balance) (family cut (horizon+1) balance) := by
  cases horizon with
  | zero => exact Approx.timeout (body_grow cut balance)
  | succ n => exact Approx.refl (body_grow cut balance)

theorem actual_scope_step (cut : Option Nat) (horizon : Nat) :
    Approx (requestScope (points cut) (family cut horizon))
      (requestScope (points cut) (family cut (horizon+1))) :=
  requestScope_approx _ (family_step cut horizon)

def started : St E := { journalSeed with resource := requestFinished }
def finished : St E := { started with events := journalSeed.events ++ [event] }

theorem zero_horizon_full :
    (requestScope (points none) (family none 0)).run (caller,journalSeed) =
      (.error .timeout,(caller,started)) := by rfl

theorem completed_full :
    (requestScope (points none) (family none 1)).run (caller,journalSeed) =
      (.ok (some (2^256,[0xDE,0xAD])),(caller,finished)) := by rfl

theorem later_complete_full (horizon : Nat) :
    (requestScope (points none) (family none (horizon+1))).run (caller,journalSeed) =
      (.ok (some (2^256,[0xDE,0xAD])),(caller,finished)) := by rfl

theorem cut_zero_suppresses :
    (requestScope (points (some 0)) (family (some 0) 1)).run (caller,journalSeed) =
      (.error (.revert []),(caller,started)) := by rfl

theorem cut_one_full :
    (requestScope (points (some 1)) (family (some 1) 1)).run (caller,journalSeed) =
      (.error (.revert []),(caller,finished)) := by rfl

def swallowed (_balance : Nat) : EM E [.bytes .memory,.bool] Nat := do
  let _ ← attempt (Source.emitEvent event (some (points (some 1))))
  pure 7

theorem caught_cut_cannot_succeed :
    (requestScope (points (some 1)) swallowed).run (caller,journalSeed) =
      (.error (.revert []),(caller,finished)) := by rfl

theorem dropped_is_distinct :
    (requestScope (constantRequestPlan .dropped) (family none 1)).run (caller,journalSeed) =
      (.ok none,(caller,started)) := by rfl

theorem heap_alias_retained :
    (heapBytes 0 : EM E [.bytes .memory,.bool] Roadmap.Bytes).run (caller,finished) =
      (.ok [0xDE,0xAD],(caller,finished)) := by rfl

/-- Fixed plans are essential: successful completed scopes with different
post-fee inputs are distinct, even though both have no scheduled failures. -/
theorem changed_plan_not_approx :
    ¬ Approx
      (requestScope (constantRequestPlan (.runs 257 none)) (fun b => pure b) : EM E [.bytes .memory,.bool] (Option Nat))
      (requestScope (constantRequestPlan (.runs 258 none)) (fun b => pure b)) := by
  intro claim
  have difference := claim.2.2 (caller,journalSeed)
  cases difference with
  | inl timed => cases timed.1
  | inr equal => cases equal

end Solidity.Source.FailureExecution.RequestHorizonControls

/-- info: 'Solidity.Source.FailureExecution.RequestHorizonControls.body_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.RequestHorizonControls.body_grow
/-- info: 'Solidity.Source.FailureExecution.RequestHorizonControls.family_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.RequestHorizonControls.family_step
/-- info: 'Solidity.Source.FailureExecution.RequestHorizonControls.actual_scope_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.RequestHorizonControls.actual_scope_step
/-- info: 'Solidity.Source.FailureExecution.RequestHorizonControls.zero_horizon_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.RequestHorizonControls.zero_horizon_full
/-- info: 'Solidity.Source.FailureExecution.RequestHorizonControls.completed_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.RequestHorizonControls.completed_full
/-- info: 'Solidity.Source.FailureExecution.RequestHorizonControls.later_complete_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.RequestHorizonControls.later_complete_full
/-- info: 'Solidity.Source.FailureExecution.RequestHorizonControls.cut_zero_suppresses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.RequestHorizonControls.cut_zero_suppresses
/-- info: 'Solidity.Source.FailureExecution.RequestHorizonControls.cut_one_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.RequestHorizonControls.cut_one_full
/-- info: 'Solidity.Source.FailureExecution.RequestHorizonControls.caught_cut_cannot_succeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.RequestHorizonControls.caught_cut_cannot_succeed
/-- info: 'Solidity.Source.FailureExecution.RequestHorizonControls.dropped_is_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.RequestHorizonControls.dropped_is_distinct
/-- info: 'Solidity.Source.FailureExecution.RequestHorizonControls.heap_alias_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.RequestHorizonControls.heap_alias_retained
/-- info: 'Solidity.Source.FailureExecution.RequestHorizonControls.changed_plan_not_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.RequestHorizonControls.changed_plan_not_approx
