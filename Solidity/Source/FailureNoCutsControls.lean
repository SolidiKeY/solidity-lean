import Solidity.Source.FailureNoCutsEffects
import Solidity.Source.FailureMachineControls

/-! Actual nested no-cut budgets, event ticks and full-state check controls.
No account-balance installation or whole NoFail evaluator is claimed. -/
namespace Solidity.Source.FailureExecution.NoCutsControls
open EM Controls

def points := FailureResources.noFailures (fun _ => 2^256)
theorem points_noFail : FailureResources.NoFail points :=
  FailureResources.noFailures_noFail _
def requested := (Cursor.empty.enterRequest points rfl).2
def nested := (requested.enterFrame points).enterFrame points

theorem requested_clear : requested.CutFree :=
  Cursor.cutFree_enterRequest points points_noFail _ Cursor.cutFree_empty rfl

theorem nested_clear : nested.CutFree :=
  Cursor.cutFree_enterFrame points points_noFail _
    (Cursor.cutFree_enterFrame points points_noFail _ requested_clear)

def state : St E := { journalSeed with resource := nested }

theorem checked :
    (check (some points) : EM E [.bytes .memory,.bool] Unit).run (caller,state) =
      (.ok (),(caller,state)) := check_cutFree _ _ _ nested_clear

def emitTwo : EM E [.bytes .memory,.bool] Unit := do
  check (some points)
  Source.emitEvent event (some points)
  Source.emitEvent event (some points)
  check (some points)

def after : St E := { state with
  events := journalSeed.events ++ [event,event]
  resource := ⟨1,2,some ⟨⟨0,by decide⟩,2^256,none,2⟩,
    [⟨⟨1,by decide⟩,none,2⟩,⟨⟨0,by decide⟩,none,2⟩],none⟩ }

theorem one_event_exact :
    (Source.emitEvent event (some points) : EM E [.bytes .memory,.bool] Unit).run
      (caller,state) = (.ok (),(caller,{ state with events := state.events ++ [event], resource := state.resource.advanceEvent })) :=
  emitEvent_cutFree _ _ _ _ nested_clear

theorem after_clear : after.resource.CutFree :=
  Cursor.cutFree_advanceEvent _ (Cursor.cutFree_advanceEvent _ nested_clear)

theorem emitted_full_state : emitTwo.run (caller,state) =
    (.ok (),(caller,after)) := by rfl

theorem retained_bytes : (heapBytes 0 : EM E [.bytes .memory,.bool] Roadmap.Bytes).run
    (caller,after) = (.ok [0xDE,0xAD],(caller,after)) := by rfl

-- Input NoFail is insufficient if the actual cursor was built from a cut plan.
def mismatched : St E := { journalSeed with resource := Cursor.empty.enterFrame zeroPlan }
def stopped : St E := { mismatched with resource :=
  { mismatched.resource with pending := some (.frame ⟨0,by decide⟩) } }

theorem mismatched_stop :
    (check (some points) : EM E [.bytes .memory,.bool] Unit).run (caller,mismatched) =
      (.error (.revert []),(caller,stopped)) := by rfl

theorem mismatched_not_clear : ¬ mismatched.resource.CutFree := by
  intro clear
  have bad := check_cutFree (some points) caller mismatched clear
  rw [mismatched_stop] at bad
  cases bad

theorem noFail_not_enough : ¬ (∀ (s : St E),
    (check (some points) : EM E [.bytes .memory,.bool] Unit).run (caller,s) =
      (.ok (),(caller,s))) := by
  intro wrong
  have bad := wrong mismatched
  rw [mismatched_stop] at bad
  cases bad

end Solidity.Source.FailureExecution.NoCutsControls

/-- info: 'Solidity.Source.FailureExecution.NoCutsControls.points_noFail' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.NoCutsControls.points_noFail

/-- info: 'Solidity.Source.FailureExecution.NoCutsControls.requested_clear' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.NoCutsControls.requested_clear

/-- info: 'Solidity.Source.FailureExecution.NoCutsControls.nested_clear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.NoCutsControls.nested_clear

/-- info: 'Solidity.Source.FailureExecution.NoCutsControls.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.NoCutsControls.checked

/-- info: 'Solidity.Source.FailureExecution.NoCutsControls.one_event_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.NoCutsControls.one_event_exact

/-- info: 'Solidity.Source.FailureExecution.NoCutsControls.after_clear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.NoCutsControls.after_clear

/-- info: 'Solidity.Source.FailureExecution.NoCutsControls.emitted_full_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.NoCutsControls.emitted_full_state

/-- info: 'Solidity.Source.FailureExecution.NoCutsControls.retained_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.NoCutsControls.retained_bytes

/-- info: 'Solidity.Source.FailureExecution.NoCutsControls.mismatched_stop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.NoCutsControls.mismatched_stop

/-- info: 'Solidity.Source.FailureExecution.NoCutsControls.mismatched_not_clear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.NoCutsControls.mismatched_not_clear

/-- info: 'Solidity.Source.FailureExecution.NoCutsControls.noFail_not_enough' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.NoCutsControls.noFail_not_enough
