import Solidity.Source.FailureMachineControls
import Solidity.Source.FailureEventLaws

/-! Independently fixed complete states for actual Source.emitEvent, with
nonempty caller journal/event prefix and byte-memory alias. No native/EVM
comparison, rollback or recursive plan-threading claim. -/
namespace Solidity.Source.FailureExecution.EventControls
open Controls
def input : St E := { journalSeed with resource := Cursor.empty.enterFrame ownPlan }
def actual := (Source.emitEvent event (some ownPlan)).run (caller,input)
def expected : St E := { journalSeed with events := [prefixEvent,event], resource :=
  ⟨0,1,none,[⟨⟨0,by decide⟩,some 1,1⟩],some (.frame ⟨0,by decide⟩)⟩ }
def disabled := (Source.emitEvent event none).run (caller,input)
def disabledExpected : St E := { input with events := [prefixEvent,event] }
theorem enabled_complete : actual = (.error (.revert []),(caller,expected)) := by rfl
theorem disabled_complete : disabled = (.ok (),(caller,disabledExpected)) := by rfl
theorem no_false_success : actual.1 ≠ .ok () := by
  simp only [ne_eq, enabled_complete, reduceCtorEq, not_false_eq_true]
theorem owner_complete : actual.2.2.resource.pending.map (fun owner => owner.isFrame 0) = some true := by rfl
theorem caller_prefix_required : actual.2.2.events.length ≠ 1 := by decide
theorem caller_nonce_retained : (actual.2.2.ex.world.accounts ⟨3,by decide⟩).nonce = 5 := by rfl
theorem heap_alias_readback : (heapBytes 0 : EM E [.bytes .memory,.bool] Roadmap.Bytes).run actual.2 =
    (.ok [0xDE,0xAD],actual.2) := by rfl
/- BEGIN GENERATED EVENT PINS -/
/-- info: 'Solidity.Source.FailureExecution.EventControls.enabled_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.EventControls.enabled_complete
/-- info: 'Solidity.Source.FailureExecution.EventControls.disabled_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.EventControls.disabled_complete
/-- info: 'Solidity.Source.FailureExecution.EventControls.no_false_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.EventControls.no_false_success
/-- info: 'Solidity.Source.FailureExecution.EventControls.owner_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.EventControls.owner_complete
/-- info: 'Solidity.Source.FailureExecution.EventControls.caller_prefix_required' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.EventControls.caller_prefix_required
/-- info: 'Solidity.Source.FailureExecution.EventControls.caller_nonce_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.EventControls.caller_nonce_retained
/-- info: 'Solidity.Source.FailureExecution.EventControls.heap_alias_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.EventControls.heap_alias_readback
/- END GENERATED EVENT PINS -/

end Solidity.Source.FailureExecution.EventControls
