import Solidity.Backend.Passes.RuntimeReturnCaptureControls

/-! Guard vacuous primitive-return capture admission, swapping capture before
its call, or assigning call failure to a reached consumer. Preserve actual
success/failure members and the correlated returned map before capture. -/
namespace Solidity.Backend.Passes.AuditRuntimeReturnCapture
open Evm Evm.Memory
open Solidity.Backend.Passes
open Solidity.Backend.InternalFlow.RuntimeFrame
open V3CallProducer.Controls

theorem joint :
    V3CallProducer.admitted selected 8 8 1 16 initial bases machine 10 ∧
    V3CallProducer.admitted selected 8 8 1 16 failing bases failedMachine 10 ∧
    InterfaceV1.NoAliasPromotion F selected.checked.frag .refl ∧
    call.run initial = .ok ⟨output,List.prefix_refl _⟩ ∧
    call.run failing = .error .revert ∧
    RuntimeReturnCapture.Controls.Fixture.operand.evalT output = .ok (uint 7 (by decide)) ∧
    (∃ (mid : Machine) (addresses : Nat → Fin W),
      run (V3CallProducer.plan selected 8 8).code machine = .ok mid 0 ∧
      StateRepr 1 0 16 selected.checked.frag output addresses mid ∧
      BaseExtends initial.H bases addresses ∧
      RuntimeReturnCapture.Controls.Fixture.suffix.Input 1 16 addresses output mid) := by
  refine ⟨positive_member, negative_member, flags, source_success, source_revert,
    RuntimeReturnCapture.Controls.Fixture.evaluated, ?_⟩
  obtain ⟨_, mid, addresses, word, final, _, callRun, represented, _, extension,
    _, _, _, suffixInput, _⟩ := RuntimeReturnCapture.Controls.Fixture.instantiated
  exact ⟨mid, addresses, callRun, represented, extension, suffixInput⟩
def evaluated := @Solidity.Backend.Passes.RuntimeReturnCapture.Controls.Fixture.evaluated
def ordered := @Solidity.Backend.Passes.RuntimeReturnCapture.Controls.Fixture.ordered
def failure := @Solidity.Backend.Passes.RuntimeReturnCapture.Controls.Fixture.failure
def failure_source := @Solidity.Backend.Passes.RuntimeReturnCapture.Controls.Fixture.failure_source
def failure_tail := @Solidity.Backend.Passes.RuntimeReturnCapture.Controls.Fixture.failure_tail
def suffix_instructions := @Solidity.Backend.Passes.RuntimeReturnCapture.Controls.Fixture.suffix_instructions
def wrong_order := @Solidity.Backend.Passes.RuntimeReturnCapture.Controls.Fixture.wrong_order
def wrong_capture := @Solidity.Backend.Passes.RuntimeReturnCapture.Controls.Fixture.wrong_capture
def wrong_tail := @Solidity.Backend.Passes.RuntimeReturnCapture.Controls.Fixture.wrong_tail
def insufficient_private_frame := @Solidity.Backend.Passes.RuntimeReturnCapture.Controls.Fixture.insufficient_private_frame

/-- info: 'Solidity.Backend.Passes.AuditRuntimeReturnCapture.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditRuntimeReturnCapture.joint

/-- info: 'Solidity.Backend.Passes.AuditRuntimeReturnCapture.evaluated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditRuntimeReturnCapture.evaluated

/-- info: 'Solidity.Backend.Passes.AuditRuntimeReturnCapture.ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditRuntimeReturnCapture.ordered

/-- info: 'Solidity.Backend.Passes.AuditRuntimeReturnCapture.failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditRuntimeReturnCapture.failure

/-- info: 'Solidity.Backend.Passes.AuditRuntimeReturnCapture.failure_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditRuntimeReturnCapture.failure_source

/-- info: 'Solidity.Backend.Passes.AuditRuntimeReturnCapture.failure_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditRuntimeReturnCapture.failure_tail

/-- info: 'Solidity.Backend.Passes.AuditRuntimeReturnCapture.suffix_instructions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditRuntimeReturnCapture.suffix_instructions

/-- info: 'Solidity.Backend.Passes.AuditRuntimeReturnCapture.wrong_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditRuntimeReturnCapture.wrong_order

/-- info: 'Solidity.Backend.Passes.AuditRuntimeReturnCapture.wrong_capture' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditRuntimeReturnCapture.wrong_capture

/-- info: 'Solidity.Backend.Passes.AuditRuntimeReturnCapture.wrong_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditRuntimeReturnCapture.wrong_tail

/-- info: 'Solidity.Backend.Passes.AuditRuntimeReturnCapture.insufficient_private_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditRuntimeReturnCapture.insufficient_private_frame
end Solidity.Backend.Passes.AuditRuntimeReturnCapture
