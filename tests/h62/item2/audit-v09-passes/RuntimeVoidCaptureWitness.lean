import Solidity.Backend.Passes.RuntimeVoidCaptureControls

/-! Guard capturing the old heap value before a void call mutates it, vacuous
runtime admission, and loss of live aliases or saved tails. Reuse the actual
void-call entry and reached map; do not assign body failure a consumer output. -/
namespace Solidity.Backend.Passes.AuditRuntimeVoidCapture
open Evm Evm.Memory
open Solidity.Backend.Passes
open Solidity.Backend.InternalFlow.RuntimeFrame
open V3FixedThunkProducer.Witness

theorem joint :
    domain 1 16 caller0 P.base machine0 10 ∧
    domain 1 16 caller9 P.base machine9 10 ∧
    InterfaceV1.Entry (NoneProducer.plan selected 8 8) 1 0 16 F caller0 P.base machine0 10 ∧
    InterfaceV1.NoAliasPromotion F selected.checked.frag .refl ∧
    call.run caller0 = .ok ⟨reached,List.prefix_refl _⟩ ∧
    call.run caller9 = .error .revert ∧
    RuntimeVoidCapture.Controls.operand.evalT caller0 = .ok (P.uint 7 (by decide)) ∧
    RuntimeVoidCapture.Controls.operand.evalT reached = .ok (P.uint 37 (by decide)) ∧
    (∃ (mid : Machine) (addresses : Nat → Fin W),
      run (NoneProducer.plan selected 8 8).code machine0 = .ok mid 0 ∧
      StateRepr 1 0 16 selected.checked.frag reached addresses mid ∧
      BaseExtends caller0.H P.base addresses ∧
      RuntimeVoidCapture.Controls.suffix.Input 1 16 addresses reached mid) := by
  refine ⟨member0, member9, RuntimeVoidCapture.Controls.entry,
    NoneProducer.init_flags selected.checked.frag .refl, source0, source9,
    RuntimeVoidCapture.Controls.evaluated_before, RuntimeVoidCapture.Controls.evaluated, ?_⟩
  obtain ⟨_, mid, addresses, word, final, _, callRun, represented, _, extension,
    _, _, _, suffixInput, _⟩ := RuntimeVoidCapture.Controls.instantiated
  exact ⟨mid, addresses, callRun, represented, extension, suffixInput⟩
def evaluated := @Solidity.Backend.Passes.RuntimeVoidCapture.Controls.evaluated
def evaluated_before := @Solidity.Backend.Passes.RuntimeVoidCapture.Controls.evaluated_before
def ordered := @Solidity.Backend.Passes.RuntimeVoidCapture.Controls.ordered
def failure := @Solidity.Backend.Passes.RuntimeVoidCapture.Controls.failure
def failure_source := @Solidity.Backend.Passes.RuntimeVoidCapture.Controls.failure_source
def failure_tail := @Solidity.Backend.Passes.RuntimeVoidCapture.Controls.failure_tail
def fragment := @Solidity.Backend.Passes.RuntimeVoidCapture.Controls.fragment
def premature_capture := @Solidity.Backend.Passes.RuntimeVoidCapture.Controls.premature_capture
def stale_capture_refused := @Solidity.Backend.Passes.RuntimeVoidCapture.Controls.stale_capture_refused
def corrupt_tail_refused := @Solidity.Backend.Passes.RuntimeVoidCapture.Controls.corrupt_tail_refused
def insufficient_private_frame := @Solidity.Backend.Passes.RuntimeVoidCapture.Controls.insufficient_private_frame

/-- info: 'Solidity.Backend.Passes.AuditRuntimeVoidCapture.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditRuntimeVoidCapture.joint

/-- info: 'Solidity.Backend.Passes.AuditRuntimeVoidCapture.evaluated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditRuntimeVoidCapture.evaluated

/-- info: 'Solidity.Backend.Passes.AuditRuntimeVoidCapture.evaluated_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditRuntimeVoidCapture.evaluated_before

/-- info: 'Solidity.Backend.Passes.AuditRuntimeVoidCapture.ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditRuntimeVoidCapture.ordered

/-- info: 'Solidity.Backend.Passes.AuditRuntimeVoidCapture.failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditRuntimeVoidCapture.failure

/-- info: 'Solidity.Backend.Passes.AuditRuntimeVoidCapture.failure_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditRuntimeVoidCapture.failure_source

/-- info: 'Solidity.Backend.Passes.AuditRuntimeVoidCapture.failure_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditRuntimeVoidCapture.failure_tail

/-- info: 'Solidity.Backend.Passes.AuditRuntimeVoidCapture.fragment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditRuntimeVoidCapture.fragment

/-- info: 'Solidity.Backend.Passes.AuditRuntimeVoidCapture.premature_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditRuntimeVoidCapture.premature_capture

/-- info: 'Solidity.Backend.Passes.AuditRuntimeVoidCapture.stale_capture_refused' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditRuntimeVoidCapture.stale_capture_refused

/-- info: 'Solidity.Backend.Passes.AuditRuntimeVoidCapture.corrupt_tail_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditRuntimeVoidCapture.corrupt_tail_refused

/-- info: 'Solidity.Backend.Passes.AuditRuntimeVoidCapture.insufficient_private_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditRuntimeVoidCapture.insufficient_private_frame
end Solidity.Backend.Passes.AuditRuntimeVoidCapture
