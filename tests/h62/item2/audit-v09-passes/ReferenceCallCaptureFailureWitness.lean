import Solidity.Backend.Passes.ReferenceCallCaptureFailureControls

/-! Guard attributing a reached alias-read revert to the successful tuple call,
assuming a free capture slot was zeroed, or losing the paid allocation and tail.
Keep the actual successful prefix map; never invent a post-failure machine. -/
namespace Solidity.Backend.Passes.AuditReferenceCallCaptureFailure
open Evm Evm.Memory Evm.Compiler
open Solidity.Backend.Passes
open Solidity.Backend.InternalFlow.RuntimeFrame

theorem joint :
    InterfaceV1.Entry (V3CallProducerRef.plan V3CallProducerRef.Tuple.Controls.selected 16 16)
      1 1 64 V3CallProducerRef.Tuple.Controls.F ReferenceCallReadback.Controls.caller
      ReferenceCallReadback.Controls.bases ReferenceCallReadback.Controls.initial 20 ∧
    InterfaceV1.NoAliasPromotion V3CallProducerRef.Tuple.Controls.F
      V3CallProducerRef.Tuple.Controls.selected.checked.frag V3CallProducerRef.Tuple.Controls.scope ∧
    V3CallProducerRef.Tuple.Controls.call.run ReferenceCallReadback.Controls.caller =
      .ok ReferenceCallReadback.Controls.output ∧
    ReferenceCallReadback.FailureControls.bad.evalT ReferenceCallReadback.Controls.output.st = .error .revert ∧
    (∃ addresses,
      StateRepr 1 1 64 V3CallProducerRef.Tuple.Controls.selected.checked.frag
        ReferenceCallReadback.Controls.output.st addresses ReferenceCallReadback.Controls.returned ∧
      BaseExtends ReferenceCallReadback.Controls.caller.H ReferenceCallReadback.Controls.bases addresses ∧
      GrowsAllocator 1 64 1 ReferenceCallReadback.Controls.caller ReferenceCallReadback.Controls.bases
        ReferenceCallReadback.Controls.initial ReferenceCallReadback.Controls.output.st
        addresses ReferenceCallReadback.Controls.returned ∧
      ReferenceCallReadback.Controls.returned.mem 16 = w[20] ∧
      Footprint.Words 16 20 ReferenceCallReadback.Controls.initial ReferenceCallReadback.Controls.returned ∧
      ReferenceCallReadback.FailureControls.capture.Input 1 64 addresses
        ReferenceCallReadback.Controls.output.st (appendTail ReferenceCallReadback.Controls.returned [])) := by
  refine ⟨V3CallProducerRef.Tuple.Controls.entered (wmod 0), V3CallProducerRef.Tuple.Controls.flags,
    ReferenceCallReadback.Controls.source_run, ReferenceCallReadback.FailureControls.bad_source, ?_⟩
  obtain ⟨addresses, represented, extension, growth, cursor, words, tails⟩ :=
    ReferenceCallReadback.FailureControls.reached
  exact ⟨addresses, represented, extension, growth, cursor, words, (tails []).1⟩
def bad_source := @Solidity.Backend.Passes.ReferenceCallReadback.FailureControls.bad_source
def reached := @Solidity.Backend.Passes.ReferenceCallReadback.FailureControls.reached
def joined_failure := @Solidity.Backend.Passes.ReferenceCallReadback.FailureControls.joined_failure
def returned_observations := @Solidity.Backend.Passes.ReferenceCallReadback.FailureControls.returned_observations
def wrong_zero_capture_cell := @Solidity.Backend.Passes.ReferenceCallReadback.FailureControls.wrong_zero_capture_cell
def wrong_failure_stage := @Solidity.Backend.Passes.ReferenceCallReadback.FailureControls.wrong_failure_stage

/-- info: 'Solidity.Backend.Passes.AuditReferenceCallCaptureFailure.joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReferenceCallCaptureFailure.joint

/-- info: 'Solidity.Backend.Passes.AuditReferenceCallCaptureFailure.bad_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReferenceCallCaptureFailure.bad_source

/-- info: 'Solidity.Backend.Passes.AuditReferenceCallCaptureFailure.reached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReferenceCallCaptureFailure.reached

/-- info: 'Solidity.Backend.Passes.AuditReferenceCallCaptureFailure.joined_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReferenceCallCaptureFailure.joined_failure

/-- info: 'Solidity.Backend.Passes.AuditReferenceCallCaptureFailure.returned_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReferenceCallCaptureFailure.returned_observations

/-- info: 'Solidity.Backend.Passes.AuditReferenceCallCaptureFailure.wrong_zero_capture_cell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReferenceCallCaptureFailure.wrong_zero_capture_cell

/-- info: 'Solidity.Backend.Passes.AuditReferenceCallCaptureFailure.wrong_failure_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReferenceCallCaptureFailure.wrong_failure_stage
end Solidity.Backend.Passes.AuditReferenceCallCaptureFailure
