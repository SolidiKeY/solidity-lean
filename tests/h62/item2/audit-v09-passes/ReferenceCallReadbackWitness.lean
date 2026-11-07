import Solidity.Backend.Passes.ReferenceCallReadbackControls

/-! Guard vacuous tuple-reference return admission, stale caller address maps,
wrong recapture cells, and erasure of saved-tail or live-memory observations.
Use the actual runtime-frame entry, alias flags and reached suffix Input. -/
namespace Solidity.Backend.Passes.AuditReferenceCallReadback
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
    ReferenceCallReadback.Controls.value.evalT ReferenceCallReadback.Controls.output.st =
      .ok (indexValue (wmod 7)) ∧
    (∃ addresses,
      StateRepr 1 1 64 V3CallProducerRef.Tuple.Controls.selected.checked.frag
        ReferenceCallReadback.Controls.output.st addresses ReferenceCallReadback.Controls.returned ∧
      BaseExtends ReferenceCallReadback.Controls.caller.H ReferenceCallReadback.Controls.bases addresses ∧
      ReferenceCallReadback.Controls.suffix.Input 1 64 addresses
        ReferenceCallReadback.Controls.output.st (appendTail ReferenceCallReadback.Controls.returned [])) := by
  refine ⟨V3CallProducerRef.Tuple.Controls.entered (wmod 0), V3CallProducerRef.Tuple.Controls.flags,
    ReferenceCallReadback.Controls.source_run, ReferenceCallReadback.Controls.evaluated, ?_⟩
  obtain ⟨addresses, represented, extension, tails⟩ := ReferenceCallReadback.Controls.reached
  exact ⟨addresses, represented, extension, (tails []).1⟩
def source_run := @Solidity.Backend.Passes.ReferenceCallReadback.Controls.source_run
def evaluated := @Solidity.Backend.Passes.ReferenceCallReadback.Controls.evaluated
def returned_run := @Solidity.Backend.Passes.ReferenceCallReadback.Controls.returned_run
def reached := @Solidity.Backend.Passes.ReferenceCallReadback.Controls.reached
def source_observations := @Solidity.Backend.Passes.ReferenceCallReadback.Controls.source_observations
def complete_observations := @Solidity.Backend.Passes.ReferenceCallReadback.Controls.complete_observations
def wrong_recapture := @Solidity.Backend.Passes.ReferenceCallReadback.Controls.wrong_recapture
def body_failure := @Solidity.Backend.Passes.ReferenceCallReadback.Controls.body_failure
def private_frame_refused := @Solidity.Backend.Passes.ReferenceCallReadback.Controls.private_frame_refused
def stale_map_refused := @Solidity.Backend.Passes.ReferenceCallReadback.Controls.stale_map_refused

/-- info: 'Solidity.Backend.Passes.AuditReferenceCallReadback.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReferenceCallReadback.joint

/-- info: 'Solidity.Backend.Passes.AuditReferenceCallReadback.source_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReferenceCallReadback.source_run

/-- info: 'Solidity.Backend.Passes.AuditReferenceCallReadback.evaluated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReferenceCallReadback.evaluated

/-- info: 'Solidity.Backend.Passes.AuditReferenceCallReadback.returned_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReferenceCallReadback.returned_run

/-- info: 'Solidity.Backend.Passes.AuditReferenceCallReadback.reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReferenceCallReadback.reached

/-- info: 'Solidity.Backend.Passes.AuditReferenceCallReadback.source_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReferenceCallReadback.source_observations

/-- info: 'Solidity.Backend.Passes.AuditReferenceCallReadback.complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReferenceCallReadback.complete_observations

/-- info: 'Solidity.Backend.Passes.AuditReferenceCallReadback.wrong_recapture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReferenceCallReadback.wrong_recapture

/-- info: 'Solidity.Backend.Passes.AuditReferenceCallReadback.body_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReferenceCallReadback.body_failure

/-- info: 'Solidity.Backend.Passes.AuditReferenceCallReadback.private_frame_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReferenceCallReadback.private_frame_refused

/-- info: 'Solidity.Backend.Passes.AuditReferenceCallReadback.stale_map_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReferenceCallReadback.stale_map_refused
end Solidity.Backend.Passes.AuditReferenceCallReadback
