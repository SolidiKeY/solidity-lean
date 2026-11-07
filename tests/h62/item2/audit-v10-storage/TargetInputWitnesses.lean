import Solidity.Backend.StorageOps.ProducerInterfaceControls

/-! Data-input inhabitance for five frozen target laws with no logical hypotheses.
These are not compiler success/totality certificates or joint logical-premise bundles. -/
namespace H62.StorageAudit.TargetInputWitnesses
open Solidity Solidity.Backend.StorageOps

theorem slot_input : Nonempty Evm.Slot := by
  exact ⟨.root 0⟩

theorem read_inputs : Nonempty (Evm.Slot × Evm.Machine) := by
  exact ⟨(.root 0, ProducerInterfaceControls.after)⟩

theorem write_inputs : Nonempty (Evm.Slot × Semantics.Word × Evm.Machine) := by
  exact ⟨(.root 0, ProducerInterfaceControls.word, ProducerInterfaceControls.after)⟩

theorem copy_inputs : Nonempty (Evm.Slot × Evm.Slot × Evm.Machine) := by
  exact ⟨(.root 0, .root 1, ProducerInterfaceControls.after)⟩

theorem self_copy_inputs : Nonempty (Evm.Slot × Evm.Machine) := by
  exact read_inputs

/-- info: 'H62.StorageAudit.TargetInputWitnesses.slot_input' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms slot_input
/-- info: 'H62.StorageAudit.TargetInputWitnesses.read_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms read_inputs
/-- info: 'H62.StorageAudit.TargetInputWitnesses.write_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms write_inputs
/-- info: 'H62.StorageAudit.TargetInputWitnesses.copy_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms copy_inputs
/-- info: 'H62.StorageAudit.TargetInputWitnesses.self_copy_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms self_copy_inputs
end H62.StorageAudit.TargetInputWitnesses
