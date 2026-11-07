import Solidity.Lowering.StorageOps.SourceWordReadControls

/-! Joint raw Source cell/word premise witnesses using the existing typed fixture.
No Source implementation, address compiler or world relation is supplied. -/
namespace H62.StorageAudit.SourceReadWitnesses
open Solidity Solidity.Backend.StorageOps Solidity.Lowering.StorageOps
open SourceWordWriteControls

def selected_value : Source.Val env.layout (env.cellTy left) := .int 11 (by decide)

theorem total_joint : env.transientRoot left = false := by
  rfl

theorem complete_joint : env.transientRoot left = false ∧
    (state.ex.world.accounts frame.this).storage.read left = some selected_value ∧
    selected_value.word = some (machine.store.cells (.root 0)) := by
  exact ⟨rfl, rfl, rfl⟩

/-- Reuse the published concrete certificate at the SAME inputs. -/
theorem complete_reused :
    (Source.readAt (E := env) (Γ := []) frame left (env.cellTy left)).run initial =
      (.ok selected_value, initial) ∧
    Evm.run (TargetOperations.readCode (.root 0)) machine =
      .ok { machine with stack := .val (machine.store.cells (.root 0)) :: machine.stack } 0 ∧
    selected_value.word = some (machine.store.cells (.root 0)) :=
  SourceWordReadControls.certificate

theorem readonly_read :
    (Source.readAt (E := env) (Γ := []) { frame with static := true } left (env.cellTy left)).run initial =
      (.ok selected_value, initial) := by
  rfl

theorem missing_read : env.transientRoot missing = false ∧
    (state.ex.world.accounts frame.this).storage.read missing = none ∧
    (Source.readAt (E := env) (Γ := []) frame missing (env.cellTy missing)).run initial =
      (.error (.stuck "storage cell without a value"), initial) := by
  exact ⟨rfl, rfl, rfl⟩

/-- Wrong-slot SLOAD still succeeds, but cannot satisfy this raw coherence premise. -/
theorem wrong_slot_coherence : selected_value.word ≠ some (machine.store.cells (.root 1)) := by
  decide

theorem wrong_slot_runs : Evm.run (TargetOperations.readCode (.root 1)) machine =
    .ok { machine with stack := .val (machine.store.cells (.root 1)) :: machine.stack } 0 :=
  TargetOperations.run_read _ _

theorem transient_is_not_ordinary : env.transientRoot scratch ≠ false := by
  decide

/-- info: 'H62.StorageAudit.SourceReadWitnesses.total_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms total_joint
/-- info: 'H62.StorageAudit.SourceReadWitnesses.complete_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms complete_joint
/-- info: 'H62.StorageAudit.SourceReadWitnesses.complete_reused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms complete_reused
/-- info: 'H62.StorageAudit.SourceReadWitnesses.readonly_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readonly_read
/-- info: 'H62.StorageAudit.SourceReadWitnesses.missing_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms missing_read
/-- info: 'H62.StorageAudit.SourceReadWitnesses.wrong_slot_coherence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_slot_coherence
/-- info: 'H62.StorageAudit.SourceReadWitnesses.wrong_slot_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_slot_runs
/-- info: 'H62.StorageAudit.SourceReadWitnesses.transient_is_not_ordinary' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms transient_is_not_ordinary
end H62.StorageAudit.SourceReadWitnesses
