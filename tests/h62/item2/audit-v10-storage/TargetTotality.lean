import Solidity.Backend.StorageOps.ProducerInterfaceControls

/-! Totality and negative code generators at the existing symbolic-slot target.
No Source admission, physical expansion, EVM gas/fork or world rollback theorem. -/
namespace H62.StorageAudit.TargetTotality
open Solidity Solidity.Backend.StorageOps
open TargetOperations

def rejectAll (_ : Evm.Slot) : List Evm.Instr := [.revert]
def noopAll (_ : Evm.Slot) : List Evm.Instr := []

theorem read_totality (slot : Evm.Slot) (machine : Evm.Machine) :
    ∃ after, Evm.run (readCode slot) machine = .ok after 0 :=
  ⟨{machine with stack := .val (machine.store.cells slot) :: machine.stack}, run_read slot machine⟩

theorem write_totality (slot : Evm.Slot) (word : Semantics.Word) (machine : Evm.Machine) :
    ∃ after, Evm.run (writeCode slot word) machine = .ok after 0 :=
  ⟨{machine with store := Evm.WordStore.write machine.store slot (encodeWord word).val},
    run_write slot word machine⟩

theorem copy_totality (dst src : Evm.Slot) (machine : Evm.Machine) :
    ∃ after, Evm.run (copyCode dst src) machine = .ok after 0 :=
  ⟨{machine with store := Evm.WordStore.write machine.store dst (machine.store.cells src).val},
    run_copy dst src machine⟩

theorem reject_mismatch (slot : Evm.Slot) (machine : Evm.Machine) :
    Evm.run (rejectAll slot) machine ≠ Evm.run (readCode slot) machine := by
  rw [run_read]
  intro equal
  cases equal

theorem noop_mismatch (slot : Evm.Slot) (machine : Evm.Machine) :
    Evm.run (noopAll slot) machine ≠ Evm.run (readCode slot) machine := by
  rw [run_read]
  intro equal
  have sizes := congrArg (fun out : Evm.Out => match out with
    | .ok next _ => next.stack.length
    | _ => 0) equal
  change machine.stack.length = machine.stack.length + 1 at sizes
  omega

theorem reject_not_public : ¬ (∀ slot machine, Evm.run (rejectAll slot) machine =
    .ok {machine with stack := .val (machine.store.cells slot) :: machine.stack} 0) := by
  intro accepted
  exact reject_mismatch (.root 0) ProducerInterfaceControls.before
    ((accepted (.root 0) ProducerInterfaceControls.before).trans (run_read (.root 0) ProducerInterfaceControls.before).symm)

theorem noop_not_public : ¬ (∀ slot machine, Evm.run (noopAll slot) machine =
    .ok {machine with stack := .val (machine.store.cells slot) :: machine.stack} 0) := by
  intro accepted
  exact noop_mismatch (.root 0) ProducerInterfaceControls.before
    ((accepted (.root 0) ProducerInterfaceControls.before).trans (run_read (.root 0) ProducerInterfaceControls.before).symm)

theorem revert_skips_write (slot : Evm.Slot) (word : Semantics.Word) (machine : Evm.Machine) :
    Evm.run ([.revert] ++ writeCode slot word) machine = .revert := by rfl

theorem write_actual : Evm.run (writeCode (.root 0) ProducerInterfaceControls.word) ProducerInterfaceControls.before = .ok ProducerInterfaceControls.after 0 ∧
    ProducerInterfaceControls.before.store (.root 0) = 0 ∧ ProducerInterfaceControls.after.store (.root 0) = 1 := by
  exact ⟨rfl, rfl, rfl⟩

def copied : Evm.Machine := {ProducerInterfaceControls.after with store := Evm.WordStore.write ProducerInterfaceControls.after.store (.root 1) 1}

theorem copy_actual : Evm.run (copyCode (.root 1) (.root 0)) ProducerInterfaceControls.after = .ok copied 0 := by rfl

theorem copy_observations :
    (copied.store (.root 1), copied.store (.root 0), copied.stack, copied.mem 0,
     copied.self, copied.caller, copied.timestamp) =
    (1, 1, ProducerInterfaceControls.after.stack, ProducerInterfaceControls.after.mem 0, ProducerInterfaceControls.after.self, ProducerInterfaceControls.after.caller, ProducerInterfaceControls.after.timestamp) := by rfl

theorem noop_write_diff : Evm.run [] ProducerInterfaceControls.before ≠ Evm.run (writeCode (.root 0) ProducerInterfaceControls.word) ProducerInterfaceControls.before := by
  rw [run_write]
  intro equal
  have cells := congrArg (fun out : Evm.Out => match out with
    | .ok next _ => next.store (.root 0)
    | _ => 0) equal
  change (0 : Nat) = 1 at cells
  cases cells

/-- info: 'H62.StorageAudit.TargetTotality.read_totality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms read_totality
/-- info: 'H62.StorageAudit.TargetTotality.write_totality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms write_totality
/-- info: 'H62.StorageAudit.TargetTotality.copy_totality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms copy_totality
/-- info: 'H62.StorageAudit.TargetTotality.reject_mismatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reject_mismatch
/-- info: 'H62.StorageAudit.TargetTotality.noop_mismatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms noop_mismatch
/-- info: 'H62.StorageAudit.TargetTotality.reject_not_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reject_not_public
/-- info: 'H62.StorageAudit.TargetTotality.noop_not_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms noop_not_public
/-- info: 'H62.StorageAudit.TargetTotality.revert_skips_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revert_skips_write
/-- info: 'H62.StorageAudit.TargetTotality.write_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms write_actual
/-- info: 'H62.StorageAudit.TargetTotality.copy_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms copy_actual
/-- info: 'H62.StorageAudit.TargetTotality.copy_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms copy_observations
/-- info: 'H62.StorageAudit.TargetTotality.noop_write_diff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms noop_write_diff
end H62.StorageAudit.TargetTotality
