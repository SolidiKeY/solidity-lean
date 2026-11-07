import Solidity.Backend.StorageOps.TargetRetainedCycle
import Solidity.Backend.StorageOps.ProducerInterfaceControls

/-! Joint reuse premises in the existing symbolic-slot target. Retained payload
is populated even though its child header is empty. No Source, physical-word,
gas/fork or world rollback adequacy is asserted. -/
namespace H62.StorageAudit.TargetReuseWitnesses
open Solidity Solidity.Backend.StorageOps

def base : Evm.Slot := .root 0
def child : Evm.Slot := .data base 1
def payload : Evm.Slot := .data child 0
def machine : Evm.Machine := {ProducerInterfaceControls.before with
  store := .ofFn fun slot => if slot = base then 1 else if slot = payload then 71
    else if slot = .root 9 then 99 else 0}

theorem after_joint : machine.store base + 1 < Evm.W ∧
    machine.store (.data base (machine.store base)) = 0 := by
  exact ⟨by decide, rfl⟩

theorem run_joint : machine.store base + 1 < Evm.W ∧
    machine.store (.data base (machine.store base)) = 0 := after_joint

theorem cycle_inputs : Nonempty (Evm.Machine × Evm.Slot) := ⟨(machine, base)⟩

theorem after_actual :
    TargetNestedPop.after (TargetHeaderPush.incremented base machine) base = machine :=
  TargetRetainedCycle.after_reuse machine base after_joint.1 after_joint.2

theorem run_actual : Evm.run (TargetRetainedCycle.code base) machine = .ok machine 0 :=
  TargetRetainedCycle.run_reuse machine base run_joint.1 run_joint.2

theorem observations :
    (machine.store base, machine.store child, machine.store payload, machine.store (.root 9),
      machine.stack, machine.mem 0, machine.self, machine.caller, machine.timestamp) =
    (1, 0, 71, 99, ProducerInterfaceControls.before.stack, ProducerInterfaceControls.before.mem 0,
      ProducerInterfaceControls.before.self, ProducerInterfaceControls.before.caller,
      ProducerInterfaceControls.before.timestamp) := rfl

theorem repeated_actual :
    Evm.run (TargetRetainedCycle.code base ++ TargetRetainedCycle.code base) machine = .ok machine 0 :=
  (Evm.run_append_ok run_actual).trans run_actual

def uncleared : Evm.Machine := {machine with store := Evm.WordStore.write machine.store child 1}
def unclearedAfter : Evm.Machine :=
  TargetNestedPop.after (TargetHeaderPush.incremented base uncleared) base

theorem uncleared_execution : Evm.run (TargetRetainedCycle.code base) uncleared = .ok unclearedAfter 0 := by
  unfold TargetRetainedCycle.code
  rw [Evm.run_append_ok (m' := TargetHeaderPush.incremented base uncleared)
    (by rw [TargetHeaderPush.run_current]; rfl), TargetNestedPop.run_current]
  rfl

theorem uncleared_changed : unclearedAfter ≠ uncleared := by
  intro equal
  have observed := congrArg (fun next : Evm.Machine => next.store payload) equal
  change (0 : Nat) = 71 at observed
  omega

def saturated : Evm.Machine := {machine with store := Evm.WordStore.write machine.store base (Evm.W-1)}
def empty : Evm.Machine := {machine with store := Evm.WordStore.write machine.store base 0}

theorem negative_axes : ¬ saturated.store base + 1 < Evm.W ∧
    uncleared.store child ≠ 0 ∧ machine.store payload = 71 := by
  exact ⟨by decide, by decide, rfl⟩

theorem saturated_reverts : Evm.run (TargetRetainedCycle.code base) saturated = .revert := by
  unfold TargetRetainedCycle.code
  apply Evm.run_append_revert
  rw [TargetHeaderPush.run_current]
  rfl

theorem cycle_actual : Evm.run (TargetRetainedCycle.popRegrowPop base) machine =
    .ok (TargetNestedPop.after machine base) 0 := by
  rw [TargetRetainedCycle.run_pop_regrow_pop]
  rfl

theorem cycle_observations :
    ((TargetNestedPop.after machine base).store base,
      (TargetNestedPop.after machine base).store payload,
      (TargetNestedPop.after machine base).store (.root 9), machine.store base) = (0, 71, 99, 1) := rfl

theorem empty_reverts : Evm.run (TargetRetainedCycle.popRegrowPop base) empty = .revert := by
  rw [TargetRetainedCycle.run_pop_regrow_pop]
  rfl


theorem reject_mismatch : Evm.run [.revert] machine ≠ Evm.run (TargetRetainedCycle.code base) machine := by
  rw [run_actual]
  intro equal
  cases equal

/-- info: 'H62.StorageAudit.TargetReuseWitnesses.after_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms after_joint

/-- info: 'H62.StorageAudit.TargetReuseWitnesses.run_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms run_joint

/-- info: 'H62.StorageAudit.TargetReuseWitnesses.cycle_inputs' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms cycle_inputs

/-- info: 'H62.StorageAudit.TargetReuseWitnesses.after_actual' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms after_actual

/-- info: 'H62.StorageAudit.TargetReuseWitnesses.run_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_actual

/-- info: 'H62.StorageAudit.TargetReuseWitnesses.observations' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms observations

/-- info: 'H62.StorageAudit.TargetReuseWitnesses.repeated_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms repeated_actual

/-- info: 'H62.StorageAudit.TargetReuseWitnesses.uncleared_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uncleared_execution

/-- info: 'H62.StorageAudit.TargetReuseWitnesses.uncleared_changed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uncleared_changed

/-- info: 'H62.StorageAudit.TargetReuseWitnesses.negative_axes' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms negative_axes

/-- info: 'H62.StorageAudit.TargetReuseWitnesses.saturated_reverts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms saturated_reverts

/-- info: 'H62.StorageAudit.TargetReuseWitnesses.cycle_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cycle_actual

/-- info: 'H62.StorageAudit.TargetReuseWitnesses.cycle_observations' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms cycle_observations

/-- info: 'H62.StorageAudit.TargetReuseWitnesses.empty_reverts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_reverts

/-- info: 'H62.StorageAudit.TargetReuseWitnesses.reject_mismatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reject_mismatch

end H62.StorageAudit.TargetReuseWitnesses
