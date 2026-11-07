import Solidity.Backend.StorageOps.TargetDefaultInit
import Solidity.Backend.StorageOps.ProducerInterfaceControls

/-! Simultaneous inputs for target write-sequence laws. The nonempty sequence
writes two roots and then overwrites the first. No schema/Source lowering,
physical hashing, gas, fork or world adequacy follows from these fixtures. -/
namespace H62.StorageAudit.TargetWriteSequenceWitnesses
open Solidity Solidity.Backend.StorageOps Solidity.Storage.Representation

def word (n : Fin 256) : Semantics.Word :=
  ⟨n.val, by have bound := n.isLt; simp only [PrimTy.inRange, decide_eq_true_eq]; omega⟩
def updates : List (Storage.Loc × Semantics.Word) :=
  [(.root 0, word 7), (.root 1, word 23), (.root 0, word 0)]
def locations : List Storage.Loc := [.root 0, .root 1]
def captured : Store := fun loc => if loc = .root 0 then word 71 else word 99
def machine : Evm.Machine := {ProducerInterfaceControls.before with
  store := .ofFn fun slot => if slot = .root 0 then 71 else 99}

theorem run_joint : ∀ op ∈ updates, TargetOperations.KeysFit op.1 := by
  intro op member
  simp only [updates, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> exact True.intro

theorem context_joint : ∀ op ∈ updates, TargetOperations.KeysFit op.1 := run_joint

theorem agreement_joint :
    (∀ op ∈ updates, TargetOperations.KeysFit op.1) ∧
    ∃ fitting : ∀ loc ∈ locations, TargetOperations.KeysFit loc,
      ∀ loc (member : loc ∈ locations),
        machine.store.cells (TargetOperations.toSlot loc (fitting loc member)) =
          TargetOperations.encodeWord (captured loc) := by
  refine ⟨run_joint, ?_⟩
  have fitting : ∀ loc ∈ locations, TargetOperations.KeysFit loc := by
    intro loc member
    simp only [locations, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact True.intro
  refine ⟨fitting, ?_⟩
  intro loc member
  simp only [locations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem outside_joint :
    (∀ op ∈ updates, TargetOperations.KeysFit op.1) ∧
    ∀ op (member : op ∈ updates),
      (Evm.Slot.root 9) ≠ TargetOperations.toSlot op.1 (run_joint op member) := by
  refine ⟨run_joint, ?_⟩
  intro op member
  simp only [updates, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp only [TargetOperations.toSlot] <;> decide

def after : Evm.Machine := TargetDefaultInit.afterWrites updates run_joint machine

theorem actual : Evm.run (TargetDefaultInit.writeProgram updates run_joint) machine =
    .ok after 0 := TargetDefaultInit.run_writes updates run_joint machine

theorem context_actual : {after with store := machine.store} = machine :=
  TargetDefaultInit.context_writes updates run_joint machine

theorem agreement_actual :
    ∀ loc (member : loc ∈ locations),
      after.store.cells (TargetOperations.toSlot loc (agreement_joint.2.choose loc member)) =
        TargetOperations.encodeWord
          ((updates.foldl (fun store op => write store op.1 op.2) captured) loc) :=
  TargetDefaultInit.agreement_writes updates run_joint captured machine locations
    agreement_joint.2.choose agreement_joint.2.choose_spec

theorem outside_actual : after.store (.root 9) = machine.store (.root 9) :=
  TargetDefaultInit.outside_writes updates run_joint machine (.root 9) outside_joint.2

theorem ordered_observations :
    (machine.store (.root 0), machine.store (.root 1), after.store (.root 0),
      after.store (.root 1), after.store (.root 9)) = (71, 99, 0, 23, 99) := rfl

theorem omitted_overwrite_changes :
    (TargetDefaultInit.afterWrites (updates.take 2)
      (by intro op member; exact run_joint op (List.mem_of_mem_take member)) machine).store (.root 0) ≠
        after.store (.root 0) := by decide

theorem reject_mismatch : Evm.run [.revert] machine ≠
    Evm.run (TargetDefaultInit.writeProgram updates run_joint) machine := by
  rw [actual]
  intro same
  cases same

/-- info: 'H62.StorageAudit.TargetWriteSequenceWitnesses.run_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_joint
/-- info: 'H62.StorageAudit.TargetWriteSequenceWitnesses.context_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms context_joint
/-- info: 'H62.StorageAudit.TargetWriteSequenceWitnesses.agreement_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms agreement_joint
/-- info: 'H62.StorageAudit.TargetWriteSequenceWitnesses.outside_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outside_joint
/-- info: 'H62.StorageAudit.TargetWriteSequenceWitnesses.actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual
/-- info: 'H62.StorageAudit.TargetWriteSequenceWitnesses.context_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms context_actual
/-- info: 'H62.StorageAudit.TargetWriteSequenceWitnesses.agreement_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms agreement_actual
/-- info: 'H62.StorageAudit.TargetWriteSequenceWitnesses.outside_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outside_actual
/-- info: 'H62.StorageAudit.TargetWriteSequenceWitnesses.ordered_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ordered_observations
/-- info: 'H62.StorageAudit.TargetWriteSequenceWitnesses.omitted_overwrite_changes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms omitted_overwrite_changes
/-- info: 'H62.StorageAudit.TargetWriteSequenceWitnesses.reject_mismatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reject_mismatch

end H62.StorageAudit.TargetWriteSequenceWitnesses
