import Solidity.Backend.StorageOps.TargetArrayWrite
import Solidity.Backend.StorageOps.CopyDemandControls
import Solidity.Backend.StorageOps.ProducerInterfaceControls

/-! Populated live-array access witnesses. Retained cells beyond the current
header are distinct from out-of-extent cells. Existing operation adapters and
symbolic-slot EVM execution are used; Source/physical/world adequacy is open. -/
namespace H62.StorageAudit.ArrayAccessWitnesses
open Solidity Solidity.Backend.StorageOps TypeGraph
open Solidity.Storage.Representation Solidity.Storage.Representation.Graph
abbrev graph := CopyDemandControls.graph
def zero : Index := ⟨0, by decide⟩
def one : Index := ⟨1, by decide⟩
def three : Index := ⟨3, by decide⟩
def old : Value graph (.array (.prim .bool)) :=
  .array ⟨3, by decide⟩ one (by decide) (fun _ => .present (.prim true))
def result : Value graph (.array (.prim .bool)) :=
  (TargetArrayWrite.writeAt old zero false).getD old
def machine : Evm.Machine := {ProducerInterfaceControls.before with
  store := .ofFn fun slot => if slot = .root 0 then 1 else
    if slot = .data (.root 0) 0 then 1 else
    if slot = .data (.root 0) 1 then 1 else 99}
def tail : List Evm.Word := [.val ⟨17, by decide⟩, .slot (.root 9)]

theorem read_joint : zero.val < Evm.W := zero.isLt
theorem write_joint : zero.val < Evm.W := zero.isLt
theorem read_failure_joint : machine.store (.root 0) = old.length.val := rfl
theorem write_failure_joint : machine.store (.root 0) = old.length.val := rfl
theorem success_joint : TargetArrayWrite.writeAt old zero false = some result := rfl

def symbolic : Store := fun _ => lengthWord 1 (by decide)
theorem header_joint : TargetArrayWrite.writeAt old zero false = some result ∧
    Represented old [.length .nil] (.root 0) symbolic := by
  refine ⟨success_joint, ?_⟩
  intro query member
  have same : query = .length .nil := List.mem_singleton.mp member
  subst query
  refine ⟨True.intro, by change 1 ≤ Storage.lmax ∧ 3 ≤ Storage.lmax; decide, ?_⟩
  intro value observed
  cases observed
  rfl

theorem live_read :
    Evm.run TargetArrayRead.code {machine with stack := .val zero :: .slot (.root 0) :: tail} =
      .ok {machine with stack := .val ⟨1, by decide⟩ :: tail} 0 := by
  exact (TargetArrayRead.run_current machine tail (.root 0) zero.val read_joint).trans (by rfl)

theorem live_write :
    Evm.run TargetArrayWrite.code
      {machine with stack := .val zero :: .slot (.root 0) :: .val ⟨0, by decide⟩ :: tail} =
      .ok {machine with stack := tail, store := Evm.WordStore.write machine.store (.data (.root 0) 0) 0} 0 := by
  exact (TargetArrayWrite.run_current machine tail (.root 0) zero.val write_joint ⟨0, by decide⟩).trans (by rfl)

theorem adapter_success : zero.val < old.length.val ∧
    old.save (TargetArrayRead.path zero) (.prim false) = some result :=
  TargetArrayWrite.success old result zero false success_joint

theorem header_frame_actual : Represented result [.length .nil] (.root 0)
    (write symbolic (pathLoc (TargetArrayRead.path (G := graph) (p := .bool) zero) (.root 0)) (PrimTy.toWord (p := .bool) false)) :=
  TargetArrayWrite.header_frame old result zero false header_joint.1 (.root 0) symbolic header_joint.2

theorem retained_raw_and_live :
    Step.get Value.dflt (.index one) old = some (.prim true) ∧
    (TargetArrayRead.path one).readLive Value.dflt old = none ∧
    TargetArrayWrite.writeAt old one false = none ∧
    old.save (TargetArrayRead.path one) (.prim false) ≠ none := by
  exact ⟨rfl, rfl, rfl, by intro impossible; cases impossible⟩

theorem retained_read_reverts : Evm.run TargetArrayRead.code
    {machine with stack := .val one :: .slot (.root 0) :: tail} = .revert := by
  exact (TargetArrayRead.failure_matches old one machine tail (.root 0) read_failure_joint).mpr rfl

theorem retained_write_reverts : Evm.run TargetArrayWrite.code
    {machine with stack := .val one :: .slot (.root 0) :: .val (TargetOperations.encodeWord (PrimTy.toWord (p := .bool) false)) :: tail} = .revert := by
  exact (TargetArrayWrite.failure_matches old one false machine tail (.root 0) write_failure_joint).mpr rfl

theorem outside_extent_reverts : Evm.run TargetArrayRead.code
    {machine with stack := .val three :: .slot (.root 0) :: tail} = .revert ∧
    Evm.run TargetArrayWrite.code {machine with stack := .val three :: .slot (.root 0) :: .val (TargetOperations.encodeWord (PrimTy.toWord (p := .bool) false)) :: tail} = .revert := by
  exact ⟨(TargetArrayRead.failure_matches old three machine tail (.root 0) read_failure_joint).mpr rfl,
    (TargetArrayWrite.failure_matches old three false machine tail (.root 0) write_failure_joint).mpr rfl⟩

theorem after_write_observations :
    let after := {machine with stack := tail, store := Evm.WordStore.write machine.store (.data (.root 0) 0) 0}
    (after.store (.root 0), after.store (.data (.root 0) 0),
      after.store (.data (.root 0) 1), after.store (.root 9), after.stack,
      after.mem 0, after.self, after.caller, after.timestamp) =
    (1, 0, 1, 99, tail, machine.mem 0, machine.self, machine.caller, machine.timestamp) := rfl

theorem reject_all_mismatch : Evm.run [.revert]
    {machine with stack := .val zero :: .slot (.root 0) :: tail} ≠
    Evm.run TargetArrayRead.code {machine with stack := .val zero :: .slot (.root 0) :: tail} := by
  rw [live_read]
  intro equal
  cases equal

/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.read_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms read_joint
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.write_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms write_joint
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.read_failure_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms read_failure_joint
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.write_failure_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms write_failure_joint
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.success_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms success_joint
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.header_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms header_joint
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.live_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms live_read
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.live_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms live_write
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.adapter_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms adapter_success
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.header_frame_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms header_frame_actual
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.retained_raw_and_live' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms retained_raw_and_live
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.retained_read_reverts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms retained_read_reverts
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.retained_write_reverts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms retained_write_reverts
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.outside_extent_reverts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outside_extent_reverts
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.after_write_observations' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms after_write_observations
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.reject_all_mismatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reject_all_mismatch

end H62.StorageAudit.ArrayAccessWitnesses
