import Solidity.Backend.Failure.Unwind
import Solidity.Backend.Failure.SliceChecks

/-! Distinct, inhabited persistent/transient types and snapshots. The nested
witness actually executes two emitted failures with an intervening local
mutation; no call/world/catch semantics is presumed. -/
namespace Solidity.Backend.Failure.Local

abbrev Witness := Journal (Fin 17) (Fin 19)

def root : Witness := ⟨⟨1, by decide⟩, ⟨2, by decide⟩, markedMachine⟩
def middle : Witness := ⟨⟨7, by decide⟩, ⟨11, by decide⟩,
  { markedMachine with memory := Slice.putByte markedMemory 0 0xaa }⟩
def deep : Witness := ⟨⟨13, by decide⟩, ⟨17, by decide⟩,
  { markedMachine with memory := Slice.putByte markedMemory 0 0xbb }⟩

def resume (s : Witness) : Witness :=
  ⟨⟨15, by decide⟩, ⟨18, by decide⟩,
    { s.machine with memory := Slice.putByte s.machine.memory 0 0xcc }⟩

theorem inner_failure_control :
    execute (save middle) 31 (.custom [0xde, 0xad]) deep =
      some (middle, .revert [0xde, 0xad]) := by
  simpa only [restore_save] using
    execute_failure (save middle) 31 [0xde, 0xad] deep
      (by unfold Fits; decide) (by decide)

theorem outer_failure_control :
    execute (save root) 64 (.custom [0xbe, 0xef, 0, 0xff]) (resume middle) =
      some (root, .revert [0xbe, 0xef, 0, 0xff]) := by
  simpa only [restore_save] using
    execute_failure (save root) 64 [0xbe, 0xef, 0, 0xff] (resume middle)
      (by unfold Fits; decide) (by decide)

theorem nested_failure_control :
    nested (save root) (save middle) 31 64 [0xde, 0xad] [0xbe, 0xef, 0, 0xff] resume deep =
      some (root, .revert [0xde, 0xad], .revert [0xbe, 0xef, 0, 0xff]) := by
  simpa only [restore_save] using
    nested_failure (save root) (save middle) 31 64 [0xde, 0xad] [0xbe, 0xef, 0, 0xff] resume deep
      (by unfold Fits; decide) (by unfold Fits; decide) (by decide) (by decide)

theorem distinct_snapshots_control :
    (restore (save root)).persistent.val = 1 ∧ (restore (save root)).transient.val = 2 ∧
    (restore (save middle)).persistent.val = 7 ∧ (restore (save middle)).transient.val = 11 ∧
    deep.persistent.val = 13 ∧ deep.transient.val = 17 ∧
    (resume middle).persistent.val = 15 ∧ (resume middle).transient.val = 18 := by decide

theorem restored_memory_control :
    (restore (save middle)).machine.memory 0 = 0xaa ∧
    (restore (save root)).machine.memory 0 = 17 ∧
    deep.machine.memory 0 = 0xbb ∧ (resume middle).machine.memory 0 = 0xcc ∧
    (restore (save middle)).machine.memory 31 = 48 := by decide

theorem wrong_transient_rejected :
    ¬ CheckpointRel (save root) (.revert [9]) deep { root with transient := ⟨11, by decide⟩ } := by
  intro h
  have he : restore (save root) = { root with transient := ⟨11, by decide⟩ } :=
    CheckpointRel.functional (CheckpointRel.revert [9] deep) h
  have ht : (2 : Nat) = 11 := congrArg (fun s : Witness => s.transient.val) he
  omega

theorem wrong_persistent_rejected :
    ¬ CheckpointRel (save root) (.revert [9]) deep { root with persistent := ⟨7, by decide⟩ } := by
  intro h
  have he : restore (save root) = { root with persistent := ⟨7, by decide⟩ } :=
    CheckpointRel.functional (CheckpointRel.revert [9] deep) h
  have hp : (1 : Nat) = 7 := congrArg (fun s : Witness => s.persistent.val) he
  omega

theorem return_keeps_live_control :
    execute (save root) 31 (.returned [1, 2, 3]) deep =
      some ({ deep with machine :=
        { deep.machine with memory := Slice.putBytes deep.machine.memory 31 [1, 2, 3] } },
        .success [1, 2, 3]) :=
  execute_return (save root) 31 [1, 2, 3] deep (by unfold Fits; decide) (by decide)

theorem successful_outer_control :
    execute (save root) 31 (.returned [7]) (restore (save middle)) =
      some ({ middle with machine := { middle.machine with memory := Slice.putBytes middle.machine.memory 31 [7] } },
        .success [7]) := by
  simpa only [restore_save] using
    execute_return (save root) 31 [7] (restore (save middle)) (by unfold Fits; decide) (by decide)

/-- info: 'Solidity.Backend.Failure.Local.CheckpointRel.functional' does not depend on any axioms -/
#guard_msgs in
#print axioms CheckpointRel.functional
/-- info: 'Solidity.Backend.Failure.Local.outer_rollback' does not depend on any axioms -/
#guard_msgs in
#print axioms outer_rollback
/-- info: 'Solidity.Backend.Failure.Local.execute_checkpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms execute_checkpoint
/-- info: 'Solidity.Backend.Failure.Local.execute_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms execute_failure
/-- info: 'Solidity.Backend.Failure.Local.execute_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms execute_return
/-- info: 'Solidity.Backend.Failure.Local.nested_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nested_failure
/-- info: 'Solidity.Backend.Failure.Local.nested_failure_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nested_failure_control
/-- info: 'Solidity.Backend.Failure.Local.wrong_transient_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms wrong_transient_rejected
end Solidity.Backend.Failure.Local
