import Solidity.Backend.StorageOps.TargetNestedArrayClearLoop

/-! Full ACTUAL two-level runtime target traversal. Both OUTER headers are
captured before writes; each copied/cleared child executes its own runtime loop.
Independent graph/PUBLIC representation correspondence is a separate gate. -/
namespace Solidity.Backend.StorageOps.TargetNestedArrayRuntime

def afterCopy (machine : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot) : Evm.Machine :=
  let sourceLength := machine.store.cells src
  let oldLength := machine.store.cells dst
  let copied := TargetNestedArrayCopyLoop.prefixMachine machine src dst sourceLength.val
  let cleared := TargetNestedArrayClearLoop.prefixMachine copied dst sourceLength.val (max sourceLength.val oldLength.val)
  { cleared with stack := tail,store := Evm.WordStore.write cleared.store dst sourceLength.val }

/-- Kernel termination/result of genuine nested runtime loops for ALL actual
outer and inner word lengths. No depth/fuel/length Source restriction is added.
This is CURRENT-source execution, not an asserted aggregate snapshot theorem. -/
theorem run_current (machine : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot) :
    Evm.run TargetNestedArrayCopy.code { machine with stack := .slot src :: .slot dst :: tail } =
      .ok (afterCopy machine tail src dst) 0 := by
  let sourceLength := machine.store.cells src
  let oldLength := machine.store.cells dst
  let copied := TargetNestedArrayCopyLoop.prefixMachine machine src dst sourceLength.val
  let cleared := TargetNestedArrayClearLoop.prefixMachine copied dst sourceLength.val (max sourceLength.val oldLength.val)
  have copyLoop := TargetNestedArrayCopyLoop.run_loop_from machine tail src dst oldLength sourceLength ⟨0,by decide⟩ (Nat.zero_le _)
  have clearLoop := TargetNestedArrayClearLoop.run_loop copied tail dst sourceLength oldLength
  unfold TargetNestedArrayCopy.code
  simp only [List.append_assoc]
  rw [Evm.run_append_ok (TargetArrayCopy.run_setup machine tail src dst)]
  change Evm.run _ (TargetNestedArrayCopyLoop.iterationMachine machine tail src dst oldLength sourceLength ⟨0,by decide⟩) = _
  rw [Evm.run_append_ok copyLoop]
  change Evm.run _ { copied with stack := .val sourceLength :: .val sourceLength :: .slot src :: .slot dst :: .val oldLength :: tail } = _
  rw [Evm.run_append_ok (TargetArrayCopyTail.run_transition copied tail src dst sourceLength oldLength)]
  rw [Evm.run_append_ok clearLoop]
  change Evm.run TargetArrayCopy.finish { cleared with stack := .val (TargetNestedArrayClearLoop.finalIndex sourceLength oldLength) :: .val oldLength :: .slot dst :: .val sourceLength :: tail } = _
  rw [TargetArrayCopyTail.run_finish cleared tail dst (TargetNestedArrayClearLoop.finalIndex sourceLength oldLength) oldLength sourceLength]
  rfl

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayRuntime.afterCopy' does not depend on any axioms -/
#guard_msgs in #print axioms afterCopy
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayRuntime.run_current' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_current

end Solidity.Backend.StorageOps.TargetNestedArrayRuntime
