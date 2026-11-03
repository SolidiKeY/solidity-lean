import Solidity.Backend.StorageOps.TargetNestedArrayRuntime

/-! Target self-copy at arbitrary runtime lengths, with no Source imports.
The historical theorem namespace is retained for compatibility. TargetSelfCopy
exports the same laws; legacy SourceSelfCopy imports remain valid. Static-call,
gas and world refinement of the legacy target model remain separate obligations. -/
namespace Solidity.Backend.StorageOps.SourceSelfCopy

private theorem write_read_self (store : Evm.WordStore) (slot : Evm.Slot) :
    Evm.WordStore.write store slot (store slot) = store := by
  apply Evm.WordStore.ext
  intro observer
  by_cases same : observer = slot
  · subst observer
    exact Evm.WordStore.write_same_of_lt store slot _ (Evm.WordStore.read_lt store slot)
  · exact Evm.WordStore.write_other store _ same

theorem primitive_prefix_self (store : Evm.WordStore) (slot : Evm.Slot) (count : Nat) :
    TargetArrayCopy.copyPrefix store slot slot count = store := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [TargetArrayCopy.copyPrefix,ih]
    exact write_read_self store (.data slot count)

theorem primitive_after_self (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot) :
    TargetArrayCopyTail.afterCopy machine tail slot slot = { machine with stack := tail } := by
  unfold TargetArrayCopyTail.afterCopy
  rw [primitive_prefix_self,Nat.max_self,
    TargetArrayCopyTail.suffix_before _ _ _ _ (Nat.le_refl _),write_read_self]

theorem nested_prefix_self (machine : Evm.Machine) (slot : Evm.Slot) (count : Nat) :
    TargetNestedArrayCopyLoop.prefixMachine machine slot slot count = machine := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [TargetNestedArrayCopyLoop.prefixMachine,ih,primitive_after_self]

theorem nested_after_self (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot) :
    TargetNestedArrayRuntime.afterCopy machine tail slot slot = { machine with stack := tail } := by
  unfold TargetNestedArrayRuntime.afterCopy
  simp only [nested_prefix_self,Nat.max_self]
  rw [TargetNestedArrayClearLoop.prefix_before _ _ _ _ (Nat.le_refl _)]
  have saved : Evm.WordStore.write machine.store slot (machine.store.cells slot).val = machine.store :=
    write_read_self machine.store slot
  rw [saved]

theorem run_self (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot) :
    Evm.run TargetNestedArrayCopy.code { machine with stack := .slot slot :: .slot slot :: tail } =
      .ok { machine with stack := tail } 0 := by
  rw [TargetNestedArrayRuntime.run_current,nested_after_self]

/-- info: 'Solidity.Backend.StorageOps.SourceSelfCopy.primitive_prefix_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms primitive_prefix_self

/-- info: 'Solidity.Backend.StorageOps.SourceSelfCopy.primitive_after_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms primitive_after_self

/-- info: 'Solidity.Backend.StorageOps.SourceSelfCopy.nested_prefix_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms nested_prefix_self

/-- info: 'Solidity.Backend.StorageOps.SourceSelfCopy.nested_after_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms nested_after_self

/-- info: 'Solidity.Backend.StorageOps.SourceSelfCopy.run_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_self
end Solidity.Backend.StorageOps.SourceSelfCopy

namespace Solidity.Backend.StorageOps.TargetSelfCopy
export Solidity.Backend.StorageOps.SourceSelfCopy (primitive_prefix_self primitive_after_self nested_prefix_self nested_after_self run_self)
end Solidity.Backend.StorageOps.TargetSelfCopy
