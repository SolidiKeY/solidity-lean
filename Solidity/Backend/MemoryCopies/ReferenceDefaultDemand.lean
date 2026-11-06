import Solidity.Backend.MemoryCopies.ReferenceDefaultDemandInterface

/-! Cost and allocation agreement for existing runtime reference defaults.
The target constructor/guard and the intrinsic copying fold are unchanged. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem reference_default_copy {H : HTy} (heap : Heap H) (root : RefTy)
    (memory : (Ty.ref root).mapFree = true) (size : Fin W) :
    (referenceDefaultValue root size).copyStToM heap memory =
      Objects.referenceArrayCopy heap root memory size := by
  rw [referenceDefaultValue, SVal.copyStToM_array]
  rfl

theorem reference_default_words {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) (size : Fin W) :
    referenceDefaultWords root size =
      size.val + 1 + size.val * ReferenceDefaults.defaultCells (.ref root) := by
  have available : (ReferenceDefaults.compileDefault root memory).isSome = true := by
    rw [selected.selected]; rfl
  simp only [referenceDefaultWords, referenceDefaultValue, liveWordCount, replicated_element_words]
  rw [selected_default_words root memory available]
  omega

theorem reference_default_allocation {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) {H : HTy} (heap : Heap H) (size : Fin W) :
    heapWords (Objects.referenceArrayCopy heap root memory size).heap =
      heapWords heap + referenceDefaultWords root size := by
  rw [← reference_default_copy heap root memory size]
  exact valueCopy_words (referenceDefaultValue root size) memory heap

theorem reference_default_checked {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) {H : HTy} (heap : Heap H) (size : Fin W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    run (checkedReferenceCode selected) (machine.push (.val size)) =
      if cursor.val + referenceDefaultWords root size < W
      then run (Objects.referenceArrayCode selected.builder.code) (machine.push (.val size))
      else .revert := by
  rw [reference_default_words selected size]
  exact checked_reference_run selected heap size base frame cursor machine allocator

def referenceDefaultDemand : ReferenceDefaultDemandCertificate :=
  ⟨reference_default_words, reference_default_allocation, reference_default_checked⟩

/--
info: 'Solidity.Backend.MemoryCopies.reference_default_copy' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms reference_default_copy
/--
info: 'Solidity.Backend.MemoryCopies.reference_default_words' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reference_default_words
/--
info: 'Solidity.Backend.MemoryCopies.reference_default_allocation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reference_default_allocation
/--
info: 'Solidity.Backend.MemoryCopies.reference_default_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reference_default_checked
/--
info: 'Solidity.Backend.MemoryCopies.referenceDefaultDemand' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms referenceDefaultDemand
end Solidity.Backend.MemoryCopies
