import Solidity.Backend.MemoryCopies.SnapshotRestoreInterface

/-! Compose an explicit memory-preserving intervention with the published typed
array copy-back. The restored contents come from the captured representation;
cleanup and storage framing refer to the reached post-intervention store. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

private theorem push_destination (changed : Machine) (address : Fin W) (destination : Slot) :
    run [.push (.slot destination)] (changed.push (.val address)) =
      .ok ((changed.push (.val address)).push (.slot destination)) 0 := rfl

attribute [local irreducible] run exec Instr.step loopRun

theorem snapshot_restore_correct {H : HTy} {primitive : PrimTy} (heap : Heap H)
    (reference : HRef H (.array (.prim primitive))) (address : Fin W)
    (before changed : Machine) (intervention : List Instr) (destination : Slot)
    (L : Nat) (old : SVal (.ref (.array (.prim primitive))))
    (captured : Evm.Memory.ArrayRepr heap reference address before)
    (executed : run intervention (before.push (.val address)) = .ok (changed.push (.val address)) 0)
    (memory : changed.mem = before.mem)
    (represented : ReprAt changed.store L (.ref (.array (.prim primitive))) destination old)
    (bounded : heap.len reference .dyn < L) :
    SnapshotRestoreResult heap reference address before changed intervention destination L old := by
  have reached : Evm.Memory.ArrayRepr heap reference address changed := by
    refine ⟨captured.space,?_,?_⟩
    · rw [memory]
      exact captured.length
    · intro i item selected
      rw [memory]
      exact captured.elements i item selected
  let words := fun i => payloadWord (before.mem (address.val+1+i))
  let final : Machine := {changed with store := arrayCopyStore changed.store destination (heap.len reference .dyn) words}
  have payload : ∀ i, i < heap.len reference .dyn → changed.mem (address.val+1+i) = .val (words i) := by
    intro i within
    let item := (MObj.elems .dyn (heap.get reference))[i]'within
    rw [memory]
    exact ReprV.payload (captured.elements i item (getElem?_pos _ i within))
  have copied : run memoryArrayCopyCode ((changed.push (.val address)).push (.slot destination)) = .ok final 0 :=
    memoryArrayCopy_run changed address destination (heap.len reference .dyn) words
      (heap.len_dyn_lt reference) reached.space reached.length payload
  have typed : ReprAt final.store L (.ref (.array (.prim primitive))) destination
      (old.overlay (MVal.copyMToSt heap reference)) :=
    primitiveArray_copy_repr captured changed.store destination L bounded old
  have oldLength : changed.store destination = old.view.n := by
    cases represented with
    | array header small entries => exact header
  refine ⟨?_,copied,typed,arrayCopyStore_length _ _ _ _ (heap.len_dyn_lt reference),?_,?_,?_,memory,rfl⟩
  · rw [snapshotRestoreCode,List.append_assoc,run_append_ok executed,run_append_ok (push_destination changed address destination)]
    exact copied
  · intro i within
    exact arrayCopyStore_live changed.store destination (heap.len reference .dyn) words i within
  · intro i lower upper
    exact arrayCopyStore_tail changed.store destination (heap.len reference .dyn) words i lower (by rw [oldLength]; exact upper)
  · intro slot outside
    exact arrayCopyStore_other (p := primitive) changed.store destination (heap.len reference .dyn) words slot outside

def snapshotRestore : SnapshotRestoreCertificate := ⟨snapshot_restore_correct⟩

/--
info: 'Solidity.Backend.MemoryCopies.snapshot_restore_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms snapshot_restore_correct
/--
info: 'Solidity.Backend.MemoryCopies.snapshotRestore' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms snapshotRestore

end Solidity.Backend.MemoryCopies
