import Solidity.Evm.MemoryStorageCopyLaws

/-! Contract for copy-back after an explicitly executed memory-preserving program.
The intervention run is a premise, not a callback or Source adequacy theorem.
Cleanup uses the reached old destination; the typed payload is the captured heap. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def snapshotRestoreCode (intervention : List Instr) (destination : Slot) : List Instr :=
  intervention ++ [.push (.slot destination)] ++ memoryArrayCopyCode

def SnapshotRestoreResult {H : HTy} {primitive : PrimTy} (heap : Heap H)
    (reference : HRef H (.array (.prim primitive))) (address : Fin W)
    (before changed : Machine) (intervention : List Instr) (destination : Slot)
    (L : Nat) (old : SVal (.ref (.array (.prim primitive)))) : Prop :=
  let words := fun i => payloadWord (before.mem (address.val+1+i))
  let final : Machine := {changed with store := arrayCopyStore changed.store destination (heap.len reference .dyn) words}
  run (snapshotRestoreCode intervention destination) (before.push (.val address)) = .ok final 0 ∧
  run memoryArrayCopyCode ((changed.push (.val address)).push (.slot destination)) = .ok final 0 ∧
  ReprAt final.store L (.ref (.array (.prim primitive))) destination (old.overlay (MVal.copyMToSt heap reference)) ∧
  final.store destination = heap.len reference .dyn ∧
  (∀ i, i < heap.len reference .dyn → final.store (.data destination i) = (words i).val) ∧
  (∀ i, heap.len reference .dyn ≤ i → i < old.view.n → final.store (.data destination i) = 0) ∧
  (∀ slot, ¬ Occ (.ref (.array (.prim primitive))) destination slot → final.store slot = changed.store slot) ∧
  final.mem = before.mem ∧ final.stack = changed.stack

structure SnapshotRestoreCertificate : Prop where
  restore : ∀ {H : HTy} {primitive : PrimTy} (heap : Heap H)
    (reference : HRef H (.array (.prim primitive))) (address : Fin W)
    (before changed : Machine) (intervention : List Instr) (destination : Slot)
    (L : Nat) (old : SVal (.ref (.array (.prim primitive)))),
    Evm.Memory.ArrayRepr heap reference address before →
    run intervention (before.push (.val address)) = .ok (changed.push (.val address)) 0 →
    changed.mem = before.mem →
    ReprAt changed.store L (.ref (.array (.prim primitive))) destination old →
    heap.len reference .dyn < L →
    SnapshotRestoreResult heap reference address before changed intervention destination L old

end Solidity.Backend.MemoryCopies
