import Solidity.Backend.MemoryCopies.MemoryParentSnapshotInterface

/-! Complete parent contents agree with the actual row traversal. The proof
normalizes only the existing rank-bounded read and reuses primitive snapshots. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory
open Semantics (tyRank)

private theorem child_rows_toList {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (children : List (HRef H (.array (.prim primitive)))) :
    (nestedStorageValues primitive (children.map (fun child : HRef H (.array (.prim primitive)) =>
      (⟨MObj.elems .dyn (heap.get child), heap.len_dyn_lt child⟩ : PrimitiveStorageRow primitive)))).toList =
      children.map (MVal.copyMToSt heap (T := .ref (.array (.prim primitive)))) := by
  induction children with
  | nil => simp only [List.map_nil, nestedStorageValues, SVec.toList_nil]
  | cons child children ih =>
    simp only [List.map_cons, nestedStorageValues, SVec.toList_cons, primitiveArray_snapshot,
      primitiveArrayValue, ih]

private theorem parent_arrays_equal {E : Ty} {n m : Nat} (left : SVec E n) (right : SVec E m)
    (ln : n < 2 ^ 256) (rm : m < 2 ^ 256) (same : left.toList = right.toList) :
    SVal.array left .nil ln = SVal.array right .nil rm := by
  have count : n = m := by
    simpa only [SVec.length_toList] using congrArg List.length same
  cases count
  have values : left = right := SVec.eq_of_toList_eq left right same
  cases values
  rfl

private theorem child_read_at_eq {H : HTy} (heap : Heap H) (k : Nat) (T : Ty)
    (bound : tyRank T < k + 1) (value : MVal H T) :
    MVal.copyAt heap k (MVal.copyBelow heap k) T bound value = MVal.copyMToSt heap value :=
  MVal.copyBelow_eq heap (k + 1) T bound value

theorem memory_parent_snapshot {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) :
    MVal.copyMToSt heap (T := .ref (.array (.ref (.array (.prim primitive))))) source =
      memoryParentRowsValue heap primitive source := by
  unfold MVal.copyMToSt
  rw [MVal.copyBelow, MVal.copyAt, MVal.copyRefAt]
  unfold memoryParentRowsValue nestedStorageParentValue
  apply parent_arrays_equal
  rw [SVec.toList_ofList]
  calc
    _ = ((heap.get source).val).map (MVal.copyMToSt heap (T := .ref (.array (.prim primitive)))) :=
      congrArg (fun f => ((heap.get source).val).map f) (funext (child_read_at_eq heap _ _ _))
    _ = _ := by
      simpa only [memoryChildRows, MObj.elems_dyn] using (child_rows_toList heap primitive ((heap.get source).val)).symm

theorem memory_parent_copy_agreement {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) :
    (MVal.copyMToSt heap (T := .ref (.array (.ref (.array (.prim primitive))))) source).copyStToM heap rfl =
      (memoryParentRowsValue heap primitive source).copyStToM heap rfl :=
  congrArg (fun value : SVal (.ref (.array (.ref (.array (.prim primitive))))) => value.copyStToM heap rfl)
    (memory_parent_snapshot heap primitive source)

def memoryParentSnapshot : MemoryParentSnapshotCertificate := ⟨memory_parent_snapshot⟩

#print axioms memory_parent_snapshot
#print axioms memory_parent_copy_agreement
#print axioms memoryParentSnapshot
end Solidity.Backend.MemoryCopies
