import Solidity.Backend.MemoryCopies.MemoryParentSnapshot
import Solidity.Backend.MemoryCopies.TraversalWords

/-! Concrete intrinsic source contents, alias multiplicity and exact copy-fold
word growth. These controls do not claim compiled parent entry or gas behavior. -/
namespace Solidity.Backend.MemoryCopies.MemoryParentSnapshotControls
open Evm Evm.Memory
private abbrev R (primitive : PrimTy) : RefTy := .array (.prim primitive)
private abbrev P (primitive : PrimTy) : RefTy := .array (.ref (R primitive))
private def child (primitive : PrimTy) : HRef [R primitive, P primitive] (R primitive) := ⟨0, rfl⟩
private def source (primitive : PrimTy) : HRef [R primitive, P primitive] (P primitive) := ⟨1, rfl⟩
private def aliases (primitive : PrimTy) (values : List primitive.Denote) (bounded : values.length < W) :
    Heap [R primitive, P primitive] := (⟨values, bounded⟩, (⟨[child primitive, child primitive], by change 2 < 2 ^ 256; decide⟩, ()))
private def row (primitive : PrimTy) (values : List primitive.Denote) (bounded : values.length < W) : PrimitiveStorageRow primitive :=
  ⟨values, bounded⟩
private def pair : List PrimTy.uint.Denote := [indexValue (wmod 11), indexValue (wmod 23)]
private def long : List PrimTy.uint.Denote := List.ofFn (fun i : Fin 64 => indexValue (wmod (i.val + 1)))
private abbrev HM : HTy := [R .uint, R .uint, R .uint, P .uint]
private def mixed0 : HRef HM (R .uint) := ⟨0, rfl⟩
private def mixed1 : HRef HM (R .uint) := ⟨1, rfl⟩
private def mixed2 : HRef HM (R .uint) := ⟨2, rfl⟩
private def mixedSource : HRef HM (P .uint) := ⟨3, rfl⟩
private def mixedHeap : Heap HM := (⟨pair, by decide⟩, (⟨[], by decide⟩,
  (⟨long, by rw [long, List.length_ofFn]; decide⟩, (⟨[mixed0,mixed1,mixed2], by decide⟩, ()))))
private def mixedRows : List (PrimitiveStorageRow .uint) :=
  [row .uint pair (by decide), row .uint [] (by decide), row .uint long (by rw [long, List.length_ofFn]; decide)]

theorem certificate_inhabited : MemoryParentSnapshotCertificate := memoryParentSnapshot

theorem aliases_are_actual (primitive : PrimTy) (values : List primitive.Denote) (bounded : values.length < W) :
    (aliases primitive values bounded).index (source primitive) .dyn (indexValue (wmod 0)) = some (child primitive) ∧
    (aliases primitive values bounded).index (source primitive) .dyn (indexValue (wmod 1)) = some (child primitive) := by
  exact ⟨by with_unfolding_all rfl, by with_unfolding_all rfl⟩

theorem alias_rows (primitive : PrimTy) (values : List primitive.Denote) (bounded : values.length < W) :
    memoryChildRows (aliases primitive values bounded) primitive (source primitive) =
      [row primitive values bounded, row primitive values bounded] := by
  with_unfolding_all rfl

theorem alias_snapshot (primitive : PrimTy) (values : List primitive.Denote) (bounded : values.length < W) :
    MVal.copyMToSt (aliases primitive values bounded) (T := .ref (P primitive)) (source primitive) =
      nestedStorageParentValue primitive [row primitive values bounded, row primitive values bounded] (by change 2 < W; decide) := by
  simpa only [memoryParentRowsValue, alias_rows] using memory_parent_snapshot (aliases primitive values bounded) primitive (source primitive)

theorem mixed_rows : memoryChildRows mixedHeap .uint mixedSource = mixedRows := by
  with_unfolding_all rfl

theorem mixed_snapshot : MVal.copyMToSt mixedHeap (T := .ref (P .uint)) mixedSource =
    nestedStorageParentValue .uint mixedRows (by decide) := by
  simpa only [memoryParentRowsValue, mixed_rows] using memory_parent_snapshot mixedHeap .uint mixedSource

theorem mixed_word_demand : liveWordCount (MVal.copyMToSt mixedHeap (T := .ref (P .uint)) mixedSource) = 73 := by
  rw [mixed_snapshot]
  decide +kernel

theorem mixed_copy_growth :
    heapWords ((MVal.copyMToSt mixedHeap (T := .ref (P .uint)) mixedSource).copyStToM mixedHeap rfl).heap =
      heapWords mixedHeap + 73 := by
  rw [valueCopy_words, mixed_word_demand]

theorem aliases_expand_demand : liveWordCount
    (MVal.copyMToSt (aliases .uint pair (by decide)) (T := .ref (P .uint)) (source .uint)) = 9 := by
  rw [alias_snapshot]
  decide +kernel

private def emptySource (primitive : PrimTy) : HRef [P primitive] (P primitive) := ⟨0,rfl⟩
private def emptyHeap (primitive : PrimTy) : Heap [P primitive] := (⟨[],by change 0 < 2 ^ 256; decide⟩,())

theorem empty_parent_snapshot (primitive : PrimTy) : MVal.copyMToSt (emptyHeap primitive) (T := .ref (P primitive)) (emptySource primitive) =
    nestedStorageParentValue primitive [] (by change 0 < W; decide) := by
  have rows : memoryChildRows (emptyHeap primitive) primitive (emptySource primitive) = [] := by with_unfolding_all rfl
  simpa only [memoryParentRowsValue, rows] using memory_parent_snapshot (emptyHeap primitive) primitive (emptySource primitive)

theorem empty_parent_demand (primitive : PrimTy) :
    liveWordCount (MVal.copyMToSt (emptyHeap primitive) (T := .ref (P primitive)) (emptySource primitive)) = 1 := by
  rw [empty_parent_snapshot]
  simp only [nestedStorageParentValue, nestedStorageValues, liveWordCount, elementWordCount, List.length_nil, Nat.add_zero, Nat.zero_add]

private def erased : SVal (.ref (P .uint)) := nestedStorageParentValue .uint
  [row .uint [indexValue (wmod 0),indexValue (wmod 0)] (by decide), row .uint [indexValue (wmod 0),indexValue (wmod 0)] (by decide)] (by decide)

theorem wrong_payload_rejected : MVal.copyMToSt (aliases .uint pair (by decide)) (T := .ref (P .uint)) (source .uint) ≠ erased := by
  rw [alias_snapshot]
  intro equal
  have different : (nestedStorageParentValue .uint [row .uint pair (by decide),row .uint pair (by decide)] (by decide)).beq erased = false := by decide +kernel
  rw [equal, SVal.beq_self] at different
  cases different

theorem collapsed_alias_rejected : MVal.copyMToSt (aliases .uint pair (by decide)) (T := .ref (P .uint)) (source .uint) ≠
    nestedStorageParentValue .uint [row .uint pair (by decide)] (by decide) := by
  intro equal
  have count : ((MVal.copyMToSt (aliases .uint pair (by decide)) (T := .ref (P .uint)) (source .uint)).view).n = 2 :=
    (MVal.copyMToSt_len _ _).trans (by with_unfolding_all rfl)
  rw [equal] at count
  change 1 = 2 at count
  cases count

#print axioms certificate_inhabited
#print axioms aliases_are_actual
#print axioms alias_rows
#print axioms alias_snapshot
#print axioms mixed_rows
#print axioms mixed_snapshot
#print axioms mixed_word_demand
#print axioms mixed_copy_growth
#print axioms aliases_expand_demand
#print axioms empty_parent_snapshot
#print axioms empty_parent_demand
#print axioms wrong_payload_rejected
#print axioms collapsed_alias_rejected
end Solidity.Backend.MemoryCopies.MemoryParentSnapshotControls
