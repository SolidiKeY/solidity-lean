import Solidity.Backend.MemoryCopies.NestedMemoryParentInterface
import Solidity.Backend.MemoryCopies.MemoryCopyDemand

/-! The checked parent reservation plus child reservations consume exactly the
existing source snapshot's symbolic live words. This is not a gas estimate. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

private theorem primitive_live_words {primitive : PrimTy} (items : List primitive.Denote) :
    elementWordCount (SVec.ofList (items.map SVal.prim)) = 0 := by
  induction items with
  | nil => simp only [List.map_nil, SVec.ofList, elementWordCount]
  | cons item items ih => simp only [List.map_cons, SVec.ofList, elementWordCount, liveWordCount, ih, Nat.zero_add]

private theorem row_live_words (primitive : PrimTy) (items : List primitive.Denote) (bounded : items.length < W) :
    liveWordCount (primitiveArrayValue primitive items bounded) = items.length + 1 := by
  simp only [primitiveArrayValue, liveWordCount, primitive_live_words, List.length_map, Nat.zero_add]
  omega

private theorem child_live_words (primitive : PrimTy) (rows : List (PrimitiveStorageRow primitive)) :
    elementWordCount (nestedStorageValues primitive rows) = nestedStorageDemand rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp only [nestedStorageValues, elementWordCount, row_live_words, nestedStorageDemand, ih]

theorem memory_parent_demand_snapshot {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) :
    memoryParentDemand heap primitive source = liveWordCount (MVal.copyMToSt heap (T := .ref (.array (.ref (.array (.prim primitive))))) source) := by
  rw [memory_parent_snapshot]
  simp only [memoryParentRowsValue, memoryParentDemand, nestedStorageParentValue, nestedStorageParentDemand,
    liveWordCount, child_live_words]
  omega

theorem memory_parent_copy_word_growth {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) :
    heapWords ((MVal.copyMToSt heap (T := .ref (.array (.ref (.array (.prim primitive))))) source).copyStToM heap rfl).heap =
      heapWords heap + memoryParentDemand heap primitive source := by
  rw [valueCopy_words, memory_parent_demand_snapshot]

#print axioms memory_parent_demand_snapshot
#print axioms memory_parent_copy_word_growth
end Solidity.Backend.MemoryCopies
