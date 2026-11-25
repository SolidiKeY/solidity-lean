import Solidity.Backend.MemoryCopies.NestedMemoryParentInterface
import Solidity.Backend.MemoryCopies.MemoryCopyDemand

/-! The checked parent reservation plus child reservations consume exactly the
existing source snapshot's symbolic live words. This is not a gas estimate. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem memory_parent_demand_snapshot {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) :
    memoryParentDemand heap primitive source = liveWordCount (MVal.copyMToSt heap (T := .ref (.array (.ref (.array (.prim primitive))))) source) := by
  rw [memory_parent_snapshot]
  simp only [memoryParentRowsValue, memoryParentDemand, nestedStorageParentValue, nestedStorageParentDemand,
    liveWordCount, nestedStorage_elementWordCount]
  omega

theorem memory_parent_copy_word_growth {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) :
    heapWords ((MVal.copyMToSt heap (T := .ref (.array (.ref (.array (.prim primitive))))) source).copyStToM heap rfl).heap =
      heapWords heap + memoryParentDemand heap primitive source := by
  rw [valueCopy_words, memory_parent_demand_snapshot]

#print axioms memory_parent_demand_snapshot
#print axioms memory_parent_copy_word_growth
end Solidity.Backend.MemoryCopies
