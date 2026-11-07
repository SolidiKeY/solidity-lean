import Solidity.Backend.MemoryCopies.NestedMemoryRows
import Solidity.Backend.MemoryCopies.NestedStorageParentInterface

/-! The complete existing source snapshot agrees with the parent value built
from actual heap-derived child rows. No caller-provided rows or shape premise
is required. This is an intrinsic content bridge, not compiled parent entry. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def memoryParentRowsValue {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) :
    SVal (.ref (.array (.ref (.array (.prim primitive))))) :=
  nestedStorageParentValue primitive (memoryChildRows heap primitive source) (by
    rw [memory_rows_length]
    exact heap.len_dyn_lt source)

structure MemoryParentSnapshotCertificate : Prop where
  snapshot : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))),
    MVal.copyMToSt heap (T := .ref (.array (.ref (.array (.prim primitive))))) source =
      memoryParentRowsValue heap primitive source

end Solidity.Backend.MemoryCopies
