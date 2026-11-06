import Solidity.Backend.MemoryCopies.RuntimeStorageArray

/-! Live primitive-array normalization retains the original storage value and
forgets only the storage shadow when constructing its memory copy. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def primitiveArrayLiveValues {primitive : PrimTy}
    (value : SVal (.ref (.array (.prim primitive)))) : List primitive.Denote :=
  value.view.elems.toList.map (fun element => element.view)

structure PrimitiveArrayLiveCertificate {primitive : PrimTy}
    (value : SVal (.ref (.array (.prim primitive)))) : Prop where
  bounded : (primitiveArrayLiveValues value).length < W
  copying : ∀ {H : HTy} (heap : Heap H),
    value.copyStToM heap rfl =
      (primitiveArrayValue primitive (primitiveArrayLiveValues value) bounded).copyStToM heap rfl
  representation : ∀ (store : WordStore) (limit : Nat) (source : Slot),
    ReprAt store limit (.ref (.array (.prim primitive))) source value →
    ReprAt store limit (.ref (.array (.prim primitive))) source
      (primitiveArrayValue primitive (primitiveArrayLiveValues value) bounded)
end Solidity.Backend.MemoryCopies
