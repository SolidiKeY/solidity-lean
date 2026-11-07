import Solidity.Backend.MemoryCopies.CheckedDefault
import Solidity.Backend.MemoryCopies.DefaultDemand

/-! Cost agreement for the existing selected default compiler. This does not
extend its selection domain or supply Source allocation panic semantics. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

structure SelectedDefaultDemandCertificate : Prop where
  demand : ∀ (root : RefTy) (memory : (Ty.ref root).mapFree = true),
    (ReferenceDefaults.compileDefault root memory).isSome = true →
    liveWordCount (SVal.dflt (.ref root)) = ReferenceDefaults.defaultCells (.ref root)
  allocation : ∀ {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) {H : HTy} (heap : Heap H),
    heapWords (heap.allocDefault root memory).heap =
      heapWords heap + ReferenceDefaults.defaultCells (.ref root)
  checked : ∀ {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) {H : HTy} (heap : Heap H)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine),
    Objects.AllocatorRepr heap base frame cursor machine →
    run selected.code machine =
      if cursor.val + liveWordCount (SVal.dflt (.ref root)) < W
      then run selected.builder.code machine else .revert

end Solidity.Backend.MemoryCopies
