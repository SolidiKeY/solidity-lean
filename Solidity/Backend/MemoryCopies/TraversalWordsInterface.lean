import Solidity.Evm.MemoryObjectAllocator
import Solidity.Backend.MemoryCopies.TraversalInterface

/-! Unconditional intrinsic cell-sum obligations for the existing deep-copy fold.
The concrete measures must be supplied; this interface asserts no runtime
compiler, physical layout, Source admission, gas or capacity-failure result. -/
namespace Solidity.Backend.MemoryCopies

structure TraversalWordsCertificate
    (heapWords : {H : HTy} → Heap H → Nat)
    (liveWords : {T : Ty} → SVal T → Nat) : Prop where
  exact_growth : ∀ {T : Ty} (value : SVal T) (memory : T.mapFree = true)
    {H : HTy} (heap : Heap H),
    heapWords (value.copyStToM heap memory).heap = heapWords heap + liveWords value
  old_cells : ∀ {T : Ty} (value : SVal T) (memory : T.mapFree = true)
    {H : HTy} (heap : Heap H) {R : RefTy} (reference : HRef H R),
    Evm.Memory.Objects.cells (value.copyStToM heap memory).heap
      (reference.wk (value.copyStToM heap memory).ext) =
      Evm.Memory.Objects.cells heap reference

end Solidity.Backend.MemoryCopies
