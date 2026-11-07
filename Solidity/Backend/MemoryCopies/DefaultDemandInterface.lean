import Solidity.Backend.MemoryCopies.TraversalWords
import Solidity.Evm.MemoryStructDefaultPlan

/-! Agreement obligations between existing finite default plans and actual
intrinsic cell demand. Planner availability, Source admission, emitted execution,
physical capacity and allocation panic behavior are separate obligations. -/
namespace Solidity.Backend.MemoryCopies

structure DefaultDemandCertificate : Prop where
  finite_cost : ∀ (T : Ty) (cost : Nat),
    Evm.Memory.finiteDefaultCells T = some cost → liveWordCount (SVal.dflt T) = cost
  allocation : ∀ {H : HTy} (heap : Heap H) (R : RefTy)
    (memory : (Ty.ref R).mapFree = true),
    heapWords (heap.allocDefault R memory).heap =
      heapWords heap + liveWordCount (SVal.dflt (.ref R))

end Solidity.Backend.MemoryCopies
