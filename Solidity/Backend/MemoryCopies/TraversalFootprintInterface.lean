import Solidity.Backend.MemoryCopies.TraversalInterface

/-! Exact object-identity footprint obligations for the existing intrinsic copy.
Counts are heap identities, not physical words, gas or Source interpreter fuel. -/
namespace Solidity.Backend.MemoryCopies

structure TraversalFootprintCertificate {H : HTy} {R : RefTy} (heap : Heap H)
    (value : SVal (.ref R)) (memory : (Ty.ref R).mapFree = true) (objects : Nat) : Prop where
  count : (value.copyStToM heap memory).H'.length = H.length + objects
  parent_last : (value.copyStToM heap memory).val.id + 1 = (value.copyStToM heap memory).H'.length

structure TraversalPairFootprint {H : HTy} {R Q : RefTy} (heap : Heap H)
    (first : SVal (.ref R)) (second : SVal (.ref Q))
    (firstMemory : (Ty.ref R).mapFree = true) (secondMemory : (Ty.ref Q).mapFree = true)
    (firstObjects secondObjects : Nat) : Prop where
  first_count : (first.copyStToM heap firstMemory).H'.length = H.length + firstObjects
  second_count : (second.copyStToM (first.copyStToM heap firstMemory).heap secondMemory).H'.length =
    H.length + firstObjects + secondObjects
  separated : (first.copyStToM heap firstMemory).val.id < (first.copyStToM heap firstMemory).H'.length ∧
    (first.copyStToM heap firstMemory).H'.length ≤
      (second.copyStToM (first.copyStToM heap firstMemory).heap secondMemory).val.id
end Solidity.Backend.MemoryCopies
