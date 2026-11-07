import Solidity.Backend.MemoryCopies.TraversalFootprint

/-! Typed observations below existing copied heaps. Paths are the existing Path;
object bounds refer to intrinsic identities, not physical words or gas. -/
namespace Solidity.Backend.MemoryCopies

abbrev CopyPathObserver := ∀ {H : HTy}, Heap H → {T U : Ty} → Path T U → MVal H T → Option (MVal H U)

structure CopiedPathCertificate (observe : CopyPathObserver) : Prop where
  contents : ∀ {H : HTy} {T U : Ty} (heap : Heap H) (value : SVal T) (memory : T.mapFree = true) (path : Path T U),
    let grown := value.copyStToM heap memory
    (observe grown.heap path grown.val).map (MVal.copyMToSt grown.heap) = (value.findLiveM path).map SVal.strip
  reference_bounds : ∀ {H : HTy} {T : Ty} {R : RefTy} (heap : Heap H) (value : SVal T)
    (memory : T.mapFree = true) (path : Path T (.ref R))
    (reference : HRef (value.copyStToM heap memory).H' R),
    observe (value.copyStToM heap memory).heap path (value.copyStToM heap memory).val = some reference →
      H.length ≤ reference.id ∧ reference.id < H.length + liveObjectCount value
end Solidity.Backend.MemoryCopies
