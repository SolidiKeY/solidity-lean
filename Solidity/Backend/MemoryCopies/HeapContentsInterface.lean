import Solidity.Backend.MemoryCopies.InterfaceV2
import Solidity.Theory.Typed.MemMirror

/-! Live-content obligation over the existing intrinsic heap and mirror.
No new copy evaluator, graph selector or Source admission rule is introduced. -/
namespace Solidity.Backend.MemoryCopies

/-- Reading an existing member-by-member mirror reconstructs its live storage
contents. Storage-only shadow slots are removed by the published strip operation.
This is not a Source layout or emitted-code correctness certificate. -/
structure MirrorContentsCertificate : Prop where
  contents : ∀ {H : HTy} (hp : Heap H) {T : Ty} (value : SVal T)
    (memory : MVal H T) (frontier : Nat), value.Mirrors hp frontier memory →
      MVal.copyMToSt hp memory = value.strip

end Solidity.Backend.MemoryCopies
