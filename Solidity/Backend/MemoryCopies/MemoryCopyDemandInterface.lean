import Solidity.Backend.MemoryCopies.TraversalWords
import Solidity.Backend.MemoryCopies.DeepCopyContents

/-! Actual intrinsic memory snapshot/copy demand, distinct from alias rebinding.
No emitted compiler or Source graph-admission premise is postulated. -/
namespace Solidity.Backend.MemoryCopies

structure MemoryCopyDemandCertificate {H : HTy} {R : RefTy} (heap : Heap H)
    (input : HRef H R) (memory : (Ty.ref R).mapFree = true) : Prop where
  growth :
    let snapshot := MVal.copyMToSt heap (T := .ref R) input
    heapWords (snapshot.copyStToM heap memory).heap = heapWords heap + liveWordCount snapshot
  positive : 0 < liveWordCount (MVal.copyMToSt heap (T := .ref R) input)
  recopy :
    let snapshot := MVal.copyMToSt heap (T := .ref R) input
    let copied := snapshot.copyStToM heap memory
    liveWordCount (MVal.copyMToSt copied.heap (T := .ref R) copied.val) = liveWordCount snapshot

structure MemoryAliasDemandCertificate : Prop where
  alias : ∀ {C : Contract} {Γ : Ctx} {R : RefTy} (state : State C Γ)
    (path : MPath C Γ (.ref R)) (destination : Idx Γ (.mem R)) (reference : HRef state.H R),
    path.mvalT state = .ok reference →
    TRun.rebindMem destination (.alias path) state =
      .ok ⟨state.setLocal destination (some reference), List.prefix_refl _⟩ ∧
    heapWords (state.setLocal destination (some reference)).heap = heapWords state.heap

end Solidity.Backend.MemoryCopies
