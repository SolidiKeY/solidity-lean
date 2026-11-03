import Solidity.Yul.Views.ScratchHeapTransport
import Solidity.Yul.Views.EnumeratedMemory

namespace Solidity.Yul.Views

/-- Constructive whole-state/writeback and WHOLE-map realization after a
scratch copy. Inventory preparation/coverage is DERIVED from actual owner
MemOK and the existing constructor support profile, not supplied as a result
law. Ordinary Placement and original retained ownership remain real premises. -/
theorem ownerMemory_scratch_writeback {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (H : Source.HeapTy) (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (residual src : ByteView)
    (destination start size : Nat) (scratch : destination+size≤64) (ok : Source.MemOK E H s)
    (supported : ∀ a ty d, s.2.heap.get a=some ⟨ty,d⟩ → InventoryTypeSupported E ty) :
    enumeratedMemoryView p (copyBytes residual src destination start size)=
      .ok (copyBytes (encodeMixedHeap p (generatedHeapEntries p) residual) src destination start size) ∧
    enumeratedMemoryWriteback s allocated p history
      (copyBytes (encodeMixedHeap p (generatedHeapEntries p) residual) src destination start size)=
        .ok (some (.ok (),s)) := by
  rw [encodeMixedHeap_scratch_copy p (generatedHeapEntries p) residual src destination start size scratch]
  exact ownerMemory_unchanged H s allocated p history _ ok supported

end Solidity.Yul.Views
