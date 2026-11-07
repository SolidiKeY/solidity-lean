import Solidity.Yul.Views.MixedNominalAllocation

namespace Solidity.Yul.Views.MixedNominalInventory

/-- Generic supported ordinary allocation, with computed physical preparation,
actual Source.allocRef, every-original-H MemOK, complete map/source writeback
and ORIGINAL retained capacities. New child ownership is checked against the
OLD heap. No final image/view/inverse/safety witness is a caller premise. -/
theorem retained_allocation_physical {E Γ} {origin : Source.Heap E.layout}
    (H : Source.HeapTy) (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) {τ : Source.STy} (data : Source.Data E.layout τ)
    (memory : τ.loc?=some .memory) (shape : MemoryShape) (shaped : HasMemoryShape data shape)
    (inner : Source.Data.Inner (E := E) data) (valid : Source.DataOK E s.2.heap.ty data)
    (supportedNew : TypeSupported E τ)
    (base : Nat) (free : Roadmap.Word) (after : allocated.free.val≤base)
    (fresh : ∀ a, (origin.cells a).isSome → allocated.address a≠base) (fits : base+shape.size≤free.val)
    (m : ByteView) (ok : Source.MemOK E H s)
    (supportedOld : ∀ a σ d, s.2.heap.get a=some ⟨σ,d⟩ → TypeSupported E σ)
    (reads : ∀ e ∈ generatedHeapEntries p, e.image.Reads m (p.address e.id)) (reserved : ReservedOK m p.free) :
    let currentAfter : p.free.val≤base := by rw [history.free]; exact after
    let currentFresh : ∀ a, (s.2.heap.cells a).isSome → p.address a≠base := fun a present => by
      rw [history.addresses]; exact fresh a (by rw [← history.occupancy a]; exact present)
    let q : Placement (objectAllocatedState s data).2.heap :=
      retainedAllocationPlacement (h := s.2.heap) allocated p history data shape shaped base free after fresh fits
    let nextOrigin := heapAllocPlacement origin allocated data shape shaped base free after fresh fits
    let nextHistory := retainAllocated (h := s.2.heap) allocated p history data shape shaped base free after fresh fits
    let nextState := objectAllocatedState s data
    ∃ raw, objectAllocationView s.2.heap p data memory shape shaped base free currentAfter currentFresh fits m=some raw ∧
      (Source.allocRef data).run s=(.ok (Source.Val.memRef memory s.2.heap.next),nextState) ∧
      Source.MemOK E H nextState ∧ prepareHeapInventory q=.ok (generatedHeapEntries q) ∧
      CoversMixedHeap (generatedHeapEntries q) ∧ ((generatedHeapEntries q).map MixedHeapEntry.id).Nodup ∧
      encodeMixedHeap q (generatedHeapEntries q) raw=raw ∧
      writeback nextState nextOrigin q nextHistory (generatedHeapEntries q) raw=some (.ok (),nextState) ∧ ReservedOK raw free := by
  dsimp only
  have currentAfter : p.free.val≤base := by rw [history.free]; exact after
  have currentFresh : ∀ a, (s.2.heap.cells a).isSome → p.address a≠base := by
    intro a present
    rw [history.addresses]
    exact fresh a (by rw [← history.occupancy a]; exact present)
  let q : Placement (objectAllocatedState s data).2.heap :=
    retainedAllocationPlacement (h := s.2.heap) allocated p history data shape shaped base free after fresh fits
  let nextOrigin := heapAllocPlacement origin allocated data shape shaped base free after fresh fits
  let nextHistory := retainAllocated (h := s.2.heap) allocated p history data shape shaped base free after fresh fits
  have complete : (objectAllocationView s.2.heap p data memory shape shaped base free currentAfter currentFresh fits m).isSome := by
    unfold objectAllocationView
    rw [Option.isSome_map]
    exact image_prepared _ _ _ data (Source.Heap.alloc_get s.2.heap _) supportedNew inner
      (Source.DataOK.mono (Source.Heap.alloc_le s.2.heap ⟨τ,data⟩) valid)
  obtain ⟨raw,step⟩ := Option.isSome_iff_exists.mp complete
  have prepared := owner_prepares H s p ok supportedOld
  have physical := objectAllocationView_computed s.2.heap p data memory shape shaped base free currentAfter currentFresh fits
    _ prepared m raw reads step
  have ready : prepareHeapInventory q=.ok (generatedHeapEntries q) := physical.1
  have whole : encodeMixedHeap q (generatedHeapEntries q) raw=raw := physical.2.2.2
  have top : Source.Data.Top (E := E) data := by cases shaped <;> trivial
  have safe := (objectAllocRef_MemOK H s data memory top inner valid ok).1
  have support := allocation_profile s.2.heap data supportedNew supportedOld
  have unchanged := (generated_roundtrip H (objectAllocatedState s data) nextOrigin q nextHistory safe support raw).2
  rw [whole] at unchanged
  exact ⟨raw,step,objectAllocRef_run s data memory,safe,ready,physical.2.1,physical.2.2.1,whole,unchanged,
    objectAllocationView_reserved s.2.heap p data memory shape shaped base free currentAfter currentFresh fits m raw reserved step⟩

end Solidity.Yul.Views.MixedNominalInventory
