import Solidity.Yul.Views.AllocationPhysicalView
import Solidity.Yul.Views.AllocatedMemory

namespace Solidity.Yul.Views

/-- Concrete source allocation, actual physical encoder, computed complete
inventory and whole-state writeback are connected for EVERY real initial owner
typing H. Initial read/ReservedOK agreement and allocation geometry are real
premises; no final map/safety/inverse law or compiler choice theorem is assumed. -/
theorem retainedByteAllocation_physical {E Γ} {origin : Source.Heap E.layout}
    (H : Source.HeapTy) (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (string : Bool) (bs : List UInt8)
    (base : Nat) (free : Roadmap.Word) (after : allocated.free.val≤base)
    (fresh : ∀ a, (origin.cells a).isSome → allocated.address a≠base)
    (fits : base+(MemoryShape.bytes bs.length).size≤free.val)
    (m : ByteView) (ok : Source.MemOK E H s)
    (supported : ∀ a τ d, s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (reads : ∀ e ∈ generatedHeapEntries p, e.image.Reads m (p.address e.id))
    (reserved : ReservedOK m p.free) :
    let data := heapByteData E.layout string bs
    let q : Placement (byteAllocatedState s string bs).2.heap :=
      retainedAllocationPlacement (h := s.2.heap) allocated p history data (.bytes bs.length)
        (heapByteData_shape E.layout string bs) base free after fresh fits
    let nextOrigin := heapAllocPlacement origin allocated data (.bytes bs.length)
      (heapByteData_shape E.layout string bs) base free after fresh fits
    let nextHistory := retainAllocated (h := s.2.heap) allocated p history data (.bytes bs.length)
      (heapByteData_shape E.layout string bs) base free after fresh fits
    let nextState := byteAllocatedState s string bs
    let physical := byteAllocationView bs base free fits m
    (Source.allocRef data).run s=(.ok (Source.Val.memRef (heapByteType_memory string) s.2.heap.next),nextState) ∧
      Source.MemOK E H nextState ∧
      prepareHeapInventory q=.ok (generatedHeapEntries q) ∧
      CoversMixedHeap (generatedHeapEntries q) ∧ ((generatedHeapEntries q).map MixedHeapEntry.id).Nodup ∧
      encodeMixedHeap q (generatedHeapEntries q) physical=physical ∧
      enumeratedMemoryWriteback nextState nextOrigin q nextHistory physical=.ok (some (.ok (),nextState)) ∧
      ReservedOK physical free ∧
      ∀ i, (i<base ∨ base+32+bs.length≤i) → (i<64 ∨ 96≤i) → physical i=m i := by
  dsimp only
  let data := heapByteData E.layout string bs
  let q : Placement (byteAllocatedState s string bs).2.heap :=
    retainedAllocationPlacement (h := s.2.heap) allocated p history data (.bytes bs.length)
      (heapByteData_shape E.layout string bs) base free after fresh fits
  let nextOrigin := heapAllocPlacement origin allocated data (.bytes bs.length)
    (heapByteData_shape E.layout string bs) base free after fresh fits
  let nextHistory := retainAllocated (h := s.2.heap) allocated p history data (.bytes bs.length)
    (heapByteData_shape E.layout string bs) base free after fresh fits
  have currentAfter : p.free.val≤base := by rw [history.free]; exact after
  have currentFresh : ∀ a, (s.2.heap.cells a).isSome → p.address a≠base := by
    intro a present
    rw [history.addresses]
    exact fresh a (by rw [← history.occupancy a]; exact present)
  have prepared := ownerMemOK_prepares_inventory H s p ok supported
  have physicalFacts := byteAllocation_computed_view s.2.heap p string bs base free currentAfter currentFresh fits
    (generatedHeapEntries p) prepared m reads
  have ready : prepareHeapInventory q=.ok (generatedHeapEntries q) := physicalFacts.1
  have whole : encodeMixedHeap q (generatedHeapEntries q) (byteAllocationView bs base free fits m)=
      byteAllocationView bs base free fits m := physicalFacts.2.2.2
  have safe := byteAllocRef_MemOK s string bs H ok
  have support := heapAlloc_inventory_supported s.2.heap data
    (show InventoryTypeSupported E (heapByteType string) by cases string <;> trivial) supported
  have unchanged := enumeratedMemory_unchanged (byteAllocatedState s string bs) nextOrigin q nextHistory
    (byteAllocationView bs base free fits m) support _ ready
  rw [whole] at unchanged
  have start : 128≤base := Nat.le_trans p.free_start currentAfter
  exact ⟨byteAllocRef_run s string bs,safe,ready,physicalFacts.2.1,physicalFacts.2.2.1,whole,unchanged,
    byteAllocation_reserved bs base free p.free fits m start reserved,
    fun i outside notFree => byteAllocation_residual bs base free fits m i outside notFree⟩

end Solidity.Yul.Views
