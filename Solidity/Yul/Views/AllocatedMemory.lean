import Solidity.Yul.Views.AllocationInventory

namespace Solidity.Yul.Views

/-- End-to-end actual byte/string allocation to computed complete supported
inventory and unchanged whole-state writeback, retaining the ORIGINAL extent
history. The encoded current inventory is constructed, never a supplied final
view law. Arbitrary raw-memory decode/reachability/refinement is not asserted. -/
theorem retainedByteAllocation_inventory {E Γ} {origin : Source.Heap E.layout}
    (H : Source.HeapTy) (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (string : Bool) (bs : List UInt8)
    (base : Nat) (free : Roadmap.Word) (after : allocated.free.val≤base)
    (fresh : ∀ a, (origin.cells a).isSome → allocated.address a≠base)
    (fits : base+(MemoryShape.bytes bs.length).size≤free.val)
    (residual : ByteView) (ok : Source.MemOK E H s)
    (supported : ∀ a τ d, s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ) :
    let data := heapByteData E.layout string bs
    let q : Placement (byteAllocatedState s string bs).2.heap := retainedAllocationPlacement (h := s.2.heap) allocated p history data (.bytes bs.length)
      (heapByteData_shape E.layout string bs) base free after fresh fits
    let nextOrigin := heapAllocPlacement origin allocated data (.bytes bs.length)
      (heapByteData_shape E.layout string bs) base free after fresh fits
    let nextHistory := retainAllocated (h := s.2.heap) allocated p history data (.bytes bs.length)
      (heapByteData_shape E.layout string bs) base free after fresh fits
    let nextState := byteAllocatedState s string bs
    (Source.allocRef data).run s=(.ok (Source.Val.memRef (heapByteType_memory string) s.2.heap.next),nextState) ∧
      Source.MemOK E H nextState ∧
      prepareHeapInventory q=.ok (generatedHeapEntries q) ∧
      CoversMixedHeap (generatedHeapEntries q) ∧ ((generatedHeapEntries q).map MixedHeapEntry.id).Nodup ∧
      (generatedHeapEntries q).map MixedHeapEntry.id=(generatedHeapEntries p).map MixedHeapEntry.id ++ [s.2.heap.next] ∧
      enumeratedMemoryView q residual=.ok (encodeMixedHeap q (generatedHeapEntries q) residual) ∧
      enumeratedMemoryWriteback nextState nextOrigin q nextHistory (encodeMixedHeap q (generatedHeapEntries q) residual)=
        .ok (some (.ok (),nextState)) := by
  dsimp only
  let data := heapByteData E.layout string bs
  let q : Placement (byteAllocatedState s string bs).2.heap := retainedAllocationPlacement (h := s.2.heap) allocated p history data (.bytes bs.length)
    (heapByteData_shape E.layout string bs) base free after fresh fits
  let nextOrigin := heapAllocPlacement origin allocated data (.bytes bs.length)
    (heapByteData_shape E.layout string bs) base free after fresh fits
  let nextHistory := retainAllocated (h := s.2.heap) allocated p history data (.bytes bs.length)
    (heapByteData_shape E.layout string bs) base free after fresh fits
  have safe := byteAllocRef_MemOK s string bs H ok
  have support := heapAlloc_inventory_supported s.2.heap data
    (show InventoryTypeSupported E (heapByteType string) by cases string <;> trivial) supported
  have ready := byteAllocated_inventory H s p string bs q ok supported
  have whole := ownerMemory_unchanged H (byteAllocatedState s string bs) nextOrigin q nextHistory residual safe support
  exact ⟨byteAllocRef_run s string bs,safe,ready.1,ready.2.1,ready.2.2.1,ready.2.2.2,whole.1,whole.2⟩

end Solidity.Yul.Views
