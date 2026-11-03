import Solidity.Yul.Views.RetainedHeapAllocation
import Solidity.Yul.Views.HeapAllocationReads

namespace Solidity.Yul.Views

/-- FULL old allocation extents, including a shrunken object's dormant tail,
remain untouched by a new byte/string allocation at/after original free. -/
theorem retainedAllocation_full_region {D} {origin h : Source.Heap D}
    (allocated : Placement origin) (current : Placement h) (history : RetainedAllocation allocated current)
    (bs : List UInt8) (base : Nat) (free : Roadmap.Word) (after : allocated.free.val≤base)
    (fits : base+(MemoryShape.bytes bs.length).size≤free.val) (m : ByteView)
    (a off : Nat) (present : (origin.cells a).isSome) (inside : off<(allocated.shape a).size) :
    byteAllocationView bs base free fits m (current.address a+off)=m (current.address a+off) := by
  rw [history.addresses]
  exact byteAllocation_old_region origin allocated bs base free after fits m a off present inside

/-- The extended origin keeps each original capacity at its actual identity. -/
theorem retainedAllocation_old_capacity {D} {origin h : Source.Heap D}
    (allocated : Placement origin) (current : Placement h) (history : RetainedAllocation allocated current)
    {τ} (data : Source.Data D τ) (shape : MemoryShape) (shaped : HasMemoryShape data shape)
    (base : Nat) (free : Roadmap.Word) (after : allocated.free.val≤base)
    (fresh : ∀ a, (origin.cells a).isSome → allocated.address a≠base)
    (fits : base+shape.size≤free.val) (a : Nat) (present : (origin.cells a).isSome) :
    (heapAllocPlacement origin allocated data shape shaped base free after fresh fits).shape a=allocated.shape a ∧
      (retainedAllocationPlacement allocated current history data shape shaped base free after fresh fits).address a=allocated.address a := by
  constructor
  · exact (heapAllocPlacement_old origin allocated data shape shaped base free after fresh fits a present).2
  · have actual : (h.cells a).isSome := by rw [history.occupancy a]; exact present
    have old := heapAllocPlacement_old h current data shape shaped base free
      (by rw [history.free]; exact after)
      (fun b hb => by rw [history.addresses]; exact fresh b (by rw [← history.occupancy b]; exact hb)) fits a actual
    exact old.1.trans (congrFun history.addresses a)

end Solidity.Yul.Views
