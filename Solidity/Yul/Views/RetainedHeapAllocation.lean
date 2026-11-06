import Solidity.Yul.Views.HeapAllocationCommute

namespace Solidity.Yul.Views

/-- Rebuild EVERY actual old write on the extended actual origin. The output
choice equations are proved, not supplied input coverage/inverse laws. -/
theorem retain_allocate_exists {D} {origin h : Source.Heap D} {allocated : Placement origin}
    {current : Placement h} (history : RetainedAllocation allocated current)
    {τ} (data : Source.Data D τ) (newShape : MemoryShape) (shaped : HasMemoryShape data newShape)
    (base : Nat) (free : Roadmap.Word) (after : allocated.free.val ≤ base)
    (fresh : ∀ a, (origin.cells a).isSome → allocated.address a≠base)
    (fits : base+newShape.size≤free.val) :
    ∃ q : Placement (h.alloc ⟨τ,data⟩).1,
      RetainedAllocation (heapAllocPlacement origin allocated data newShape shaped base free after fresh fits) q ∧
      q.address=(fun a => if a=h.next then base else current.address a) ∧
      q.shape=(fun a => if a=h.next then newShape else current.shape a) ∧ q.free=free := by
  let allocatedNext := heapAllocPlacement origin allocated data newShape shaped base free after fresh fits
  change ∃ q : Placement (h.alloc ⟨τ,data⟩).1, RetainedAllocation allocatedNext q ∧ _
  induction history with
  | initial => exact ⟨allocatedNext,.initial,rfl,rfl,rfl⟩
  | @written h current geometry prior a σ d typed shape shapeOK capacity ih =>
    rcases ih with ⟨q,lineage,addresses,shapes,freeEq⟩
    have present := heap_type_present h a σ typed
    have different := occupied_ne_next h a present
    have originalDifferent : a≠origin.next := by rw [← prior.next]; exact different
    have capacityNext : shape.size≤(allocatedNext.shape a).size := by
      change shape.size≤(if a=origin.next then newShape else allocated.shape a).size
      rw [if_neg originalDifferent]
      exact capacity
    let targetType := heap_alloc_old_type h ⟨τ,data⟩ a σ typed
    let written := retainedWritePlacement allocatedNext q lineage a d targetType shape shapeOK capacityNext
    have writtenLineage : RetainedAllocation allocatedNext written :=
      retainWritten allocatedNext q lineage a d targetType shape shapeOK capacityNext
    have sameHeap := heap_write_alloc h ⟨τ,data⟩ a d typed
    let finalPlacement := sameHeap.symm ▸ written
    have choices := placement_cast_choices sameHeap.symm written
    refine ⟨finalPlacement,retainedAllocation_cast sameHeap.symm written writtenLineage,?_,?_,?_⟩
    · exact choices.1.trans addresses
    · rw [choices.2.1]
      change (fun b => if b=a then shape else q.shape b)=
        (fun b => if b=h.next then newShape else if b=a then shape else current.shape b)
      funext b
      rw [congrFun shapes b]
      by_cases target : b=a
      · subst b
        simp only [if_true,if_neg different]
      · by_cases newest : b=h.next
        · subst b
          simp only [if_neg target,if_true]
        · simp only [if_neg target,if_neg newest]
    · exact choices.2.2.trans freeEq

/-- The executable current placement uses the same actual allocation choice.
All current-side premises follow from the existing real history. -/
def retainedAllocationPlacement {D} {origin h : Source.Heap D}
    (allocated : Placement origin) (current : Placement h) (history : RetainedAllocation allocated current)
    {τ} (data : Source.Data D τ) (shape : MemoryShape) (shaped : HasMemoryShape data shape)
    (base : Nat) (free : Roadmap.Word) (after : allocated.free.val≤base)
    (fresh : ∀ a, (origin.cells a).isSome → allocated.address a≠base)
    (fits : base+shape.size≤free.val) : Placement (h.alloc ⟨τ,data⟩).1 :=
  heapAllocPlacement h current data shape shaped base free
    (by rw [history.free]; exact after)
    (fun a present => by
      rw [history.addresses]
      exact fresh a (by rw [← history.occupancy a]; exact present)) fits

/-- Exact lineage on the canonical constructed output, including old capacities.
Neither the original history nor its origin is reset to the shrunken current heap. -/
theorem retainAllocated {D} {origin h : Source.Heap D}
    (allocated : Placement origin) (current : Placement h) (history : RetainedAllocation allocated current)
    {τ} (data : Source.Data D τ) (shape : MemoryShape) (shaped : HasMemoryShape data shape)
    (base : Nat) (free : Roadmap.Word) (after : allocated.free.val≤base)
    (fresh : ∀ a, (origin.cells a).isSome → allocated.address a≠base)
    (fits : base+shape.size≤free.val) :
    RetainedAllocation (heapAllocPlacement origin allocated data shape shaped base free after fresh fits)
      (retainedAllocationPlacement allocated current history data shape shaped base free after fresh fits) := by
  obtain ⟨q,lineage,addresses,shapes,freeEq⟩ := retain_allocate_exists history data shape shaped base free after fresh fits
  have same : q=retainedAllocationPlacement allocated current history data shape shaped base free after fresh fits :=
    placement_choices_ext _ _ addresses shapes freeEq
  rw [← same]
  exact lineage

end Solidity.Yul.Views
