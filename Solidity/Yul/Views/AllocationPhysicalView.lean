import Solidity.Yul.Views.AllocationViewImages

namespace Solidity.Yul.Views

/-- A real complete initial inventory's image reads determine reads for any
other constructor-derived image of the same actual lookup. Entries themselves
need not be definitionally equal to a computed inventory. -/
theorem mixedImage_reads_of_coverage {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) (m : ByteView)
    (reads : ∀ e ∈ es, e.image.Reads m (p.address e.id)) (e : MixedHeapEntry p) :
    e.image.Reads m (p.address e.id) := by
  rcases e with ⟨a,τ,d,found,image⟩
  have present : (h.cells a).isSome := by change (h.get a).isSome=true; rw [found]; rfl
  obtain ⟨old,member,same⟩ := coverage a present
  subst a
  have sameData := Option.some.inj (found.symm.trans old.found)
  cases sameData
  exact (old.image.reads_unique image m _).mp (reads old member)

/-- The ACTUAL byte allocation encoder realizes every output image computed
from the actual allocated heap, given actual old image reads. No desired
output-view/read/inverse theorem is an input. -/
theorem byteAllocation_image_reads {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (string : Bool) (bs : List UInt8) (base : Nat) (free : Roadmap.Word) (after : p.free.val≤base)
    (fresh : ∀ a, (h.cells a).isSome → p.address a≠base)
    (fits : base+(MemoryShape.bytes bs.length).size≤free.val)
    (es : List (MixedHeapEntry p)) (prepared : prepareHeapInventory p=.ok es)
    (m : ByteView) (reads : ∀ e ∈ es, e.image.Reads m (p.address e.id))
    (e : MixedHeapEntry (byteAllocPlacement h p string bs base free after fresh fits)) :
    e.image.Reads (byteAllocationView bs base free fits m)
      ((byteAllocPlacement h p string bs base free after fresh fits).address e.id) := by
  let q := byteAllocPlacement h p string bs base free after fresh fits
  have extension := heapAlloc_owned_extension h p (heapByteData D string bs) (.bytes bs.length)
    (heapByteData_shape D string bs) base free after fresh fits
  rcases e with ⟨a,τ,d,found,image⟩
  by_cases newest : a=h.next
  · subst a
    have entry : (h.alloc ⟨heapByteType string,heapByteData D string bs⟩).1.get h.next=
        some ⟨heapByteType string,heapByteData D string bs⟩ := Source.Heap.alloc_get h _
    have same := Option.some.inj (entry.symm.trans found)
    cases same
    have address : q.address h.next=base := if_pos rfl
    change image.Reads _ (q.address h.next)
    rw [address]
    cases string
    · cases image with
      | bytes _ _ => exact ⟨byteAllocation_header bs base free fits m,byteAllocation_payload bs base free fits m⟩
      | words _ _ encoded => cases encoded
    · cases image with
      | string _ _ => exact ⟨byteAllocation_header bs base free fits m,byteAllocation_payload bs base free fits m⟩
      | words _ _ encoded => cases encoded
  · have old : h.get a=some ⟨τ,d⟩ := by rw [Source.Heap.alloc_other h _ newest] at found; exact found
    have present : (h.cells a).isSome := by change (h.get a).isSome=true; rw [old]; rfl
    obtain ⟨e,member,same⟩ := (prepareHeapInventory_ok p es prepared).2.1 a present
    subst a
    have sameData := Option.some.inj (old.symm.trans e.found)
    cases sameData
    have agreement := byteAllocation_old_image_reads h p string bs base free after fresh fits
      e.id e.data e.found e.image m (reads e member)
    exact ((e.image.forward q extension).reads_unique image _ _).mp agreement

/-- Whole physical-map reconstruction, not equality of separate projections.
Every old represented constructor plus the new bytes/string object is covered;
padding, retained tails, gaps and unknown bytes are left exactly as supplied. -/
theorem byteAllocation_computed_view {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (string : Bool) (bs : List UInt8) (base : Nat) (free : Roadmap.Word) (after : p.free.val≤base)
    (fresh : ∀ a, (h.cells a).isSome → p.address a≠base)
    (fits : base+(MemoryShape.bytes bs.length).size≤free.val)
    (es : List (MixedHeapEntry p)) (prepared : prepareHeapInventory p=.ok es)
    (m : ByteView) (reads : ∀ e ∈ es, e.image.Reads m (p.address e.id)) :
    let q := byteAllocPlacement h p string bs base free after fresh fits
    let physical := byteAllocationView bs base free fits m
    prepareHeapInventory q=.ok (generatedHeapEntries q) ∧
      CoversMixedHeap (generatedHeapEntries q) ∧ ((generatedHeapEntries q).map MixedHeapEntry.id).Nodup ∧
      encodeMixedHeap q (generatedHeapEntries q) physical=physical := by
  dsimp only
  have ready := byteAlloc_prepares h p string bs base free after fresh fits es prepared
  have facts := prepareHeapInventory_ok _ _ ready
  exact ⟨ready,facts.2.1,facts.2.2,encodeMixedHeap_unchanged _ _ _
    (fun e _ => byteAllocation_image_reads h p string bs base free after fresh fits es prepared m reads e)⟩

end Solidity.Yul.Views
