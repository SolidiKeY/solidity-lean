import Solidity.Yul.Views.MemoryImageExtension
import Solidity.Yul.Views.AllocationInventory

namespace Solidity.Yul.Views

theorem byteAlloc_images {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (string : Bool) (bs : List UInt8) (base : Nat) (free : Roadmap.Word) (after : p.free.val≤base)
    (fresh : ∀ a, (h.cells a).isSome → p.address a≠base)
    (fits : base+(MemoryShape.bytes bs.length).size≤free.val)
    (es : List (MixedHeapEntry p)) (prepared : prepareHeapInventory p=.ok es) :
    HeapImageRepresentable (byteAllocPlacement h p string bs base free after fresh fits) := by
  let q := byteAllocPlacement h p string bs base free after fresh fits
  have extension := heapAlloc_owned_extension h p (heapByteData D string bs) (.bytes bs.length)
    (heapByteData_shape D string bs) base free after fresh fits
  intro a τ d found
  by_cases newest : a=h.next
  · subst a
    have entry : (h.alloc ⟨heapByteType string,heapByteData D string bs⟩).1.get h.next=
        some ⟨heapByteType string,heapByteData D string bs⟩ := Source.Heap.alloc_get h _
    have same := Option.some.inj (entry.symm.trans found)
    cases same
    cases string
    · exact ⟨.bytes bs (byteAllocation_length_bound bs base free fits)⟩
    · exact ⟨.string bs (byteAllocation_length_bound bs base free fits)⟩
  · have old : h.get a=some ⟨τ,d⟩ := by rw [Source.Heap.alloc_other h _ newest] at found; exact found
    have present : (h.cells a).isSome := by change (h.get a).isSome=true; rw [old]; rfl
    obtain ⟨e,member,same⟩ := (prepareHeapInventory_ok p es prepared).2.1 a present
    subst a
    have sameData := Option.some.inj (old.symm.trans e.found)
    cases sameData
    exact ⟨e.image.forward q extension⟩

/-- Actual successful old constructor preparation constructs successful NEW
preparation, including old pointer images. No new coverage theorem is input. -/
theorem byteAlloc_prepares {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (string : Bool) (bs : List UInt8) (base : Nat) (free : Roadmap.Word) (after : p.free.val≤base)
    (fresh : ∀ a, (h.cells a).isSome → p.address a≠base)
    (fits : base+(MemoryShape.bytes bs.length).size≤free.val)
    (es : List (MixedHeapEntry p)) (prepared : prepareHeapInventory p=.ok es) :
    let q := byteAllocPlacement h p string bs base free after fresh fits
    prepareHeapInventory q=.ok (generatedHeapEntries q) := by
  dsimp only
  unfold prepareHeapInventory
  rw [representable_no_unsupported _ (byteAlloc_images h p string bs base free after fresh fits es prepared)]

/-- Preserve a real old object's read agreement over its COMPLETE live image,
using its actual extent and physical allocation separation. -/
theorem byteAllocation_old_image_reads {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (string : Bool) (bs : List UInt8) (base : Nat) (free : Roadmap.Word) (after : p.free.val≤base)
    (fresh : ∀ a, (h.cells a).isSome → p.address a≠base)
    (fits : base+(MemoryShape.bytes bs.length).size≤free.val)
    (a : Nat) {τ : Source.STy} (d : Source.Data D τ) (found : h.get a=some ⟨τ,d⟩)
    (image : MemoryImage p d) (m : ByteView) (reads : image.Reads m (p.address a)) :
    let q := byteAllocPlacement h p string bs base free after fresh fits
    let extension := heapAlloc_owned_extension h p (heapByteData D string bs) (.bytes bs.length)
      (heapByteData_shape D string bs) base free after fresh fits
    (image.forward q extension).Reads (byteAllocationView bs base free fits m) (q.address a) := by
  dsimp only
  have present : (h.cells a).isSome := by change (h.get a).isSome=true; rw [found]; rfl
  have address : (byteAllocPlacement h p string bs base free after fresh fits).address a=p.address a :=
    (heapAllocPlacement_old h p (heapByteData D string bs) (.bytes bs.length)
      (heapByteData_shape D string bs) base free after fresh fits a present).1
  rw [address]
  apply (image.forward_reads _ _ _ _).mpr
  apply image.reads_congr _ m _ _ reads
  intro i inside
  exact byteAllocation_old_region h p bs base free after fits m a i present
    (Nat.lt_of_lt_of_le inside (image.fits p a found))

end Solidity.Yul.Views
