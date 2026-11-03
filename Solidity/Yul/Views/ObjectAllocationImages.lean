import Solidity.Yul.Views.ObjectMemoryAllocation

namespace Solidity.Yul.Views

/-- General actual allocation image extension. The new image is intrinsic
constructor evidence; concrete entrypoints COMPUTE it via prepareHeapImage. -/
theorem heapAlloc_images {D : Source.Layout} (h : Source.Heap D) (p : Placement h) {τ : Source.STy}
    (data : Source.Data D τ) (shape : MemoryShape) (shaped : HasMemoryShape data shape)
    (base : Nat) (free : Roadmap.Word) (after : p.free.val≤base)
    (fresh : ∀ a, (h.cells a).isSome → p.address a≠base) (fits : base+shape.size≤free.val)
    (es : List (MixedHeapEntry p)) (prepared : prepareHeapInventory p=.ok es)
    (newImage : MemoryImage (heapAllocPlacement h p data shape shaped base free after fresh fits) data) :
    HeapImageRepresentable (heapAllocPlacement h p data shape shaped base free after fresh fits) := by
  let q := heapAllocPlacement h p data shape shaped base free after fresh fits
  have extension := heapAlloc_owned_extension h p data shape shaped base free after fresh fits
  intro a σ x found
  by_cases newest : a=h.next
  · subst a
    have entry : (h.alloc ⟨τ,data⟩).1.get h.next=some ⟨τ,data⟩ := Source.Heap.alloc_get h _
    have same := Option.some.inj (entry.symm.trans found)
    cases same
    exact ⟨newImage⟩
  · have old : h.get a=some ⟨σ,x⟩ := by rw [Source.Heap.alloc_other h _ newest] at found; exact found
    have present : (h.cells a).isSome := by change (h.get a).isSome=true; rw [old]; rfl
    obtain ⟨e,member,same⟩ := (prepareHeapInventory_ok p es prepared).2.1 a present
    subst a
    have sameData := Option.some.inj (old.symm.trans e.found)
    cases sameData
    exact ⟨e.image.forward q extension⟩

/-- A successful ACTUAL new-object preparation constructs all new heap images;
no old/new inventory or coverage/image-read adequacy theorem is assumed. -/
theorem objectAllocationView_prepares {D : Source.Layout} (h : Source.Heap D) (p : Placement h) {τ : Source.STy}
    (data : Source.Data D τ) (memory : τ.loc?=some .memory) (shape : MemoryShape) (shaped : HasMemoryShape data shape)
    (base : Nat) (free : Roadmap.Word) (after : p.free.val≤base)
    (fresh : ∀ a, (h.cells a).isSome → p.address a≠base) (fits : base+shape.size≤free.val)
    (es : List (MixedHeapEntry p)) (prepared : prepareHeapInventory p=.ok es)
    (m raw : ByteView) (step : objectAllocationView h p data memory shape shaped base free after fresh fits m=some raw) :
    let q := heapAllocPlacement h p data shape shaped base free after fresh fits
    prepareHeapInventory q=.ok (generatedHeapEntries q) := by
  unfold objectAllocationView at step
  obtain ⟨image,ready,same⟩ := Option.map_eq_some_iff.mp step
  dsimp only
  unfold prepareHeapInventory
  rw [representable_no_unsupported _ (heapAlloc_images h p data shape shaped base free after fresh fits es prepared image)]

/-- Preserve each old image under the actual prepared new object's encoder and
FMP update, over its entire old live region. -/
theorem objectAllocationView_old_reads {D : Source.Layout} (h : Source.Heap D) (p : Placement h) {τ : Source.STy}
    (data : Source.Data D τ) (memory : τ.loc?=some .memory) (shape : MemoryShape) (shaped : HasMemoryShape data shape)
    (base : Nat) (free : Roadmap.Word) (after : p.free.val≤base)
    (fresh : ∀ a, (h.cells a).isSome → p.address a≠base) (fits : base+shape.size≤free.val)
    (a : Nat) {σ : Source.STy} (old : Source.Data D σ) (found : h.get a=some ⟨σ,old⟩)
    (image : MemoryImage p old) (m raw : ByteView) (reads : image.Reads m (p.address a))
    (step : objectAllocationView h p data memory shape shaped base free after fresh fits m=some raw) :
    let q := heapAllocPlacement h p data shape shaped base free after fresh fits
    let extension := heapAlloc_owned_extension h p data shape shaped base free after fresh fits
    (image.forward q extension).Reads raw (q.address a) := by
  unfold objectAllocationView at step
  obtain ⟨newImage,ready,same⟩ := Option.map_eq_some_iff.mp step
  subst raw
  dsimp only
  have present : (h.cells a).isSome := by change (h.get a).isSome=true; rw [found]; rfl
  rw [(heapAllocPlacement_old h p data shape shaped base free after fresh fits a present).1]
  apply (image.forward_reads _ _ _ _).mpr
  apply image.reads_congr _ m _ _ reads
  intro i inside
  have span := image.fits p a found
  have ends := p.ends a present
  have starts := p.starts a present
  rw [newImage.residual _ base _ (Or.inl (by omega)),mstore_outside m 64 _ free (by omega)]

/-- The actual written image span is returned constructively; all padding and
unknown bytes outside it and the FMP are preserved EXACTLY. -/
theorem objectAllocationView_region {D : Source.Layout} (h : Source.Heap D) (p : Placement h) {τ : Source.STy}
    (data : Source.Data D τ) (memory : τ.loc?=some .memory) (shape : MemoryShape) (shaped : HasMemoryShape data shape)
    (base : Nat) (free : Roadmap.Word) (after : p.free.val≤base)
    (fresh : ∀ a, (h.cells a).isSome → p.address a≠base) (fits : base+shape.size≤free.val)
    (m raw : ByteView) (step : objectAllocationView h p data memory shape shaped base free after fresh fits m=some raw) :
    let q := heapAllocPlacement h p data shape shaped base free after fresh fits
    ∃ image : MemoryImage q data,
      prepareHeapImage q h.next τ data (Source.Heap.alloc_get h _)=some image ∧ image.span≤shape.size ∧
      raw=image.encode (mstore m 64 free) base ∧
      ∀ i, (i<base ∨ base+image.span≤i) → (i<64 ∨ 96≤i) → raw i=m i := by
  unfold objectAllocationView at step
  obtain ⟨image,ready,same⟩ := Option.map_eq_some_iff.mp step
  subst raw
  dsimp only
  have bound := image.fits (heapAllocPlacement h p data shape shaped base free after fresh fits) h.next (Source.Heap.alloc_get h _)
  change image.span≤(if h.next=h.next then shape else p.shape h.next).size at bound
  rw [if_pos rfl] at bound
  refine ⟨image,ready,bound,rfl,?_⟩
  intro i outside notFree
  rw [image.residual _ base i outside,mstore_outside m 64 i free (by omega)]

end Solidity.Yul.Views
