import Solidity.Yul.Views.ObjectAllocationImages

namespace Solidity.Yul.Views

/-- Actual generic new-object preparation plus real initial reads determines
all actual output image reads, including pointer-valued aggregate members. -/
theorem objectAllocationView_image_reads {D : Source.Layout} (h : Source.Heap D) (p : Placement h) {τ : Source.STy}
    (data : Source.Data D τ) (memory : τ.loc?=some .memory) (shape : MemoryShape) (shaped : HasMemoryShape data shape)
    (base : Nat) (free : Roadmap.Word) (after : p.free.val≤base)
    (fresh : ∀ a, (h.cells a).isSome → p.address a≠base) (fits : base+shape.size≤free.val)
    (es : List (MixedHeapEntry p)) (prepared : prepareHeapInventory p=.ok es)
    (m raw : ByteView) (reads : ∀ e ∈ es, e.image.Reads m (p.address e.id))
    (step : objectAllocationView h p data memory shape shaped base free after fresh fits m=some raw)
    (e : MixedHeapEntry (heapAllocPlacement h p data shape shaped base free after fresh fits)) :
    e.image.Reads raw ((heapAllocPlacement h p data shape shaped base free after fresh fits).address e.id) := by
  let q := heapAllocPlacement h p data shape shaped base free after fresh fits
  have extension := heapAlloc_owned_extension h p data shape shaped base free after fresh fits
  rcases e with ⟨a,σ,x,found,image⟩
  by_cases newest : a=h.next
  · subst a
    have entry : (h.alloc ⟨τ,data⟩).1.get h.next=some ⟨τ,data⟩ := Source.Heap.alloc_get h _
    have sameData := Option.some.inj (entry.symm.trans found)
    cases sameData
    have address : q.address h.next=base := if_pos rfl
    change image.Reads raw (q.address h.next)
    rw [address]
    unfold objectAllocationView at step
    obtain ⟨newImage,ready,same⟩ := Option.map_eq_some_iff.mp step
    subst raw
    exact (newImage.reads_unique image _ base).mp (newImage.encode_reads _ base)
  · have old : h.get a=some ⟨σ,x⟩ := by rw [Source.Heap.alloc_other h _ newest] at found; exact found
    have present : (h.cells a).isSome := by change (h.get a).isSome=true; rw [old]; rfl
    obtain ⟨e,member,same⟩ := (prepareHeapInventory_ok p es prepared).2.1 a present
    subst a
    have sameData := Option.some.inj (old.symm.trans e.found)
    cases sameData
    have agreement := objectAllocationView_old_reads h p data memory shape shaped base free after fresh fits
      e.id e.data e.found e.image m raw (reads e member) step
    exact ((e.image.forward q extension).reads_unique image _ _).mp agreement

/-- Complete raw-map reconstruction for every successful actual generic object
preparation, including sparse heaps and real existing pointer child ownership. -/
theorem objectAllocationView_computed {D : Source.Layout} (h : Source.Heap D) (p : Placement h) {τ : Source.STy}
    (data : Source.Data D τ) (memory : τ.loc?=some .memory) (shape : MemoryShape) (shaped : HasMemoryShape data shape)
    (base : Nat) (free : Roadmap.Word) (after : p.free.val≤base)
    (fresh : ∀ a, (h.cells a).isSome → p.address a≠base) (fits : base+shape.size≤free.val)
    (es : List (MixedHeapEntry p)) (prepared : prepareHeapInventory p=.ok es)
    (m raw : ByteView) (reads : ∀ e ∈ es, e.image.Reads m (p.address e.id))
    (step : objectAllocationView h p data memory shape shaped base free after fresh fits m=some raw) :
    let q := heapAllocPlacement h p data shape shaped base free after fresh fits
    prepareHeapInventory q=.ok (generatedHeapEntries q) ∧ CoversMixedHeap (generatedHeapEntries q) ∧
      ((generatedHeapEntries q).map MixedHeapEntry.id).Nodup ∧ encodeMixedHeap q (generatedHeapEntries q) raw=raw := by
  dsimp only
  have ready := objectAllocationView_prepares h p data memory shape shaped base free after fresh fits es prepared m raw step
  have facts := prepareHeapInventory_ok _ _ ready
  exact ⟨ready,facts.2.1,facts.2.2,encodeMixedHeap_unchanged _ _ _
    (fun e _ => objectAllocationView_image_reads h p data memory shape shaped base free after fresh fits es prepared m raw reads step e)⟩

/-- Actual typed logical word reads from the resulting heap agree with the
same raw map, without reducing proof casts or using a native oracle. -/
theorem objectAllocationView_source_word {D : Source.Layout} (h : Source.Heap D) (p : Placement h) {τ : Source.STy}
    (data : Source.Data D τ) (memory : τ.loc?=some .memory) (shape : MemoryShape) (shaped : HasMemoryShape data shape)
    (base : Nat) (free : Roadmap.Word) (after : p.free.val≤base)
    (fresh : ∀ a, (h.cells a).isSome → p.address a≠base) (fits : base+shape.size≤free.val)
    (es : List (MixedHeapEntry p)) (prepared : prepareHeapInventory p=.ok es)
    (m raw : ByteView) (reads : ∀ e ∈ es, e.image.Reads m (p.address e.id))
    (step : objectAllocationView h p data memory shape shaped base free after fresh fits m=some raw)
    (a : Nat) (σ : Source.STy) (x : Source.Data D σ)
    (found : (h.alloc ⟨τ,data⟩).1.get a=some ⟨σ,x⟩) (off : Nat) (w : Roadmap.Word)
    (read : ObjectWord (heapAllocPlacement h p data shape shaped base free after fresh fits).address x off w) :
    mload raw ((heapAllocPlacement h p data shape shaped base free after fresh fits).address a+off)=w := by
  have facts := objectAllocationView_computed h p data memory shape shaped base free after fresh fits es prepared m raw reads step
  have word := encodeMixedHeap_source_word _ _ facts.2.2.1 facts.2.1 raw a σ x found off w read
  rw [facts.2.2.2] at word
  exact word

theorem objectAllocationView_reserved {D : Source.Layout} (h : Source.Heap D) (p : Placement h) {τ : Source.STy}
    (data : Source.Data D τ) (memory : τ.loc?=some .memory) (shape : MemoryShape) (shaped : HasMemoryShape data shape)
    (base : Nat) (free : Roadmap.Word) (after : p.free.val≤base)
    (fresh : ∀ a, (h.cells a).isSome → p.address a≠base) (fits : base+shape.size≤free.val)
    (m raw : ByteView) (reserved : ReservedOK m p.free)
    (step : objectAllocationView h p data memory shape shaped base free after fresh fits m=some raw) : ReservedOK raw free := by
  unfold objectAllocationView at step
  obtain ⟨image,ready,same⟩ := Option.map_eq_some_iff.mp step
  subst raw
  apply image.reserved _ base free (Nat.le_trans p.free_start after)
  constructor
  · exact congrArg Fin.val (mload_mstore m 64 free)
  · intro i
    rw [mstore_outside m 64 (96+i.val) free (by omega)]
    exact reserved.2 i

end Solidity.Yul.Views
