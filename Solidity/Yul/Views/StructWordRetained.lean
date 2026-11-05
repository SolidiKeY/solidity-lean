import Solidity.Yul.Views.StructWordHeap

/-! Existing allocation provenance survives actual same-shape struct field
writes. Whole-map reconstruction uses the current images, while writeback
retains the original allocation snapshot rather than replacing its history. -/
namespace Solidity.Yul.Views.StructWordRetained

theorem history {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (p : Placement h) (prior : RetainedAllocation allocated p)
    (root : Nat) (name : Source.DeclName) (old next : Source.DataList D (D.fields name))
    (found : h.get root=some ⟨.struct .memory name,.struct old⟩) :
    RetainedAllocation allocated (structWrittenPlacement h p root name old next found) := by
  first | (simp only;done) | decide | omega | rfl | skip
  have shaped : HasMemoryShape (.struct (l:=.memory) next) (p.shape root) := by
    have shape := p.typed root _ _ found
    generalize he : p.shape root=sh at shape
    cases shape
    exact .strct next
  exact retainSameShapeWrite allocated p prior root (.struct next) (heap_ty_of_get h root _ _ found) shaped

theorem whole {E Γ} {origin : Source.Heap E.layout} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (allocated : Placement origin) (p : Placement s.2.heap) (prior : RetainedAllocation allocated p)
    (ok : Source.MemOK E H s)
    (supported : ∀ a σ d,s.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ)
    (F : Source.Fr) (horizon root : Nat) (name : Source.DeclName)
    (fields next : Source.DataList E.layout (E.layout.fields name)) (words : List Roadmap.Word)
    (encoded : MemoryFields p fields words)
    (found : s.2.heap.get root=some ⟨.struct .memory name,.struct fields⟩)
    (index : Fin words.length) {τ : Source.STy} (value : Source.Val E.layout τ) (word : Roadmap.Word)
    (newEncoded : MemoryElement p value word) (updated : fields.setNth index.val (.val value)=.ok next)
    (memory : ByteView) (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id))
    (reserved : ReservedOK memory p.free) :
    let after := withSourceHeap s (s.2.heap.write root (.struct next) (heap_ty_of_get _ _ _ _ found))
    let q := structWrittenPlacement s.2.heap p root name fields next found
    let nextHistory := history s.2.heap allocated p prior root name fields next found
    let patch := mstore memory (p.address root+index.val*32) word
    (Source.writeLoc F horizon (.mem root index.val) value).run s=(.ok (),after) ∧
      RetainedAllocation allocated q ∧ encodeMixedHeap q (generatedHeapEntries q) patch=patch ∧
      enumeratedMemoryWriteback after allocated q nextHistory patch=.ok (some (.ok (),after)) := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  let ht := heap_ty_of_get s.2.heap root _ _ found
  let after := withSourceHeap s (s.2.heap.write root (.struct next) ht)
  let q := structWrittenPlacement s.2.heap p root name fields next found
  let patch := mstore memory (p.address root+index.val*32) word
  have current := StructWordHeap.whole H s p ok supported F horizon root name fields next words encoded found
    index value word newEncoded updated memory oldReads reserved
  have nextHistory := history s.2.heap allocated p prior root name fields next found
  have nextSupport : ∀ a σ d,after.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ := by
    intro a σ d actual
    change (s.2.heap.write root (.struct next) ht).get a=some ⟨σ,d⟩ at actual
    by_cases same : a=root
    · subst a
      rw [Source.Heap.write_get] at actual
      cases actual
      exact supported root _ _ found
    · rw [Source.Heap.write_other s.2.heap same] at actual
      exact supported a σ d actual
  have ready := ownerMemOK_prepares_inventory H after q current.2.1 nextSupport
  have writeback := enumeratedMemory_unchanged after allocated q nextHistory patch nextSupport _ ready
  rw [current.2.2.2.1] at writeback
  exact ⟨current.1,nextHistory,current.2.2.2.1,writeback⟩
end Solidity.Yul.Views.StructWordRetained
