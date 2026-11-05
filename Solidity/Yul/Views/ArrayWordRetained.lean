import Solidity.Yul.Views.ArrayWordHeap

/-! Existing allocation provenance survives actual same-shape array-member
writes. This consumes the published retainSameShapeWrite theorem rather than
replacing historical capacity with a fresh initial snapshot. -/
namespace Solidity.Yul.Views.ArrayWordRetained
open ArrayWordStore

theorem history {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (p : Placement h) (prior : RetainedAllocation allocated p)
    (root : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat) (hl : ∀ x,k=some x → x=n)
    (old values : Fin n → Source.Val D τ)
    (found : h.get root=some ⟨_,memberArrayData D τ k n hl old⟩) :
    RetainedAllocation allocated (memberArrayWrittenPlacement h p root τ k n hl old values found) := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact retainSameShapeWrite allocated p prior root (memberArrayData D τ k n hl values)
    (heap_ty_of_get h root _ _ found) (by rw [memberArray_shape h p root τ k n hl old found];exact .array _ _ _)

theorem whole {E Γ} {origin : Source.Heap E.layout} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (allocated : Placement origin) (p : Placement s.2.heap) (prior : RetainedAllocation allocated p)
    (ok : Source.MemOK E H s)
    (supported : ∀ a σ d,s.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ)
    (F : Source.Fr) (horizon root : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat)
    (hl : ∀ x,k=some x → x=n) (old : Fin n → Source.Val E.layout τ) (words : Fin n → Roadmap.Word)
    (encoded : ∀ j,MemoryElement p (old j) (words j))
    (found : s.2.heap.get root=some ⟨_,memberArrayData E.layout τ k n hl old⟩)
    (index : Fin n) (value : Source.Val E.layout τ) (word : Roadmap.Word) (newEncoded : MemoryElement p value word)
    (memory : ByteView) (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id))
    (reserved : ReservedOK memory p.free) :
    let values := replace old index value
    let after := withSourceHeap s (s.2.heap.write root (memberArrayData E.layout τ k n hl values) (heap_ty_of_get _ _ _ _ found))
    let q := memberArrayWrittenPlacement s.2.heap p root τ k n hl old values found
    let nextHistory := history s.2.heap allocated p prior root τ k n hl old values found
    let patch := mstore memory (p.address root+arrayPayloadOffset k+index.val*32) word
    (Source.writeLoc F horizon (.mem root index.val) value).run s=(.ok (),after) ∧
      RetainedAllocation allocated q ∧ encodeMixedHeap q (generatedHeapEntries q) patch=patch ∧
      enumeratedMemoryWriteback after allocated q nextHistory patch=.ok (some (.ok (),after)) := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  let values := replace old index value
  let ht := heap_ty_of_get s.2.heap root _ _ found
  let after := withSourceHeap s (s.2.heap.write root (memberArrayData E.layout τ k n hl values) ht)
  let q := memberArrayWrittenPlacement s.2.heap p root τ k n hl old values found
  let patch := mstore memory (p.address root+arrayPayloadOffset k+index.val*32) word
  have current := ArrayWordHeap.whole H s p ok supported F horizon root τ k n hl old words encoded found
    index value word newEncoded memory oldReads reserved
  have next := history s.2.heap allocated p prior root τ k n hl old values found
  have nextSupport : ∀ a σ d,after.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ := by
    intro a σ d actual
    change (s.2.heap.write root (memberArrayData E.layout τ k n hl values) ht).get a=some ⟨σ,d⟩ at actual
    by_cases same : a=root
    · subst a
      rw [Source.Heap.write_get] at actual
      cases actual
      exact supported root _ _ found
    · rw [Source.Heap.write_other s.2.heap same] at actual
      exact supported a σ d actual
  have ready := ownerMemOK_prepares_inventory H after q current.2.1 nextSupport
  have writeback := enumeratedMemory_unchanged after allocated q next patch nextSupport _ ready
  rw [current.2.2.2.1] at writeback
  exact ⟨current.1,next,current.2.2.2.1,writeback⟩
end Solidity.Yul.Views.ArrayWordRetained
