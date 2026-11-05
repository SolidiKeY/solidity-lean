import Solidity.Yul.Views.MultiRootByteFrames

/-! Finite multi-root source byte writes cannot alter the complement above the
actual placement end. Successful offsets derive from the actual selected heap
object and its live index; source failure stops the residual journal. -/
namespace Solidity.Yul.Views.MultiRootByteBoundary
open MultiRootByteWrites

theorem payload_before_free {D : Source.Layout} (heap : Source.Heap D)
    (p : Placement heap) (root : Nat) (string : Bool) (bytes : Roadmap.Bytes)
    (found : heap.get root=some ⟨heapByteType string,heapByteData D string bytes⟩)
    (index : Nat) (inside : index<bytes.length) : p.address root+32+index<p.free.val := by
  first | (simp only;done) | decide | omega | rfl | skip
  have present : (heap.cells root).isSome := by
    change (heap.get root).isSome=true
    rw [found];rfl
  have ending := p.ends root present
  rw [heapByte_placement_shape heap p root string bytes found] at ending
  have live := byte_shape_live_bound bytes.length
  omega

/-- No initial raw-view, MemOK, capacity, length cap, or final-view law is
assumed here. Placement and supported actual heap constructors suffice. -/
theorem above_free {E Γ} (F : Source.Fr) (horizon : Nat) (requests : List Request)
    (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (memory : ByteView) (k : Nat) (high : p.free.val≤k) :
    (coupled F horizon p.address requests s memory).2 k=memory k := by
  first | (simp only;done) | decide | omega | rfl | skip
  induction requests generalizing s p memory with
  | nil => rfl
  | cons request rest ih =>
    rcases classify s F horizon request supported with ⟨string,bytes,found⟩ | ⟨reason,failure⟩
    · by_cases inside : request.2.1<bytes.length
      · let data := heapByteData E.layout string (bytes.set request.2.1 request.2.2)
        let ht := heap_ty_of_get s.2.heap request.1 _ _ found
        let after := withSourceHeap s (s.2.heap.write request.1 data ht)
        let q := ByteElementStore.placement s.2.heap p request.1 string bytes found ⟨request.2.1,inside⟩ request.2.2
        let raw := saveByte memory (p.address request.1+32+request.2.1) request.2.2
        have run : (action F horizon request).run s=(.ok (),after) :=
          ByteElementStore.source_run s F horizon request.1 string bytes found ⟨request.2.1,inside⟩ request.2.2
        have supportAfter := heapWrite_inventory_supported s.2.heap request.1 data ht supported
        have low := payload_before_free s.2.heap p request.1 string bytes found request.2.1 inside
        rw [coupled,run]
        have untouched := ih after q supportAfter raw high
        exact untouched.trans (find_saveByte_other _ _ (by omega))
      · have failure : (action F horizon request).run s=(.error (.revert (Source.panicData .index)),s) :=
          ByteWriteSequence.bounds s F horizon request.1 string bytes found request.2 inside
        rw [coupled,failure]
    · rw [coupled,failure]
end Solidity.Yul.Views.MultiRootByteBoundary
