import Solidity.Yul.Adapters.P6HeapWordStore
import Solidity.Yul.Views.ArrayWordRetained

/-! Actual physical member stores with ORIGINAL retained allocation lineage.
The origin certificate is transported through the real same-shape Source write;
writeback does not replace it with a fresh current snapshot. Canonical profile,
old reads, provenance, coordinates and physical bounds remain explicit. -/
namespace Solidity.Yul.Adapters.P6RetainedHeapWordStore
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views ArrayWordStore
variable {C : Contract} {Δ : Ctx}

theorem transport {E Γ} {origin : Source.Heap E.layout} (H : Source.HeapTy) (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap) (prior : RetainedAllocation allocated p)
    (ok : Source.MemOK E H s)
    (supported : ∀ a σ d,s.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ)
    (F : Source.Fr) (horizon root : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat)
    (hl : ∀ x,k=some x → x=n) (old : Fin n → Source.Val E.layout τ) (words : Fin n → Roadmap.Word)
    (encoded : ∀ j,MemoryElement p (old j) (words j))
    (found : s.2.heap.get root=some ⟨_,memberArrayData E.layout τ k n hl old⟩)
    (index : Fin n) (value : Source.Val E.layout τ) (word : Roadmap.Word) (newEncoded : MemoryElement p value word)
    (image : FrameMem C Δ) (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads (frameBytes image) (p.address e.id))
    (reserved : ReservedOK (frameBytes image) p.free) (sink : WordSpan image.capacity)
    (coordinates : sink.offset.val.toNat=p.address root+arrayPayloadOffset k+index.val*32)
    (tail : List Solidity.Backend.Environment.Word) :
    let values := replace old index value
    let after := withSourceHeap s (s.2.heap.write root (memberArrayData E.layout τ k n hl values) (heap_ty_of_get _ _ _ _ found))
    let q := memberArrayWrittenPlacement s.2.heap p root τ k n hl old values found
    let nextHistory := ArrayWordRetained.history s.2.heap allocated p prior root τ k n hl old values found
    let reached := store32 image sink (lenU word.val word.isLt)
    (Source.writeLoc F horizon (.mem root index.val) value).run s=(.ok (),after) ∧
      Source.MemOK E H after ∧ RetainedAllocation allocated q ∧
      encodeMixedHeap q (generatedHeapEntries q) (frameBytes reached)=frameBytes reached ∧
      enumeratedMemoryWriteback after allocated q nextHistory (frameBytes reached)=.ok (some (.ok (),after)) ∧
      ReservedOK (frameBytes reached) q.free ∧
      Solidity.Backend.Environment.cryptoStep (.op .MSTORE) ⟨sink.offset::lenU word.val word.isLt::tail,frameBytes image⟩=
        some ⟨tail,frameBytes reached⟩ ∧ reached.st=image.st ∧ reached.key=image.key := by
  dsimp only
  have source := ArrayWordRetained.whole H s allocated p prior ok supported F horizon root τ k n hl old words encoded
    found index value word newEncoded (frameBytes image) oldReads reserved
  have safe := (ArrayWordHeap.whole H s p ok supported F horizon root τ k n hl old words encoded
    found index value word newEncoded (frameBytes image) oldReads reserved).2.1
  have reservedAfter := (ArrayWordHeap.whole H s p ok supported F horizon root τ k n hl old words encoded
    found index value word newEncoded (frameBytes image) oldReads reserved).2.2.2.2.2
  have target := frame_store32_target image sink (lenU word.val word.isLt) tail
  rw [P6HeapWordStore.store_image,coordinates]
  exact ⟨source.1,safe,source.2.1,source.2.2.1,source.2.2.2,reservedAfter,
    by rw [P6HeapWordStore.store_image,coordinates] at target;exact target⟩

end Solidity.Yul.Adapters.P6RetainedHeapWordStore
