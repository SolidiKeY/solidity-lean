import Solidity.Yul.Views.ArrayWordHeap
import Solidity.Backend.MemoryOps.PhysicalFrameImage
import Solidity.Yul.Adapters.PhysicalSnapshotSlice

/-! Actual P6/MSTORE sink for canonical Source array-member word writes,
including pointer words. Whole changed-heap reconstruction is derived from the
existing typed member codec and old inventory reads, not assumed on output.
Source allocation provenance and full compiler/resource adequacy stay separate. -/
namespace Solidity.Yul.Adapters.P6HeapWordStore
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views ArrayWordStore
variable {C : Contract} {Δ : Ctx}

theorem store_image (image : FrameMem C Δ) (sink : WordSpan image.capacity) (word : Roadmap.Word) :
    frameBytes (store32 image sink (lenU word.val word.isLt))=
      mstore (frameBytes image) sink.offset.val.toNat word := by
  rw [frameBytes_store32]
  simp only [lenU,Int.toNat_natCast]
  exact PhysicalSnapshotSlice.writeBytes_mstore _ _ _

/-- Both actual executions, the whole map and whole administrative Source
writeback use the same reached heap. Canonical encodings and old reads are
input agreement; no final read/inverse/writeback law is a premise. -/
theorem transport {E Γ} (H : Source.HeapTy) (s : Source.EMState E Γ) (p : Placement s.2.heap)
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
    let reached := store32 image sink (lenU word.val word.isLt)
    (Source.writeLoc F horizon (.mem root index.val) value).run s=(.ok (),after) ∧
      Source.MemOK E H after ∧ CoversMixedHeap (generatedHeapEntries q) ∧
      encodeMixedHeap q (generatedHeapEntries q) (frameBytes reached)=frameBytes reached ∧
      enumeratedMemoryWriteback after q q (retainInitial _ _) (frameBytes reached)=.ok (some (.ok (),after)) ∧
      ReservedOK (frameBytes reached) q.free ∧
      Solidity.Backend.Environment.cryptoStep (.op .MSTORE) ⟨sink.offset::lenU word.val word.isLt::tail,frameBytes image⟩=
        some ⟨tail,frameBytes reached⟩ ∧ reached.st=image.st ∧ reached.key=image.key := by
  dsimp only
  have source := ArrayWordHeap.whole H s p ok supported F horizon root τ k n hl old words encoded
    found index value word newEncoded (frameBytes image) oldReads reserved
  have target := frame_store32_target image sink (lenU word.val word.isLt) tail
  rw [store_image,coordinates]
  exact ⟨source.1,source.2.1,source.2.2.1,source.2.2.2.1,source.2.2.2.2.1,source.2.2.2.2.2,
    by rw [store_image,coordinates] at target;exact target⟩
end Solidity.Yul.Adapters.P6HeapWordStore
