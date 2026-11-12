import Solidity.Yul.Adapters.P6HeapWordStore
import Solidity.Yul.Views.RetainedArrayHeader

/-! Actual P6/MSTORE dynamic header updates with original allocation history.
Canonical elements are decoded from the SAME reached raw map, including dormant
payload exposed by regrowth. Capacity and canonical preparation stay explicit;
heapPut transport is not a new high-level Source length-assignment operation. -/
namespace Solidity.Yul.Adapters.P6RetainedArrayHeader
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views
variable {C : Contract} {Δ : Ctx}

theorem transport {E Γ} {origin : Source.Heap E.layout} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (allocated : Placement origin) (p : Placement s.2.heap) (prior : RetainedAllocation allocated p)
    (ok : Source.MemOK E H s)
    (supported : ∀ a σ d,s.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ)
    (root : Nat) (τ : Source.STy) (elementType : ExtendedMemberType E.layout τ)
    (n : Nat) (old : Fin n → Source.Val E.layout τ)
    (found : s.2.heap.get root=some ⟨_,dynamicMemberData E.layout τ n old⟩)
    (length : Roadmap.Word) (values : Fin length.val → Source.Val E.layout τ) (words : Fin length.val → Roadmap.Word)
    (encoded : ∀ i,MemoryElement p (values i) (words i))
    (capacity : (MemoryShape.array true length.val).size≤(allocated.shape root).size)
    (image : FrameMem C Δ) (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads (frameBytes image) (p.address e.id))
    (tail : ∀ i,mload (frameBytes image) (p.address root+32+i.val*32)=words i) (reserved : ReservedOK (frameBytes image) p.free)
    (sink : WordSpan image.capacity) (coordinates : sink.offset.val.toNat=p.address root)
    (stackTail : List Solidity.Backend.Environment.Word) :
    let data := dynamicMemberData E.layout τ length.val values
    let out : Source.EMState E Γ := withSourceHeap s (s.2.heap.write root data (heap_ty_of_get s.2.heap root _ _ found))
    let q : Placement out.2.heap := retainedMemberArrayPlacement (h:=s.2.heap) allocated p prior root τ n old found length.val values capacity
    let history := retainedMemberArray_history allocated p prior root τ n old found length.val values capacity
    let reached := store32 image sink (lenU length.val length.isLt)
    canonicalRetainedState s allocated p prior (generatedHeapEntries p) root τ (frameBytes reached)=some (.ok (),out) ∧
      (Source.heapPut root ⟨_,data⟩).run s=(.ok (),out) ∧ Source.MemOK E H out ∧
      q.address=p.address ∧ q.free=p.free ∧
      encodeMixedHeap q (generatedHeapEntries q) (frameBytes reached)=frameBytes reached ∧
      enumeratedMemoryWriteback out allocated q history (frameBytes reached)=.ok (some (.ok (),out)) ∧ ReservedOK (frameBytes reached) q.free ∧
      Solidity.Backend.Environment.cryptoStep (.op .MSTORE)
        ⟨sink.offset::lenU length.val length.isLt::stackTail,frameBytes image⟩=
        some ⟨stackTail,frameBytes reached⟩ ∧ reached.st=image.st ∧ reached.key=image.key := by
  dsimp only
  have source := RetainedArrayHeader.whole H s allocated p prior ok supported root τ elementType n old found
    length values words encoded capacity (frameBytes image) oldReads tail reserved
  have target := frame_store32_target image sink (lenU length.val length.isLt) stackTail
  rw [P6HeapWordStore.store_image,coordinates]
  exact ⟨source.1,source.2.1,source.2.2.1,source.2.2.2.1,source.2.2.2.2.1,
    source.2.2.2.2.2.1,source.2.2.2.2.2.2.1,source.2.2.2.2.2.2.2,
    by rw [P6HeapWordStore.store_image,coordinates] at target;exact target⟩

end Solidity.Yul.Adapters.P6RetainedArrayHeader
