import Solidity.Yul.Adapters.P6HeapWordStore
import Solidity.Yul.Views.RetainedByteHeader

/-! Actual P6/MSTORE packed bytes/string header updates. Recovered payload is
read from the same raw physical frame, including dormant nonzero padding.
Original allocation capacity/history, complete reencoding and actual heapPut
remain distinct from source-language admission or target allocator adequacy. -/
namespace Solidity.Yul.Adapters.P6RetainedByteHeader
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views
variable {C : Contract} {Δ : Ctx}

theorem transport {E Γ} {origin : Source.Heap E.layout} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (allocated : Placement origin) (p : Placement s.2.heap) (prior : RetainedAllocation allocated p)
    (ok : Source.MemOK E H s)
    (supported : ∀ a σ d,s.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ)
    (root : Nat) (string : Bool) (old : List UInt8)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (image : FrameMem C Δ) (length : Roadmap.Word)
    (capacity : (MemoryShape.bytes length.val).size≤(allocated.shape root).size)
    (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads (frameBytes image) (p.address e.id)) (reserved : ReservedOK (frameBytes image) p.free)
    (sink : WordSpan image.capacity) (coordinates : sink.offset.val.toNat=p.address root)
    (stackTail : List Solidity.Backend.Environment.Word) :
    let data := heapByteData E.layout string (readBytes (frameBytes image) (p.address root+32) length.val)
    let out : Source.EMState E Γ := withSourceHeap s (s.2.heap.write root data (heap_ty_of_get s.2.heap root _ _ found))
    let q : Placement out.2.heap := RetainedByteHeader.placement s.2.heap allocated p prior root string old found (frameBytes image) length capacity
    let lineage := RetainedByteHeader.history s.2.heap allocated p prior root string old found (frameBytes image) length capacity
    let reached := store32 image sink (lenU length.val length.isLt)
    retainedByteStateWriteback s allocated p prior root string old found (frameBytes reached)=some out ∧
      (Source.heapPut root ⟨_,data⟩).run s=(.ok (),out) ∧ Source.MemOK E H out ∧ q.address=p.address ∧ q.free=p.free ∧
      encodeMixedHeap q (generatedHeapEntries q) (frameBytes reached)=frameBytes reached ∧
      enumeratedMemoryWriteback out allocated q lineage (frameBytes reached)=.ok (some (.ok (),out)) ∧ ReservedOK (frameBytes reached) q.free ∧
      Solidity.Backend.Environment.cryptoStep (.op .MSTORE)
        ⟨sink.offset::lenU length.val length.isLt::stackTail,frameBytes image⟩=
        some ⟨stackTail,frameBytes reached⟩ ∧ reached.st=image.st ∧ reached.key=image.key := by
  dsimp only
  have source := RetainedByteHeader.whole H s allocated p prior ok supported root string old found
    (frameBytes image) length capacity oldReads reserved
  have target := frame_store32_target image sink (lenU length.val length.isLt) stackTail
  rw [P6HeapWordStore.store_image,coordinates]
  exact ⟨source.1,source.2.1,source.2.2.1,source.2.2.2.1,source.2.2.2.2.1,
    source.2.2.2.2.2.1,source.2.2.2.2.2.2.1,source.2.2.2.2.2.2.2,
    by rw [P6HeapWordStore.store_image,coordinates] at target;exact target⟩

end Solidity.Yul.Adapters.P6RetainedByteHeader
