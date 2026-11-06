import Solidity.Yul.Views.MultiRootByteBoundary
import Solidity.Yul.Adapters.FrameHeap

/-! Construct the finite P6 frame of an actual multi-root source byte plan.
The upper bound is derived from placement geometry and the initial frame;
no final Fits/view premise is supplied. This is physical realization, not
an opcode compiler theorem or reachable allocation-provenance claim. -/
namespace Solidity.Yul.Adapters.P6MultiRootByte
open Solidity.Yul.Views Solidity.Yul.Views.MultiRootByteWrites
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
variable {C : Contract} {Δ : Ctx}

theorem fits {E Γ} (F : Source.Fr) (horizon : Nat) (requests : List Request)
    (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (image : FrameMem C Δ) (room : p.free.val≤image.highWaterWords*32) :
    MemoryAgreement.Fits image (coupled F horizon p.address requests s (frameBytes image)).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  intro k high
  rw [MultiRootByteBoundary.above_free F horizon requests s p supported (frameBytes image) k (by omega)]
  exact MemoryAgreement.fits_view image k high

/-- A single actual source result and its exact finite physical image. Existing
source failures stop writes; they are never preparation None or cleaned bytes. -/
def run {E Γ} (F : Source.Fr) (horizon : Nat) (requests : List Request)
    (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (image : FrameMem C Δ) (room : p.free.val≤image.highWaterWords*32) :
    (Source.R Unit × Source.EMState E Γ) × FrameMem C Δ :=
  let out := coupled F horizon p.address requests s (frameBytes image)
  (out.1,MemoryAgreement.writeback image out.2 (fits F horizon requests s p supported image room))

theorem bytes {E Γ} (F : Source.Fr) (horizon : Nat) (requests : List Request)
    (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (image : FrameMem C Δ) (room : p.free.val≤image.highWaterWords*32) :
    frameBytes (run F horizon requests s p supported image room).2=
      (coupled F horizon p.address requests s (frameBytes image)).2 :=
  MemoryAgreement.encode_decode image _ (fits F horizon requests s p supported image room)

/-- The full original source store roundtrip and original-H safety follow from
one coupled execution and its derived finite frame. All frame metadata stays. -/
theorem sound {E Γ} {origin : Source.Heap E.layout} (H : Source.HeapTy)
    (allocated : Placement origin) (F : Source.Fr) (horizon : Nat) (requests : List Request)
    (s : Source.EMState E Γ) (p : Placement s.2.heap) (prior : RetainedAllocation allocated p)
    (ok : Source.MemOK E H s)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (image : FrameMem C Δ) (room : p.free.val≤image.highWaterWords*32)
    (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads (frameBytes image) (p.address e.id))
    (reserved : ReservedOK (frameBytes image) p.free) :
    let out := run F horizon requests s p supported image room
    out.1=(program F horizon requests).run s ∧
    out.2.st=image.st ∧ out.2.key=image.key ∧ out.2.capacity=image.capacity ∧
    out.2.highWaterWords=image.highWaterWords ∧
    ∃ q : Placement out.1.2.2.heap,
      Source.MemOK E H out.1.2 ∧ q.address=p.address ∧ q.free=p.free ∧
      encodeMixedHeap q (generatedHeapEntries q) (frameBytes out.2)=frameBytes out.2 ∧
      ∃ history : RetainedAllocation allocated q,
        enumeratedMemoryWriteback out.1.2 allocated q history (frameBytes out.2)=.ok (some (.ok (),out.1.2)) ∧
        ReservedOK (frameBytes out.2) q.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  have actual := MultiRootByteWrites.sound H allocated F horizon requests s p prior ok supported
    (frameBytes image) oldReads reserved
  dsimp only
  refine ⟨actual.1,rfl,rfl,rfl,rfl,?_⟩
  rw [bytes]
  exact actual.2
end Solidity.Yul.Adapters.P6MultiRootByte
