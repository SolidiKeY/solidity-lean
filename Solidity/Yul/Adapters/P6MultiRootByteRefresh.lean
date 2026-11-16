import Solidity.Yul.Adapters.P6MultiRootByte
import Solidity.Yul.Views.MultiRootByteAppend

/-! Derive the next plan's physical/source preparation from the actual first
plan, including failed prefixes. Continuing execution still requires actual
success; failed plans short-circuit. No second view, frame bound or safety law
is assumed. Allocation provenance remains the incoming retained certificate. -/
namespace Solidity.Yul.Adapters.P6MultiRootByteRefresh
open Solidity.Yul.Views Solidity.Yul.Views.MultiRootByteWrites
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
variable {C : Contract} {Δ : Ctx}

theorem refresh {E Γ} {origin : Source.Heap E.layout} (H : Source.HeapTy)
    (allocated : Placement origin) (F : Source.Fr) (horizon : Nat) (requests : List Request)
    (s : Source.EMState E Γ) (p : Placement s.2.heap) (prior : RetainedAllocation allocated p)
    (ok : Source.MemOK E H s)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (image : FrameMem C Δ) (room : p.free.val≤image.highWaterWords*32)
    (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads (frameBytes image) (p.address e.id))
    (reserved : ReservedOK (frameBytes image) p.free) :
    let out := P6MultiRootByte.run F horizon requests s p supported image room
    ∃ q : Placement out.1.2.2.heap,
      q.address=p.address ∧ q.free=p.free ∧
      ∃ history : RetainedAllocation allocated q,
        Source.MemOK E H out.1.2 ∧
        (∀ a τ d,out.1.2.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ) ∧
        q.free.val≤out.2.highWaterWords*32 ∧
        (∀ e∈generatedHeapEntries q,e.image.Reads (frameBytes out.2) (q.address e.id)) ∧
        ReservedOK (frameBytes out.2) q.free ∧
        enumeratedMemoryWriteback out.1.2 allocated q history (frameBytes out.2)=.ok (some (.ok (),out.1.2)) := by
  dsimp only
  let out := P6MultiRootByte.run F horizon requests s p supported image room
  have physical := P6MultiRootByte.sound H allocated F horizon requests s p prior ok supported image room oldReads reserved
  obtain ⟨q,safe,addresses,free,full,history,wb,reservedAfter⟩ := physical.2.2.2.2.2
  obtain ⟨outcome,heap,executed,types,support⟩ := MultiRootByteFrames.program_store F horizon requests s supported
  have actual : out.1=(outcome,withSourceHeap s heap) := physical.1.trans executed
  have nextSupport : ∀ a τ d,out.1.2.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ := by
    rw [actual]
    exact support
  have prepared := ownerMemOK_prepares_inventory H out.1.2 q safe nextSupport
  have nextReads := encodeMixedHeap_reads q _ (prepareHeapInventory_ok q _ prepared).2.2 (frameBytes out.2)
  rw [full] at nextReads
  refine ⟨q,addresses,free,history,safe,nextSupport,?_,nextReads,reservedAfter,wb⟩
  rw [free,physical.2.2.2.2.1]
  exact room

/-- Exact chronological equality for two actual physical plans. The q address
fact is produced by refresh; no assumed final-byte or second-view relation. -/
theorem append_success {E Γ} (F : Source.Fr) (horizon : Nat) (first second : List Request)
    (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (image : FrameMem C Δ) (room : p.free.val≤image.highWaterWords*32)
    (q : Placement (P6MultiRootByte.run F horizon first s p supported image room).1.2.2.heap)
    (addresses : q.address=p.address)
    (nextSupport : ∀ a τ d,(P6MultiRootByte.run F horizon first s p supported image room).1.2.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (nextRoom : q.free.val≤(P6MultiRootByte.run F horizon first s p supported image room).2.highWaterWords*32)
    (success : (P6MultiRootByte.run F horizon first s p supported image room).1.1=.ok ()) :
    let out := P6MultiRootByte.run F horizon first s p supported image room
    let final := P6MultiRootByte.run F horizon second out.1.2 q nextSupport out.2 nextRoom
    coupled F horizon p.address (first++second) s (frameBytes image)=(final.1,frameBytes final.2) := by
  dsimp only
  let out := P6MultiRootByte.run F horizon first s p supported image room
  have prefixRun : coupled F horizon p.address first s (frameBytes image)=(out.1,frameBytes out.2) := by
    apply Prod.ext
    · rfl
    · exact (P6MultiRootByte.bytes F horizon first s p supported image room).symm
  have chronological := MultiRootByteAppend.coupled_append F horizon p.address first second s (frameBytes image)
  rw [prefixRun] at chronological
  dsimp only at chronological
  change out.1.1=.ok () at success
  rw [success] at chronological
  dsimp only at chronological
  rw [chronological,←addresses]
  apply Prod.ext
  · rfl
  · exact (P6MultiRootByte.bytes F horizon second out.1.2 q nextSupport out.2 nextRoom).symm
end Solidity.Yul.Adapters.P6MultiRootByteRefresh
