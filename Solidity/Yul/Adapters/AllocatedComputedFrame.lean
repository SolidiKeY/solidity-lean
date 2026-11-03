import Solidity.Yul.Adapters.ComputedFrameHeap
import Solidity.Yul.Views.ComputedAllocation

/-! Complete canonical frame preparation after actual Source allocation.
The old heap's supported types and the new object's type determine the new
profile; callers do not supply an output inventory or output-view theorem.
Frame capacity and mathematical Word extent remain explicit, independently
of target allocator refinement. -/
namespace Solidity.Yul.Adapters.AllocatedComputedFrame
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views

/-- Transport the existing concrete codec profile through actual heap lookup. -/
theorem allocated_supported {E : Source.Env} {τ : Source.STy}
    (h : Source.Heap E.layout) (data : Source.Data E.layout τ)
    (old : ∀ a σ d,h.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ)
    (new : InventoryTypeSupported E τ) :
    ∀ a σ d,(h.alloc ⟨τ,data⟩).1.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ := by
  intro a σ d found
  by_cases same : a=h.next
  · subst a
    have fresh : (h.alloc ⟨τ,data⟩).1.get h.next=some ⟨τ,data⟩ := Source.Heap.alloc_get h ⟨τ,data⟩
    rw [fresh] at found
    cases found
    exact new
  · rw [Source.Heap.alloc_other h ⟨τ,data⟩ same] at found
    exact old a σ d found

/-- Real source allocation followed by complete frame encoding and whole-source
unchanged writeback. Both results concern the same actual allocated state. -/
theorem allocation_roundtrip {E : Source.Env} {Ξ : Source.RCtx} {C : Contract} {Γ : Ctx}
    {τ : Source.STy} (H : Source.HeapTy) (s : Source.EMState E Ξ)
    (ok : Source.MemOK E H s) (data : Source.Data E.layout τ) (shape : MemoryShape)
    (found : ComputedPlacement.objectShape data=some shape)
    (valid : Source.DataOK E s.2.heap.ty data) (inner : Source.Data.Inner (E:=E) data)
    (supported : ∀ a σ d,s.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ)
    (newSupported : InventoryTypeSupported E τ)
    (clear : ComputedPlacement.unsupported s.2.heap=[])
    (bound : ComputedPlacement.position s.2.heap s.2.heap.next+max 1 shape.size<2^256)
    (carrier : FrameMem C Γ) (residual : ByteView) (fits : MemoryAgreement.Fits carrier residual)
    (room : ComputedPlacement.position s.2.heap s.2.heap.next+max 1 shape.size≤carrier.highWaterWords*32) :
    let after:=objectAllocatedState s data
    (Source.allocRef data).run s=
      (.ok (.memRef (ComputedPlacement.objectShape_memory data shape found) s.2.heap.next),after) ∧
    Source.MemOK E H after ∧
    ∃ (p : Placement after.2.heap) (image : FrameMem C Γ),
      ComputedFrameHeap.prepare after carrier residual fits=.ok ⟨p,image⟩ ∧
      CoversMixedHeap (generatedHeapEntries p) ∧ ((generatedHeapEntries p).map MixedHeapEntry.id).Nodup ∧
      frameBytes image=encodeMixedHeap p (generatedHeapEntries p) residual ∧
      enumeratedMemoryWriteback after p p (retainInitial _ _) (frameBytes image)=.ok (some (.ok (),after)) ∧
      image.st=carrier.st ∧ image.key=carrier.key ∧ image.capacity=carrier.capacity ∧
      image.highWaterWords=carrier.highWaterWords := by
  have mem := (objectAllocRef_MemOK H s data (ComputedPlacement.objectShape_memory data shape found)
    (ComputedPlacement.objectShape_top data shape found) inner valid ok).1
  refine ⟨objectAllocRef_run s data (ComputedPlacement.objectShape_memory data shape found),mem,?_⟩
  apply ComputedFrameHeap.owner_roundtrip H (objectAllocatedState s data) mem
    (allocated_supported s.2.heap data supported newSupported)
    (ComputedPlacement.alloc_clear s.2.heap ⟨τ,data⟩ clear shape found)
  · change ComputedPlacement.position (s.2.heap.alloc ⟨τ,data⟩).1 (s.2.heap.alloc ⟨τ,data⟩).1.next<2^256
    rw [ComputedPlacement.alloc_end s.2.heap ⟨τ,data⟩ shape found]
    exact bound
  · change ComputedPlacement.position (s.2.heap.alloc ⟨τ,data⟩).1 (s.2.heap.alloc ⟨τ,data⟩).1.next≤_
    rw [ComputedPlacement.alloc_end s.2.heap ⟨τ,data⟩ shape found]
    exact room
end Solidity.Yul.Adapters.AllocatedComputedFrame
