import Solidity.Yul.Views.ComputedAllocationWrite
import Solidity.Yul.Views.MixedNominalInventoryPreparation

/-! Mixed-profile actual Source allocation reuses the computed placement and
incremental object encoder. Owner facts derive preparation and allocated-heap
roundtrip. Word-fit and original reads remain genuine premises; no target
allocator policy or global allocation provenance is inferred. -/
namespace Solidity.Yul.Views.MixedNominalInventory

theorem allocation_profile {E : Source.Env} (h : Source.Heap E.layout)
    {τ : Source.STy} (data : Source.Data E.layout τ) (newSupport : TypeSupported E τ)
    (oldSupport : ∀ a σ d,h.get a=some ⟨σ,d⟩ → TypeSupported E σ) :
    ∀ a σ d,(h.alloc ⟨τ,data⟩).1.get a=some ⟨σ,d⟩ → TypeSupported E σ := by
  first | solve | simp only
        | intro a σ d found
          by_cases newest : a=h.next
          · subst a
            rw [show (h.alloc ⟨τ,data⟩).1.get h.next=some ⟨τ,data⟩ from Source.Heap.alloc_get h _] at found
            cases found
            exact newSupport
          · rw [Source.Heap.alloc_other h ⟨τ,data⟩ newest] at found
            exact oldSupport a σ d found

theorem computed_allocation_complete {E : Source.Env} (h : Source.Heap E.layout) (p : Placement h)
    (done : ComputedPlacement.prepare h=.ok p) {τ : Source.STy} (data : Source.Data E.layout τ)
    (shape : MemoryShape) (found : ComputedPlacement.objectShape data=some shape)
    (bound : p.free.val+max 1 shape.size<2^256) (m : ByteView)
    (supported : TypeSupported E τ) (inner : Source.Data.Inner (E:=E) data)
    (valid : Source.DataOK E h.ty data) :
    (ComputedAllocationWrite.prepare h p done data shape found bound m).isSome := by
  first | solve | simp only [ComputedAllocationWrite.prepare]
        | unfold ComputedAllocationWrite.prepare objectAllocationView
          rw [Option.isSome_map]
          exact image_prepared _ _ _ data (Source.Heap.alloc_get h _) supported inner
            (Source.DataOK.mono (Source.Heap.alloc_le h ⟨τ,data⟩) valid)

/-- The existing physical encoder and actual Source allocation construct the
same allocated view; no final view/inverse/preparation witness is supplied. -/
theorem computed_allocation_sound {E : Source.Env} {Γ : Source.RCtx} (H : Source.HeapTy)
    (s : Source.EMState E Γ) (p : Placement s.2.heap) (done : ComputedPlacement.prepare s.2.heap=.ok p)
    {τ : Source.STy} (data : Source.Data E.layout τ) (shape : MemoryShape)
    (found : ComputedPlacement.objectShape data=some shape) (bound : p.free.val+max 1 shape.size<2^256)
    (m raw : ByteView) (step : ComputedAllocationWrite.prepare s.2.heap p done data shape found bound m=some raw)
    (ok : Source.MemOK E H s) (inner : Source.Data.Inner (E:=E) data)
    (valid : Source.DataOK E s.2.heap.ty data) (newSupport : TypeSupported E τ)
    (oldSupport : ∀ a σ d,s.2.heap.get a=some ⟨σ,d⟩ → TypeSupported E σ)
    (reads : ∀ e∈generatedHeapEntries p,e.image.Reads m (p.address e.id)) :
    let q:=ComputedAllocationWrite.placement s.2.heap p done data shape found bound
    let after:=objectAllocatedState s data
    (Source.allocRef data).run s=(.ok (.memRef (ComputedPlacement.objectShape_memory data shape found) s.2.heap.next),after) ∧
    Source.MemOK E H after ∧ prepareHeapInventory q=.ok (generatedHeapEntries q) ∧
    encodeMixedHeap q (generatedHeapEntries q) raw=raw ∧
    writeback after q q .initial (generatedHeapEntries q) raw=some (.ok (),after) := by
  first | solve | simp only
        | have ready := owner_prepares H s p ok oldSupport
          have physical := objectAllocationView_computed s.2.heap p data
            (ComputedPlacement.objectShape_memory data shape found) shape
            (ComputedPlacement.objectShape_sound data shape found) p.free.val
            (ComputedAllocationWrite.nextFree p shape bound) (Nat.le_refl _)
            (ComputedAllocationWrite.computed_fresh s.2.heap p done) (by dsimp [ComputedAllocationWrite.nextFree];omega)
            _ ready m raw reads step
          have safe := (objectAllocRef_MemOK H s data (ComputedPlacement.objectShape_memory data shape found)
            (ComputedPlacement.objectShape_top data shape found) inner valid ok).1
          have roundtrip := generated_roundtrip H (objectAllocatedState s data)
            (ComputedAllocationWrite.placement s.2.heap p done data shape found bound)
            (ComputedAllocationWrite.placement s.2.heap p done data shape found bound) .initial safe
            (allocation_profile s.2.heap data newSupport oldSupport) raw
          dsimp only [ComputedAllocationWrite.placement] at roundtrip
          rw [physical.2.2.2] at roundtrip
          exact ⟨objectAllocRef_run s data (ComputedPlacement.objectShape_memory data shape found),safe,
            physical.1,physical.2.2.2,roundtrip.2⟩

end Solidity.Yul.Views.MixedNominalInventory
