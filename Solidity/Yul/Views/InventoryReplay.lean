import Solidity.Yul.Views.InventoryCandidateOrder
import Solidity.Yul.Views.InventoryView
import Solidity.Yul.Views.InventoryUnchanged

/-! Successful changed-snapshot preparation constructs a new typed heap view.
Its actual preserved heap types determine codec support; the same raw snapshot
then replays as whole-source identity, retaining the original allocation history.
No final inverse, view, safety or output-support witness is supplied. -/
namespace Solidity.Yul.Views

theorem inventoryProfile_of_types {E : Source.Env} (h h' : Source.Heap E.layout)
    (types : h'.ty=h.ty)
    (supported : ∀ a τ d,h.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ) :
    ∀ a τ d,h'.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ := by
  intro a τ d found
  have typed : h.ty a=some τ := types ▸ heap_ty_of_get h' a τ d found
  change (h.get a).map Sigma.fst=some τ at typed
  cases old : h.get a with
  | none => rw [old] at typed;cases typed
  | some value =>
    rcases value with ⟨σ,oldData⟩
    rw [old] at typed
    have same : σ=τ := Option.some.inj typed
    cases same
    exact supported a τ oldData old

/-- Every successful supported complete writeback constructs its own replay
state, placement, coverage and retained history. Even reordered output entries
write back as the identity on the WHOLE actual resulting Source state. -/
theorem inventoryStateWriteback_replay {E : Source.Env} {Γ : Source.RCtx}
    {origin : Source.Heap E.layout} (s : Source.EMState E Γ) (allocated : Placement origin)
    (p : Placement s.2.heap) (history : RetainedAllocation allocated p)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es)
    (distinct : (es.map MixedHeapEntry.id).Nodup)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (m : ByteView) (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : inventoryStateWriteback s allocated p history es m=some result) :
    ∃ realized : InventoryRealization allocated,
      result=(.ok (),withSourceHeap s realized.heap) ∧
      realized.heap.ty=s.2.heap.ty ∧ CoversMixedHeap realized.entries ∧
      (realized.entries.map MixedHeapEntry.id).Nodup ∧
      encodeMixedHeap realized.placement realized.entries m=m ∧
      (∀ H : Source.HeapTy,Source.MemOK E H s → Source.MemOK E H (withSourceHeap s realized.heap)) ∧
      (∀ fs : List (MixedHeapEntry realized.placement),realized.entries.Perm fs →
        inventoryStateWriteback (withSourceHeap s realized.heap) allocated realized.placement
          realized.history fs m=some (.ok (),withSourceHeap s realized.heap)) := by
  obtain ⟨realized,run,covers,nodup,raw⟩ := inventoryStateWriteback_view s allocated p history es coverage distinct m result step
  obtain ⟨us,decoded,same⟩ := Option.map_eq_some_iff.mp step
  have resultTypes : result.2.2.heap.ty=s.2.heap.ty := by
    rw [← same]
    exact runInventoryUpdates_types us s
  have types : realized.heap.ty=s.2.heap.ty := by
    rw [run] at resultTypes
    exact resultTypes
  have profile := inventoryProfile_of_types s.2.heap realized.heap types supported
  have reads : ∀ e∈realized.entries,e.image.Reads m (realized.placement.address e.id) := by
    intro e member
    have read := encodeMixedHeap_reads realized.placement realized.entries nodup m e member
    rw [raw] at read
    exact read
  have unchanged := inventoryStateWriteback_unchanged (withSourceHeap s realized.heap) allocated
    realized.placement realized.history realized.entries covers
    (fun e _=>profile e.id e.ty e.data e.found) m reads
  refine ⟨realized,run,types,covers,nodup,raw,?_,?_⟩
  · intro H ok
    have safe := inventoryStateWriteback_MemOK H s allocated p history es m result step ok
    rw [run] at safe
    exact safe
  · intro fs perm
    exact (inventoryStateWriteback_perm (withSourceHeap s realized.heap) allocated realized.placement
      realized.history realized.entries fs perm nodup m).symm.trans unchanged
end Solidity.Yul.Views
