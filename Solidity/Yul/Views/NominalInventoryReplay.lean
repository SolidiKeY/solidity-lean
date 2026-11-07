import Solidity.Yul.Views.NominalInventoryTransport

/-! Whole-source replay of an actual changed nominal snapshot. The output
profile follows preserved heap types; the raw reads follow the constructed
view. Neither is an assumed final-state correctness field. -/
namespace Solidity.Yul.Views.NominalInventory

theorem profile_of_types {E : Source.Env} (h h' : Source.Heap E.layout) (types : h'.ty=h.ty)
    (supported : ∀ a τ d,h.get a=some ⟨τ,d⟩ → TypeSupported E τ) :
    ∀ a τ d,h'.get a=some ⟨τ,d⟩ → TypeSupported E τ := by
  intro a τ d found
  have typed : h.ty a=some τ := types ▸ heap_ty_of_get h' a τ d found
  change (h.get a).map Sigma.fst=some τ at typed
  cases old : h.get a with
  | none => rw [old] at typed; cases typed
  | some value =>
    rcases value with ⟨σ,oldData⟩
    rw [old] at typed
    have same : σ=τ := Option.some.inj typed
    cases same
    exact supported a τ oldData old

/-- Replaying the same supplied snapshot preserves the WHOLE resulting source
state in any permutation. This is not commutation of different raw writes. -/
theorem writeback_replay {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) (distinct : (es.map MixedHeapEntry.id).Nodup)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → TypeSupported E τ)
    (m : ByteView) (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : writeback s allocated p history es m=some result) :
    ∃ realized : InventoryRealization allocated,
      result=(.ok (),withSourceHeap s realized.heap) ∧ realized.heap.ty=s.2.heap.ty ∧
      CoversMixedHeap realized.entries ∧ (realized.entries.map MixedHeapEntry.id).Nodup ∧
      encodeMixedHeap realized.placement realized.entries m=m ∧
      (∀ H : Source.HeapTy,Source.MemOK E H s → Source.MemOK E H (withSourceHeap s realized.heap)) ∧
      (∀ fs : List (MixedHeapEntry realized.placement),realized.entries.Perm fs →
        writeback (withSourceHeap s realized.heap) allocated realized.placement realized.history fs m=
          some (.ok (),withSourceHeap s realized.heap)) := by
  obtain ⟨realized,run,covers,nodup,types,next,addresses,free,raw⟩ :=
    writeback_view s allocated p history es coverage distinct m result step
  have profile := profile_of_types s.2.heap realized.heap types supported
  have reads : ∀ e ∈ realized.entries,e.image.Reads m (realized.placement.address e.id) := by
    intro e member
    have actual := encodeMixedHeap_reads realized.placement realized.entries nodup m e member
    rw [raw] at actual
    exact actual
  refine ⟨realized,run,types,covers,nodup,raw,?_,?_⟩
  · intro H ok
    have safe := writeback_MemOK H s allocated p history es m result step ok
    rw [run] at safe
    exact safe
  · intro fs perm
    have full : CoversMixedHeap fs := by
      intro a present
      obtain ⟨e,member,same⟩ := covers a present
      exact ⟨e,perm.mem_iff.mp member,same⟩
    exact writeback_unchanged (withSourceHeap s realized.heap) allocated realized.placement realized.history fs full
      (fun e _ => profile e.id e.ty e.data e.found) m
      (fun e member => reads e (perm.mem_iff.mpr member))

end Solidity.Yul.Views.NominalInventory
