import Solidity.Yul.Views.FixedInventoryView

/-! A successful fixed/nominal inventory write constructs a replay view with
its original allocation history. Heap type preservation derives decoder support;
no output-view or output-support certificate is required from the caller. -/
namespace Solidity.Yul.Views.FixedInventory

theorem profile_of_types {E : Source.Env} (h h' : Source.Heap E.layout)
    (types : h'.ty=h.ty)
    (supported : ∀ a τ d,h.get a=some ⟨τ,d⟩ → TypeSupported E τ) :
    ∀ a τ d,h'.get a=some ⟨τ,d⟩ → TypeSupported E τ := by
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

/-- Replaying the constructed changed snapshot preserves the entire reached
Source state, including locals, calldata and all non-heap components. -/
theorem writeback_replay {E : Source.Env} {Γ : Source.RCtx}
    {origin : Source.Heap E.layout} (s : Source.EMState E Γ) (allocated : Placement origin)
    (p : Placement s.2.heap) (history : RetainedAllocation allocated p)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es)
    (distinct : (es.map MixedHeapEntry.id).Nodup)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → TypeSupported E τ)
    (m : ByteView) (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : writeback s allocated p history es m=some result) :
    ∃ realized : InventoryRealization allocated,
      result=(.ok (),withSourceHeap s realized.heap) ∧
      CoversMixedHeap realized.entries ∧ (realized.entries.map MixedHeapEntry.id).Nodup ∧
      encodeMixedHeap realized.placement realized.entries m=m ∧
      (∀ H : Source.HeapTy,Source.MemOK E H s → Source.MemOK E H (withSourceHeap s realized.heap)) ∧
      writeback (withSourceHeap s realized.heap) allocated realized.placement
        realized.history realized.entries m=some (.ok (),withSourceHeap s realized.heap) := by
  first
  | solve | simp only [writeback]
  | solve | rfl
  | obtain ⟨r,run,covers,nodup,types,_,_,_,raw⟩ :=
      writeback_view s allocated p history es coverage distinct m result step
    have profile := profile_of_types s.2.heap r.heap types supported
    have reads : ∀ e∈r.entries,e.image.Reads m (r.placement.address e.id) := by
      intro e member
      have read := encodeMixedHeap_reads r.placement r.entries nodup m e member
      rw [raw] at read
      exact read
    refine ⟨r,run,covers,nodup,raw,?_,?_⟩
    · intro H ok
      have safe := writeback_MemOK H s allocated p history es m result step ok
      rw [run] at safe
      exact safe
    · exact writeback_unchanged (withSourceHeap s r.heap) allocated r.placement r.history
        r.entries covers (fun e _=>profile e.id e.ty e.data e.found) m reads

end Solidity.Yul.Views.FixedInventory
