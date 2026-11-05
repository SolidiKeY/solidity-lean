import Solidity.Yul.Views.FixedInventoryPreparation
import Solidity.Yul.Views.InventoryView

/-! Changed fixed/nominal snapshots use the existing real inventory realization.
Each heap write constructs its actual placement, refreshed images and retained
history. Successful canonical preparation is not universal source adequacy. -/
namespace Solidity.Yul.Views.FixedInventory

theorem update_entry {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (es : List (MixedHeapEntry p))
    (e : MixedHeapEntry p) (m : ByteView) (u : OwnedInventoryUpdate allocated p)
    (prepared : update allocated p es e m=some u) : u.entry=e := by
  first
  | solve | simp only [update] at prepared ⊢
  | solve | rfl
  | unfold update at prepared
    cases dec : decode p es e.ty m (p.address e.id) with
    | none => rw [dec] at prepared; cases prepared
    | some o =>
      rw [dec] at prepared
      change (if fits : o.shape.size≤(allocated.shape e.id).size then some (OwnedInventoryUpdate.mk e o fits) else none)=some u at prepared
      split at prepared
      · cases prepared; rfl
      · cases prepared

theorem updates_ids {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (es entries : List (MixedHeapEntry p))
    (m : ByteView) (us : List (OwnedInventoryUpdate allocated p))
    (prepared : updates allocated p es entries m=some us) :
    us.map (fun u => u.entry.id)=entries.map MixedHeapEntry.id := by
  first
  | solve | simp only [updates] at prepared ⊢
  | solve | rfl
  | induction entries generalizing us with
    | nil => cases prepared; rfl
    | cons e entries ih =>
      unfold updates at prepared
      cases one : update allocated p es e m with
      | none => rw [one] at prepared; cases prepared
      | some u =>
        cases tail : updates allocated p es entries m with
        | none => rw [one,tail] at prepared; cases prepared
        | some rest =>
          rw [one,tail] at prepared
          cases prepared
          simp only [List.map_cons,update_entry allocated p es e m u one,ih rest tail]

/-- The output view and retained provenance are constructed by the actual
source write sequence, not supplied as correctness fields. -/
theorem writeback_view {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) (distinct : (es.map MixedHeapEntry.id).Nodup)
    (m : ByteView) (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : writeback s allocated p history es m=some result) :
    ∃ realized : InventoryRealization allocated,
      result=(.ok (),withSourceHeap s realized.heap) ∧ CoversMixedHeap realized.entries ∧
      (realized.entries.map MixedHeapEntry.id).Nodup ∧
      realized.heap.ty=s.2.heap.ty ∧ realized.heap.next=s.2.heap.next ∧
      realized.placement.address=p.address ∧ realized.placement.free=p.free ∧
      encodeMixedHeap realized.placement realized.entries m=m := by
  obtain ⟨us,decoded,same⟩ := Option.map_eq_some_iff.mp step
  subst result
  let realized := realizeInventory allocated p history us s.2.heap p history rfl es
  have raw := updates_raw allocated p es es m us decoded
  have ids := updates_ids allocated p es es m us decoded
  have images := realizeInventory_images allocated p history us s.2.heap p history rfl es m raw (by
    intro e member outside
    have present : e.id ∈ us.map (fun u => u.entry.id) := by
      rw [ids]
      exact List.mem_map.mpr ⟨e,member,rfl⟩
    obtain ⟨u,member,eq⟩ := List.mem_map.mp present
    exact False.elim (outside u member eq.symm))
  have choices := realizeInventory_choices allocated p history us s.2.heap p history rfl es
  refine ⟨realized,realizeInventory_run allocated p history us s p history rfl es,
    realizeInventory_coverage allocated p history us s.2.heap p history rfl es coverage,?_,
    realizeInventory_types allocated p history us s.2.heap p history rfl es,choices.2.2,choices.1,choices.2.1,?_⟩
  · rw [realizeInventory_ids]
    exact distinct
  · apply encodeMixedHeap_unchanged
    intro e member
    have reads := e.image.encode_reads m (realized.placement.address e.id)
    rw [images e member] at reads
    exact reads

/-- Owner preparation supplies the complete inventory for a changed snapshot;
only actual successful canonical preparation is a writeback premise. -/
theorem generated_writeback_view {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (H : Source.HeapTy) (s : Source.EMState E Γ) (allocated : Placement origin)
    (p : Placement s.2.heap) (history : RetainedAllocation allocated p)
    (ok : Source.MemOK E H s)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → TypeSupported E τ)
    (m : ByteView) (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : writeback s allocated p history (generatedHeapEntries p) m=some result) :
    ∃ realized : InventoryRealization allocated,
      result=(.ok (),withSourceHeap s realized.heap) ∧ CoversMixedHeap realized.entries ∧
      (realized.entries.map MixedHeapEntry.id).Nodup ∧
      realized.heap.ty=s.2.heap.ty ∧ realized.heap.next=s.2.heap.next ∧
      realized.placement.address=p.address ∧ realized.placement.free=p.free ∧
      encodeMixedHeap realized.placement realized.entries m=m := by
  have prepared := owner_prepares H s p ok supported
  obtain ⟨_,coverage,distinct⟩ := prepareHeapInventory_ok p _ prepared
  exact writeback_view s allocated p history _ coverage distinct m result step

end Solidity.Yul.Views.FixedInventory
