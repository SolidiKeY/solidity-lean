import Solidity.Yul.Views.MixedNominalInventoryView
import Solidity.Yul.Views.InventorySnapshotCursor

/-! Fixed-array preparation feeds the existing dependent physical cursor.
The carrier is shared with nominal inventories; every Source result and refreshed
placement comes from the same concrete typed write sequence. Preparation failure
is distinct from a Source halt. No recursive evaluator is instrumented here. -/
namespace Solidity.Yul.Views.MixedNominalInventory
open NominalInventory (SnapshotCursor)

private theorem transport_cursor {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) {s t : Source.EMState E Γ} (same : s=t)
    (c : SnapshotCursor allocated t) :
    (⟨s,same.symm ▸ c⟩ : Σ next, SnapshotCursor allocated next)=⟨t,c⟩ := by
  first
  | solve | rfl
  | solve | simp only
  | cases same; rfl

/-- Execute existing prepared Source writes, retaining their actual result state.
The dependent cursor is transported by a proved equality, never an assumed law. -/
def snapshotStep {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (m : ByteView) : Option (Σ next : Source.EMState E Γ, SnapshotCursor allocated next) :=
  (updates allocated c.placement c.entries c.entries m).map fun us =>
    let r := realizeInventory allocated c.placement c.history us s.2.heap c.placement c.history rfl c.entries
    let actual := (runInventoryUpdates us).run s
    have stateEq : actual.2=withSourceHeap s r.heap :=
      congrArg Prod.snd (realizeInventory_run allocated c.placement c.history us s c.placement c.history rfl c.entries)
    ⟨actual.2,stateEq.symm ▸ (⟨r.placement,r.history,r.entries⟩ : SnapshotCursor allocated (withSourceHeap s r.heap))⟩

/-- The dependent carrier is derived from the same concrete typed realization. -/
theorem snapshotStep_eq {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (m : ByteView) :
    snapshotStep allocated s c m =
      (updates allocated c.placement c.entries c.entries m).map (fun us =>
        let r := realizeInventory allocated c.placement c.history us s.2.heap c.placement c.history rfl c.entries
        ⟨withSourceHeap s r.heap,⟨r.placement,r.history,r.entries⟩⟩) := by
  unfold snapshotStep
  apply congrArg (fun f => (updates allocated c.placement c.entries c.entries m).map f)
  funext us
  have actual := realizeInventory_run allocated c.placement c.history us s c.placement c.history rfl c.entries
  exact transport_cursor allocated (congrArg Prod.snd actual) _

/-- Erasing only physical evidence gives the existing actual Source entry point. -/
theorem snapshotStep_source {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (m : ByteView) :
    (snapshotStep allocated s c m).map (fun next => ((.ok () : Except Source.Halt Unit),next.1)) =
      writeback s allocated c.placement c.history c.entries m := by
  first
  | solve | simp only [snapshotStep_eq,Option.map_map,writeback]
  | rw [snapshotStep_eq,Option.map_map]
    unfold writeback
    apply congrArg (fun f => (updates allocated c.placement c.entries c.entries m).map f)
    funext us
    exact (realizeInventory_run allocated c.placement c.history us s c.placement c.history rfl c.entries).symm

/-- Successful physical steps preserve every original owner heap typing. -/
theorem snapshotStep_MemOK {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (m : ByteView) (next : Σ t,SnapshotCursor allocated t)
    (step : snapshotStep allocated s c m=some next)
    (H : Source.HeapTy) (ok : Source.MemOK E H s) : Source.MemOK E H next.1 := by
  have actual : writeback s allocated c.placement c.history c.entries m=some (.ok (),next.1) :=
    (snapshotStep_source allocated s c m).symm.trans (congrArg (Option.map (fun n => ((.ok () : Except Source.Halt Unit),n.1))) step)
  exact writeback_MemOK H s allocated c.placement c.history c.entries m _ actual ok

/-- Whole administrative state, original placement choices and exact heap
inventory metadata follow the actual writes; completeness is not assumed. -/
theorem snapshotStep_preserves {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (m : ByteView) (next : Σ t,SnapshotCursor allocated t)
    (step : snapshotStep allocated s c m=some next) :
    next.1=withSourceHeap s next.1.2.heap ∧ next.1.2.heap.ty=s.2.heap.ty ∧
    next.1.2.heap.next=s.2.heap.next ∧ next.2.placement.address=c.placement.address ∧
    next.2.placement.free=c.placement.free ∧
    next.2.entries.map MixedHeapEntry.id=c.entries.map MixedHeapEntry.id ∧
    (CoversMixedHeap c.entries → CoversMixedHeap next.2.entries) := by
  rw [snapshotStep_eq] at step
  obtain ⟨us,decoded,same⟩ := Option.map_eq_some_iff.mp step
  subst next
  dsimp only
  have choices := realizeInventory_choices allocated c.placement c.history us s.2.heap c.placement c.history rfl c.entries
  exact ⟨rfl,realizeInventory_types allocated c.placement c.history us s.2.heap c.placement c.history rfl c.entries,
    choices.2.2,choices.1,choices.2.1,realizeInventory_ids allocated c.placement c.history us s.2.heap c.placement c.history rfl c.entries,
    realizeInventory_coverage allocated c.placement c.history us s.2.heap c.placement c.history rfl c.entries⟩

/-- Every successful supplied snapshot is reconstructed as a COMPLETE byte map,
including residual words, without a caller-supplied final-view equation. -/
theorem snapshotStep_reencode {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (m : ByteView) (next : Σ t,SnapshotCursor allocated t)
    (step : snapshotStep allocated s c m=some next) :
    encodeMixedHeap next.2.placement next.2.entries m=m := by
  rw [snapshotStep_eq] at step
  obtain ⟨us,decoded,same⟩ := Option.map_eq_some_iff.mp step
  subst next
  let r := realizeInventory allocated c.placement c.history us s.2.heap c.placement c.history rfl c.entries
  have raw := updates_raw allocated c.placement c.entries c.entries m us decoded
  have ids := updates_ids allocated c.placement c.entries c.entries m us decoded
  have images := realizeInventory_images allocated c.placement c.history us s.2.heap c.placement c.history rfl c.entries m raw (by
    intro e member outside
    have present : e.id ∈ us.map (fun u => u.entry.id) := by
      rw [ids]
      exact List.mem_map.mpr ⟨e,member,rfl⟩
    obtain ⟨u,member,eq⟩ := List.mem_map.mp present
    exact False.elim (outside u member eq.symm))
  apply encodeMixedHeap_unchanged
  intro e member
  have reads := e.image.encode_reads m (r.placement.address e.id)
  rw [images e member] at reads
  exact reads

end Solidity.Yul.Views.MixedNominalInventory
