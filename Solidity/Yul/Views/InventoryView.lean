import Solidity.Yul.Views.InventorySnapshot

namespace Solidity.Yul.Views

theorem refreshed_image_encode {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (root : Nat) {τ : Source.STy} (d : Source.Data D τ) (ht : h.ty root = some τ)
    (q : Placement (h.write root d ht)) (addresses : q.address = p.address) (image : MemoryImage q d)
    (e : MixedHeapEntry p) (m : ByteView) :
    (refreshMixedEntry p root d ht q addresses image e).image.encode m
      (q.address (refreshMixedEntry p root d ht q addresses image e).id) =
      if e.id = root then image.encode m (q.address root) else e.image.encode m (p.address e.id) := by
  unfold refreshMixedEntry
  split
  · rename_i same; rw [dif_pos same]
  · rename_i different; rw [dif_neg different]
    rw [MemoryImage.transport_encode,addresses]

theorem realizeInventory_ids {E : Source.Env} {origin h : Source.Heap E.layout} (allocated : Placement origin)
    (p : Placement h) (snapshotHistory : RetainedAllocation allocated p) (us : List (OwnedInventoryUpdate allocated p))
    (current : Source.Heap E.layout) (q : Placement current) (history : RetainedAllocation allocated q)
    (types : current.ty = h.ty) (es : List (MixedHeapEntry q)) :
    (realizeInventory allocated p snapshotHistory us current q history types es).entries.map MixedHeapEntry.id = es.map MixedHeapEntry.id := by
  induction us generalizing current with
  | nil => rfl
  | cons u rest ih => exact (ih _ _ _ _ _).trans (refreshMixedEntries_ids _ _ _ _ _ _ _ es)

/-- Each matching snapshot image survives later writes, and a newly written
root obtains its actual decoded image. The initial outside condition is vacuous
for a complete decoded inventory; no desired final-view premise is assumed. -/
theorem realizeInventory_images {E : Source.Env} {origin h : Source.Heap E.layout} (allocated : Placement origin)
    (p : Placement h) (snapshotHistory : RetainedAllocation allocated p) (us : List (OwnedInventoryUpdate allocated p))
    (current : Source.Heap E.layout) (q : Placement current) (history : RetainedAllocation allocated q)
    (types : current.ty = h.ty) (es : List (MixedHeapEntry q)) (m : ByteView)
    (raw : ∀ u ∈ us, u.object.image.encode m (p.address u.entry.id) = m)
    (before : ∀ e ∈ es, (∀ u ∈ us, e.id ≠ u.entry.id) → e.image.encode m (q.address e.id) = m) :
    ∀ e ∈ (realizeInventory allocated p snapshotHistory us current q history types es).entries,
      e.image.encode m ((realizeInventory allocated p snapshotHistory us current q history types es).placement.address e.id) = m := by
  induction us generalizing current with
  | nil => exact fun e member => before e member (fun u member => by cases member)
  | cons u rest ih =>
    let ht : current.ty u.entry.id = some u.entry.ty := types ▸ heap_ty_of_get h u.entry.id _ _ u.entry.found
    let q2 := retainedWritePlacement allocated q history u.entry.id u.object.data ht u.object.shape u.object.shaped u.fits
    let r2 := retainWritten allocated q history u.entry.id u.object.data ht u.object.shape u.object.shaped u.fits
    let t2 := (funext (fun b => Source.Heap.write_ty current u.entry.id b u.object.data ht)).trans types
    let addr : q2.address = p.address := history.addresses.trans snapshotHistory.addresses.symm
    let image := u.object.image.transport q2 t2 addr
    let es2 := refreshMixedEntries q u.entry.id u.object.data ht q2 rfl image es
    apply ih (current.write u.entry.id u.object.data ht) q2 r2 t2 es2 (fun v member => raw v (List.mem_cons_of_mem _ member))
    intro f member outside
    obtain ⟨e,oldMember,same⟩ := List.mem_map.mp member
    subst f
    rw [refreshed_image_encode]
    by_cases eq : e.id = u.entry.id
    · rw [if_pos eq,MemoryImage.transport_encode,addr]
      exact raw u List.mem_cons_self
    · rw [if_neg eq]
      apply before e oldMember
      intro v mem
      rcases List.mem_cons.mp mem with same | later
      · subst v; exact eq
      · have no := outside v later
        rw [refreshMixedEntry_id] at no
        exact no

/-- A concrete final mixed heap view, with arbitrary preserved residual bytes,
for the full decoded inventory. All data/image evidence is constructor-derived. -/
theorem inventoryStateWriteback_view {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es)
    (distinct : (es.map MixedHeapEntry.id).Nodup) (m : ByteView)
    (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : inventoryStateWriteback s allocated p history es m = some result) :
    ∃ realized : InventoryRealization allocated,
      result = (.ok (),withSourceHeap s realized.heap) ∧ CoversMixedHeap realized.entries ∧
      (realized.entries.map MixedHeapEntry.id).Nodup ∧ encodeMixedHeap realized.placement realized.entries m = m := by
  obtain ⟨us,decoded,same⟩ := Option.map_eq_some_iff.mp step
  subst result
  let realized := realizeInventory allocated p history us s.2.heap p history rfl es
  have raw := decodeInventoryUpdates_raw allocated p es es m us decoded
  have ids := decodeInventoryUpdates_ids allocated p es es m us decoded
  have images := realizeInventory_images allocated p history us s.2.heap p history rfl es m raw (by
    intro e member outside
    have present : e.id ∈ us.map (fun u => u.entry.id) := by rw [ids]; exact List.mem_map.mpr ⟨e,member,rfl⟩
    obtain ⟨u,member,eq⟩ := List.mem_map.mp present
    exact False.elim (outside u member eq.symm))
  refine ⟨realized,realizeInventory_run allocated p history us s p history rfl es,
    realizeInventory_coverage allocated p history us s.2.heap p history rfl es coverage,?_,?_⟩
  · rw [realizeInventory_ids]; exact distinct
  · apply encodeMixedHeap_unchanged
    intro e member
    have reads := e.image.encode_reads m (realized.placement.address e.id)
    rw [images e member] at reads
    exact reads

theorem inventoryStateWriteback_reads {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es)
    (distinct : (es.map MixedHeapEntry.id).Nodup) (m : ByteView)
    (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : inventoryStateWriteback s allocated p history es m = some result) :
    ∃ realized : InventoryRealization allocated,
      result = (.ok (),withSourceHeap s realized.heap) ∧
      (∀ a τ (data : Source.Data E.layout τ) off w, realized.heap.get a = some ⟨τ,data⟩ →
        ObjectWord realized.placement.address data off w → mload m (realized.placement.address a+off) = w) ∧
      (∀ a τ (data : Source.Data E.layout τ) off b, realized.heap.get a = some ⟨τ,data⟩ →
        ObjectByte data off b → m (realized.placement.address a+off) = b) := by
  obtain ⟨realized,run,covers,nodup,same⟩ := inventoryStateWriteback_view s allocated p history es coverage distinct m result step
  refine ⟨realized,run,?_,?_⟩
  · intro a τ data off w found read
    have eq := encodeMixedHeap_source_word realized.placement realized.entries nodup covers m a τ data found off w read
    rw [same] at eq
    exact eq
  · intro a τ data off b found read
    have eq := encodeMixedHeap_source_byte realized.placement realized.entries nodup covers m a τ data found off b read
    rw [same] at eq
    exact eq

theorem inventoryStateWriteback_reserved {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es)
    (distinct : (es.map MixedHeapEntry.id).Nodup) (m : ByteView) (reserved : ReservedOK m p.free)
    (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : inventoryStateWriteback s allocated p history es m = some result) :
    ∃ realized : InventoryRealization allocated, result = (.ok (),withSourceHeap s realized.heap) ∧
      ReservedOK (encodeMixedHeap realized.placement realized.entries m) realized.placement.free := by
  obtain ⟨realized,run,covers,nodup,same⟩ := inventoryStateWriteback_view s allocated p history es coverage distinct m result step
  refine ⟨realized,run,?_⟩
  rw [same,realized.history.free,← history.free]
  exact reserved

end Solidity.Yul.Views
