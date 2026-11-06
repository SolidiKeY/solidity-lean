import Solidity.Yul.Views.OwnedInventory

namespace Solidity.Yul.Views

theorem realizeInventory_types {E : Source.Env} {origin h : Source.Heap E.layout} (allocated : Placement origin)
    (p : Placement h) (snapshotHistory : RetainedAllocation allocated p) (us : List (OwnedInventoryUpdate allocated p))
    (current : Source.Heap E.layout) (q : Placement current) (history : RetainedAllocation allocated q)
    (types : current.ty = h.ty) (es : List (MixedHeapEntry q)) :
    (realizeInventory allocated p snapshotHistory us current q history types es).heap.ty = h.ty := by
  induction us generalizing current with
  | nil => exact types
  | cons u rest ih => exact ih _ _ _ _ _

theorem realizeInventory_coverage {E : Source.Env} {origin h : Source.Heap E.layout} (allocated : Placement origin)
    (p : Placement h) (snapshotHistory : RetainedAllocation allocated p) (us : List (OwnedInventoryUpdate allocated p))
    (current : Source.Heap E.layout) (q : Placement current) (history : RetainedAllocation allocated q)
    (types : current.ty = h.ty) (es : List (MixedHeapEntry q)) (coverage : CoversMixedHeap es) :
    CoversMixedHeap (realizeInventory allocated p snapshotHistory us current q history types es).entries := by
  induction us generalizing current with
  | nil => exact coverage
  | cons u rest ih =>
    apply ih
    exact refreshMixedEntries_coverage _ _ _ _ _ _ _ _ coverage

theorem realizeInventory_choices {E : Source.Env} {origin h : Source.Heap E.layout} (allocated : Placement origin)
    (p : Placement h) (snapshotHistory : RetainedAllocation allocated p) (us : List (OwnedInventoryUpdate allocated p))
    (current : Source.Heap E.layout) (q : Placement current) (history : RetainedAllocation allocated q)
    (types : current.ty = h.ty) (es : List (MixedHeapEntry q)) :
    (realizeInventory allocated p snapshotHistory us current q history types es).placement.address = q.address ∧
    (realizeInventory allocated p snapshotHistory us current q history types es).placement.free = q.free ∧
    (realizeInventory allocated p snapshotHistory us current q history types es).heap.next = current.next := by
  induction us generalizing current with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons u rest ih => exact ih _ _ _ _ _

theorem realizeInventory_decoder {E : Source.Env} {origin h : Source.Heap E.layout} (allocated : Placement origin)
    (p : Placement h) (snapshotHistory : RetainedAllocation allocated p) (us : List (OwnedInventoryUpdate allocated p))
    (current : Source.Heap E.layout) (q : Placement current) (history : RetainedAllocation allocated q)
    (types : current.ty = h.ty) (es : List (MixedHeapEntry q)) (τ : Source.STy) (w : Roadmap.Word) :
    decodeExtendedMemoryMember (realizeInventory allocated p snapshotHistory us current q history types es).placement
      (realizeInventory allocated p snapshotHistory us current q history types es).entries τ w = decodeExtendedMemoryMember q es τ w := by
  induction us generalizing current with
  | nil => rfl
  | cons u rest ih =>
    exact (ih _ _ _ _ _).trans (decodeExtended_refresh q _ _ _ _ rfl _ es τ w)

theorem realizeInventory_run {E : Source.Env} {Γ : Source.RCtx} {origin h : Source.Heap E.layout} (allocated : Placement origin)
    (p : Placement h) (snapshotHistory : RetainedAllocation allocated p) (us : List (OwnedInventoryUpdate allocated p))
    (s : Source.EMState E Γ) (q : Placement s.2.heap) (history : RetainedAllocation allocated q)
    (types : s.2.heap.ty = h.ty) (es : List (MixedHeapEntry q)) :
    (runInventoryUpdates us).run s = (.ok (),withSourceHeap s
      (realizeInventory allocated p snapshotHistory us s.2.heap q history types es).heap) := by
  induction us generalizing s with
  | nil => exact congrArg (fun x : Source.EMState E Γ => ((.ok () : Except Source.Halt Unit),x)) (withSourceHeap_unchanged s).symm
  | cons u rest ih =>
    let ht : s.2.heap.ty u.entry.id = some u.entry.ty := types ▸ heap_ty_of_get h u.entry.id _ _ u.entry.found
    rw [runInventoryUpdates,Source.Hoare.run_bind,heapPutConcrete_run s u.entry.id u.object.data ht]
    simp only []
    exact ih _ _ _ _ _

theorem realizeInventory_other {E : Source.Env} {origin h : Source.Heap E.layout} (allocated : Placement origin)
    (p : Placement h) (snapshotHistory : RetainedAllocation allocated p) (us : List (OwnedInventoryUpdate allocated p))
    (current : Source.Heap E.layout) (q : Placement current) (history : RetainedAllocation allocated q)
    (types : current.ty = h.ty) (es : List (MixedHeapEntry q)) (a : Nat)
    (outside : ∀ u ∈ us, a ≠ u.entry.id) :
    (realizeInventory allocated p snapshotHistory us current q history types es).heap.get a = current.get a ∧
    (realizeInventory allocated p snapshotHistory us current q history types es).placement.shape a = q.shape a := by
  induction us generalizing current with
  | nil => exact ⟨rfl,rfl⟩
  | cons u rest ih =>
    let ht : current.ty u.entry.id = some u.entry.ty := types ▸ heap_ty_of_get h u.entry.id _ _ u.entry.found
    let q2 := retainedWritePlacement allocated q history u.entry.id u.object.data ht u.object.shape u.object.shaped u.fits
    let r2 := retainWritten allocated q history u.entry.id u.object.data ht u.object.shape u.object.shaped u.fits
    let t2 := (funext (fun b => Source.Heap.write_ty current u.entry.id b u.object.data ht)).trans types
    let image := u.object.image.transport q2 t2 (history.addresses.trans snapshotHistory.addresses.symm)
    let es2 := refreshMixedEntries q u.entry.id u.object.data ht q2 rfl image es
    have later := ih (current.write u.entry.id u.object.data ht) q2 r2 t2 es2 (fun v member => outside v (List.mem_cons_of_mem _ member))
    refine ⟨later.1.trans (Source.Heap.write_other current (outside u List.mem_cons_self) _ _),?_⟩
    refine later.2.trans ?_
    change (if a = u.entry.id then u.object.shape else q.shape a) = q.shape a
    rw [if_neg (outside u List.mem_cons_self)]

/-- Concrete closure over any complete actual supported inventory, not a
fixed root count or a list of assumed writeback laws. -/
theorem inventoryStateWriteback_realization {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es)
    (m : ByteView) (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : inventoryStateWriteback s allocated p history es m = some result) :
    ∃ realized : InventoryRealization allocated,
      result = (.ok (),withSourceHeap s realized.heap) ∧ CoversMixedHeap realized.entries ∧
      realized.heap.ty = s.2.heap.ty ∧ realized.heap.next = s.2.heap.next ∧
      realized.placement.address = p.address ∧ realized.placement.free = p.free ∧
      ∀ τ w, decodeExtendedMemoryMember realized.placement realized.entries τ w = decodeExtendedMemoryMember p es τ w := by
  obtain ⟨us,decoded,same⟩ := Option.map_eq_some_iff.mp step
  subst result
  let realized := realizeInventory allocated p history us s.2.heap p history rfl es
  have choices := realizeInventory_choices allocated p history us s.2.heap p history rfl es
  exact ⟨realized,realizeInventory_run allocated p history us s p history rfl es,
    realizeInventory_coverage allocated p history us s.2.heap p history rfl es coverage,
    realizeInventory_types allocated p history us s.2.heap p history rfl es,choices.2.2,choices.1,choices.2.1,
    realizeInventory_decoder allocated p history us s.2.heap p history rfl es⟩

end Solidity.Yul.Views
