import Solidity.Yul.Views.InventorySnapshot

namespace Solidity.Yul.Views

/-- Decode each original typed owned root against the CURRENT constructed
placement/candidates. Structural recursion consumes the actual finite inventory.
None is unsupported preparation, with no source/Yul result or rollback meaning. -/
def sequentialInventory {E : Source.Env} {origin h : Source.Heap E.layout} (allocated : Placement origin)
    (p : Placement h) (snapshotHistory : RetainedAllocation allocated p) :
    List (MixedHeapEntry p) → (current : Source.Heap E.layout) → (q : Placement current) →
      RetainedAllocation allocated q → current.ty = h.ty → List (MixedHeapEntry q) → ByteView → Option (InventoryRealization allocated)
  | [], current, q, history, _, es, _ => some ⟨current,q,history,es⟩
  | e::rest, current, q, history, types, es, m => do
    let o ← decodeInventoryObject q es e.ty m (q.address e.id)
    if fits : o.shape.size ≤ (allocated.shape e.id).size then
      let ht : current.ty e.id = some e.ty := types ▸ heap_ty_of_get h e.id e.ty e.data e.found
      let next := current.write e.id o.data ht
      let nextTypes : next.ty = h.ty := (funext (fun a => Source.Heap.write_ty current e.id a o.data ht)).trans types
      let nextPlacement := retainedWritePlacement allocated q history e.id o.data ht o.shape o.shaped fits
      let nextHistory := retainWritten allocated q history e.id o.data ht o.shape o.shaped fits
      let nextImage := o.image.transport nextPlacement (funext (fun a => Source.Heap.write_ty current e.id a o.data ht)) rfl
      let nextEntries := refreshMixedEntries q e.id o.data ht nextPlacement rfl nextImage es
      sequentialInventory allocated p snapshotHistory rest next nextPlacement nextHistory nextTypes nextEntries m
    else none

/-- Internal induction generalization; member agreement is derived from the
actual prior refresh and type/address transport at every recursive step. -/
theorem sequentialInventory_snapshot_aux {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (snapshotHistory : RetainedAllocation allocated p)
    (original : List (MixedHeapEntry p)) (entries : List (MixedHeapEntry p))
    (current : Source.Heap E.layout) (q : Placement current) (history : RetainedAllocation allocated q)
    (types : current.ty = h.ty) (es : List (MixedHeapEntry q))
    (addresses : q.address = p.address)
    (members : ∀ τ w, decodeExtendedMemoryMember q es τ w = decodeExtendedMemoryMember p original τ w)
    (m : ByteView) :
    sequentialInventory allocated p snapshotHistory entries current q history types es m =
      (decodeInventoryUpdates allocated p original entries m).map
        (fun us => realizeInventory allocated p snapshotHistory us current q history types es) := by
  induction entries generalizing current with
  | nil => rfl
  | cons e rest ih =>
    unfold sequentialInventory decodeInventoryUpdates decodeInventoryUpdate
    rw [addresses,decodeInventoryObject_transport p q types addresses original es members]
    cases dec : decodeInventoryObject p original e.ty m (p.address e.id) with
    | none => rfl
    | some o =>
      simp only [Option.map_some]
      dsimp only [InventoryObject.transport,Bind.bind,Pure.pure,Functor.map,Option.bind]
      by_cases capacity : o.shape.size ≤ (allocated.shape e.id).size
      · simp only [dif_pos capacity]
        let ht : current.ty e.id = some e.ty := types ▸ heap_ty_of_get h e.id _ _ e.found
        let next := current.write e.id o.data ht
        let nt : next.ty = h.ty := (funext (fun a => Source.Heap.write_ty current e.id a o.data ht)).trans types
        let nq := retainedWritePlacement allocated q history e.id o.data ht o.shape o.shaped capacity
        let nr := retainWritten allocated q history e.id o.data ht o.shape o.shaped capacity
        let ni := o.image.transport nq nt (history.addresses.trans snapshotHistory.addresses.symm)
        let nes := refreshMixedEntries q e.id o.data ht nq rfl ni es
        have stable : ∀ τ w, decodeExtendedMemoryMember nq nes τ w = decodeExtendedMemoryMember p original τ w :=
          fun τ w => (decodeExtended_refresh q e.id o.data ht nq rfl ni es τ w).trans (members τ w)
        have tail := ih next nq nr nt nes (history.addresses.trans snapshotHistory.addresses.symm) stable
        cases tailDec : decodeInventoryUpdates allocated p original rest m with
        | none => simpa only [tailDec,InventoryObject.transport,MemoryImage.transport_trans,Option.bind_some,Option.bind_none,Option.map_none,Option.map_map,realizeInventory,nes,ni,nq,nr,nt,next,ht] using tail
        | some us => simpa only [tailDec,InventoryObject.transport,MemoryImage.transport_trans,Option.bind_some,Option.map_some,Option.map_map,realizeInventory,nes,ni,nq,nr,nt,next,ht] using tail
      · simp only [dif_neg capacity,Option.map_none]

/-- Concrete finite closure: no decoder agreement or inverse is assumed at the
entry point. Exact equality includes all None cases and same-root repetitions. -/
theorem sequentialInventory_snapshot {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (history : RetainedAllocation allocated p)
    (es : List (MixedHeapEntry p)) (m : ByteView) :
    sequentialInventory allocated p history es h p history rfl es m =
      (decodeInventoryUpdates allocated p es es m).map (fun us => realizeInventory allocated p history us h p history rfl es) :=
  sequentialInventory_snapshot_aux allocated p history es es h p history rfl es rfl (fun _ _ => rfl) m

/-- Complete source result agreement. None remains absence of a supported
preparation result, never a source/Yul failure or no-op. -/
theorem inventoryStateWriteback_sequential {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p)) (m : ByteView) :
    inventoryStateWriteback s allocated p history es m =
      (sequentialInventory allocated p history es s.2.heap p history rfl es m).map
        (fun realized => ((.ok () : Except Source.Halt Unit),withSourceHeap s realized.heap)) := by
  unfold inventoryStateWriteback
  rw [sequentialInventory_snapshot,Option.map_map]
  apply congrArg (fun f => (decodeInventoryUpdates allocated p es es m).map f)
  funext us
  exact realizeInventory_run allocated p history us s p history rfl es

end Solidity.Yul.Views
