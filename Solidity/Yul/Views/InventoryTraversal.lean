import Solidity.Yul.Views.InventorySnapshot

/-! The shared typed planning step for sequential inventory preparation.
Both legacy and nominal traversals use this exact decode/capacity/write/refresh
logic. The decoder returns existing intrinsic objects, with no assumed laws. -/
namespace Solidity.Yul.Views

abbrev InventoryDecoder (E : Source.Env) :=
  {h : Source.Heap E.layout} → (p : Placement h) → List (MixedHeapEntry p) →
    (τ : Source.STy) → ByteView → Nat → Option (InventoryObject p τ)

def inventoryStep {E : Source.Env} (decodeObject : InventoryDecoder E)
    {origin h : Source.Heap E.layout} (allocated : Placement origin) (p : Placement h)
    (e : MixedHeapEntry p) (current : Source.Heap E.layout) (q : Placement current)
    (history : RetainedAllocation allocated q) (types : current.ty=h.ty)
    (es : List (MixedHeapEntry q)) (m : ByteView)
    (continueWith : (next : Source.Heap E.layout) → (nq : Placement next) →
      RetainedAllocation allocated nq → next.ty=h.ty → List (MixedHeapEntry nq) →
      Option (InventoryRealization allocated)) : Option (InventoryRealization allocated) := do
    let o ← decodeObject q es e.ty m (q.address e.id)
    if fits : o.shape.size ≤ (allocated.shape e.id).size then
      let ht : current.ty e.id = some e.ty := types ▸ heap_ty_of_get h e.id e.ty e.data e.found
      let next := current.write e.id o.data ht
      let nextTypes : next.ty = h.ty := (funext (fun a => Source.Heap.write_ty current e.id a o.data ht)).trans types
      let nextPlacement := retainedWritePlacement allocated q history e.id o.data ht o.shape o.shaped fits
      let nextHistory := retainWritten allocated q history e.id o.data ht o.shape o.shaped fits
      let nextImage := o.image.transport nextPlacement (funext (fun a => Source.Heap.write_ty current e.id a o.data ht)) rfl
      let nextEntries := refreshMixedEntries q e.id o.data ht nextPlacement rfl nextImage es
      continueWith next nextPlacement nextHistory nextTypes nextEntries
    else none

/-- Structural list recursion only; all physical planning is in inventoryStep.
None is unsupported preparation, never a Source/Yul verdict or rollback. -/
def sequentialInventoryWith {E : Source.Env} (decodeObject : InventoryDecoder E)
    {origin h : Source.Heap E.layout} (allocated : Placement origin)
    (p : Placement h) (snapshotHistory : RetainedAllocation allocated p) :
    List (MixedHeapEntry p) → (current : Source.Heap E.layout) → (q : Placement current) →
      RetainedAllocation allocated q → current.ty=h.ty → List (MixedHeapEntry q) →
      ByteView → Option (InventoryRealization allocated)
  | [],current,q,history,_,es,_ => some ⟨current,q,history,es⟩
  | e::rest,current,q,history,types,es,m =>
    inventoryStep decodeObject allocated p e current q history types es m
      (fun next nq nh nt nes => sequentialInventoryWith decodeObject allocated p snapshotHistory rest next nq nh nt nes m)

end Solidity.Yul.Views
