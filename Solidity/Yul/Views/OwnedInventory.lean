import Solidity.Yul.Views.InventoryObjectLaws

/-! Decoded updates over an ACTUAL finite typed owned inventory. These are
indexed Source.Data objects and existing ownership witnesses, not a syntax/IR
or a second semantic state. Every proof below is derived from concrete decoders
and real Source.heapPut/Heap.write; no inverse/safety/output law inputs. -/
namespace Solidity.Yul.Views

structure OwnedInventoryUpdate {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) where
  entry : MixedHeapEntry p
  object : InventoryObject p entry.ty
  fits : object.shape.size ≤ (allocated.shape entry.id).size

def decodeInventoryUpdate {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (es : List (MixedHeapEntry p)) (e : MixedHeapEntry p)
    (m : ByteView) : Option (OwnedInventoryUpdate allocated p) := do
  let o ← decodeInventoryObject p es e.ty m (p.address e.id)
  if fits : o.shape.size ≤ (allocated.shape e.id).size then pure ⟨e,o,fits⟩ else none

def decodeInventoryUpdates {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (es : List (MixedHeapEntry p)) :
    List (MixedHeapEntry p) → ByteView → Option (List (OwnedInventoryUpdate allocated p))
  | [], _ => some []
  | e::rest, m => do
    let first ← decodeInventoryUpdate allocated p es e m
    let tail ← decodeInventoryUpdates allocated p es rest m
    pure (first::tail)

def runInventoryUpdates {E : Source.Env} {Γ : Source.RCtx} {origin h : Source.Heap E.layout}
    {allocated : Placement origin} {p : Placement h} : List (OwnedInventoryUpdate allocated p) → Source.EM E Γ Unit
  | [] => pure ()
  | u::rest => do
    Source.heapPut u.entry.id ⟨u.entry.ty,u.object.data⟩
    runInventoryUpdates rest

def inventoryStateWriteback {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (_history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p)) (m : ByteView) :
    Option (Except Source.Halt Unit × Source.EMState E Γ) :=
  (decodeInventoryUpdates allocated p es es m).map (fun updates => (runInventoryUpdates updates).run s)

theorem inventory_entry_bounded {E : Source.Env} {h : Source.Heap E.layout} {p : Placement h} (e : MixedHeapEntry p) : e.id < h.next := by
  apply Nat.lt_of_not_le
  intro absent
  have no := h.bounded e.id absent
  have found := e.found
  change h.cells e.id = some ⟨e.ty,e.data⟩ at found
  rw [no] at found
  cases found

/-- Complete error results keep actual types, including a successful prefix. -/
theorem runInventoryUpdates_types {E : Source.Env} {Γ : Source.RCtx} {origin h : Source.Heap E.layout}
    {allocated : Placement origin} {p : Placement h} (us : List (OwnedInventoryUpdate allocated p))
    (s : Source.EMState E Γ) : ((runInventoryUpdates us).run s).2.2.heap.ty = s.2.heap.ty := by
  induction us generalizing s with
  | nil => rfl
  | cons u rest ih =>
    have types := heapPutConcrete_types s u.entry.id u.object.data
    rw [runInventoryUpdates,Source.Hoare.run_bind]
    cases run : (Source.heapPut u.entry.id ⟨u.entry.ty,u.object.data⟩ : Source.EM E Γ Unit).run s with
    | mk result out =>
      have same : out.2.heap.ty = s.2.heap.ty := by simpa only [run] using types
      cases result with
      | error e => exact same
      | ok value => exact (ih out).trans same

/-- Real DataOK is enough for the general program, even at wrong/missing roots.
For decoded inventories it is derived below from intrinsic images and types. -/
theorem runInventoryUpdates_MemOK {E : Source.Env} {Γ : Source.RCtx} {origin h : Source.Heap E.layout}
    {allocated : Placement origin} {p : Placement h} (us : List (OwnedInventoryUpdate allocated p))
    (H : Source.HeapTy) (s : Source.EMState E Γ)
    (values : ∀ u ∈ us, Source.DataOK E s.2.heap.ty u.object.data) (ok : Source.MemOK E H s) :
    Source.MemOK E H ((runInventoryUpdates us).run s).2 := by
  induction us generalizing s with
  | nil => exact ok
  | cons u rest ih =>
    have first := heapPutConcrete_MemOK H s u.entry.id u.object.data (values u List.mem_cons_self)
      u.object.top u.object.image.inner ok
    have types := heapPutConcrete_types s u.entry.id u.object.data
    rw [runInventoryUpdates,Source.Hoare.run_bind]
    cases run : (Source.heapPut u.entry.id ⟨u.entry.ty,u.object.data⟩ : Source.EM E Γ Unit).run s with
    | mk result out =>
      have good : Source.MemOK E H out := by simpa only [run] using first
      cases result with
      | error e => exact good
      | ok value =>
        have same : out.2.heap.ty = s.2.heap.ty := by simpa only [run] using types
        exact ih out (fun v member => by rw [same]; exact values v (List.mem_cons_of_mem _ member)) good

theorem inventoryStateWriteback_MemOK {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (H : Source.HeapTy) (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p)) (m : ByteView)
    (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : inventoryStateWriteback s allocated p history es m = some result) (ok : Source.MemOK E H s) : Source.MemOK E H result.2 := by
  obtain ⟨updates,decoded,same⟩ := Option.map_eq_some_iff.mp step
  subst result
  exact runInventoryUpdates_MemOK updates H s (fun u _ => u.object.image.dataOK) ok

/-- A proof-carrying result containing the EXISTING actual heap, placement and
images. This is not an alternative source state; fields carry no assumed laws. -/
structure InventoryRealization {E : Source.Env} {origin : Source.Heap E.layout} (allocated : Placement origin) where
  heap : Source.Heap E.layout
  placement : Placement heap
  history : RetainedAllocation allocated placement
  entries : List (MixedHeapEntry placement)

/-- Structural recursion over actual finite inventory, no new cap. Each step
constructs a typed Heap.write, retained Placement, lineage and refreshed images. -/
def realizeInventory {E : Source.Env} {origin h : Source.Heap E.layout} (allocated : Placement origin)
    (p : Placement h) (snapshotHistory : RetainedAllocation allocated p) :
    List (OwnedInventoryUpdate allocated p) → (current : Source.Heap E.layout) → (q : Placement current) →
      RetainedAllocation allocated q → current.ty = h.ty → List (MixedHeapEntry q) → InventoryRealization allocated
  | [], current, q, history, _, es => ⟨current,q,history,es⟩
  | u::rest, current, q, history, types, es =>
    let ht : current.ty u.entry.id = some u.entry.ty := types ▸ heap_ty_of_get h u.entry.id u.entry.ty u.entry.data u.entry.found
    let next := current.write u.entry.id u.object.data ht
    let nextTypes : next.ty = h.ty := (funext (fun a => Source.Heap.write_ty current u.entry.id a u.object.data ht)).trans types
    let nextPlacement := retainedWritePlacement allocated q history u.entry.id u.object.data ht u.object.shape u.object.shaped u.fits
    let nextHistory := retainWritten allocated q history u.entry.id u.object.data ht u.object.shape u.object.shaped u.fits
    let addresses : nextPlacement.address = p.address := history.addresses.trans snapshotHistory.addresses.symm
    let nextImage := u.object.image.transport nextPlacement nextTypes addresses
    let nextEntries := refreshMixedEntries q u.entry.id u.object.data ht nextPlacement rfl nextImage es
    realizeInventory allocated p snapshotHistory rest next nextPlacement nextHistory nextTypes nextEntries

end Solidity.Yul.Views
