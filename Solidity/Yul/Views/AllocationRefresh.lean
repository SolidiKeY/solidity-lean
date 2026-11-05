import Solidity.Yul.Views.ComputedAllocationWrite

/-! Refresh computed coordinates after actual allocation without asserting
false equality on unoccupied future IDs. Occupied-address and free-pointer
agreement transports constructor-derived images, including real typed pointer
members. This supplies subsequent incremental encoders with derived old reads. -/
namespace Solidity.Yul.Views.AllocationRefresh
open ComputedPlacement

def placement {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (done : ComputedPlacement.prepare h=.ok p) {τ : Source.STy} (data : Source.Data D τ)
    (shape : MemoryShape) (found : objectShape data=some shape)
    (bound : p.free.val+max 1 shape.size<2^256) : Placement (h.alloc ⟨τ,data⟩).1 :=
  build (h.alloc ⟨τ,data⟩).1 (alloc_clear h ⟨τ,data⟩ (prepare_choices h p done).2.2.2 shape found)
    (by rw [alloc_end h ⟨τ,data⟩ shape found,←(prepare_choices h p done).2.2.1];exact bound)

theorem prepared {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (done : ComputedPlacement.prepare h=.ok p) {τ : Source.STy} (data : Source.Data D τ)
    (shape : MemoryShape) (found : objectShape data=some shape)
    (bound : p.free.val+max 1 shape.size<2^256) :
    ComputedPlacement.prepare (h.alloc ⟨τ,data⟩).1=.ok (placement h p done data shape found bound) := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact prepare_success _ _ _

theorem addresses {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (done : ComputedPlacement.prepare h=.ok p) {τ : Source.STy} (data : Source.Data D τ)
    (shape : MemoryShape) (found : objectShape data=some shape)
    (bound : p.free.val+max 1 shape.size<2^256) (a : Nat)
    (present : ((h.alloc ⟨τ,data⟩).1.cells a).isSome) :
    (ComputedAllocationWrite.placement h p done data shape found bound).address a=
      (placement h p done data shape found bound).address a := by
  first | (simp only;done) | decide | omega | rfl | skip
  have choices := prepare_choices h p done
  change (if a=h.next then p.free.val else p.address a)=position (h.alloc ⟨τ,data⟩).1 a
  by_cases fresh : a=h.next
  · subst a
    rw [if_pos rfl,alloc_position_prefix h ⟨τ,data⟩ h.next (Nat.le_refl _)]
    exact choices.2.2.1
  · have old : (h.cells a).isSome := by
      change ((h.alloc ⟨τ,data⟩).1.get a).isSome=true at present
      rw [Source.Heap.alloc_other h _ fresh] at present
      exact present
    have before := occupied_lt h a old
    rw [if_neg fresh,choices.1,alloc_position_prefix h ⟨τ,data⟩ a (by omega)]

theorem free {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (done : ComputedPlacement.prepare h=.ok p) {τ : Source.STy} (data : Source.Data D τ)
    (shape : MemoryShape) (found : objectShape data=some shape)
    (bound : p.free.val+max 1 shape.size<2^256) :
    (placement h p done data shape found bound).free=ComputedAllocationWrite.nextFree p shape bound := by
  first | (simp only;done) | decide | omega | rfl | skip
  apply Fin.ext
  change position (h.alloc ⟨τ,data⟩).1 (h.alloc ⟨τ,data⟩).1.next=p.free.val+max 1 shape.size
  rw [alloc_end h ⟨τ,data⟩ shape found,←(prepare_choices h p done).2.2.1]

theorem reads {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (done : ComputedPlacement.prepare h=.ok p) {τ : Source.STy} (data : Source.Data D τ)
    (shape : MemoryShape) (found : objectShape data=some shape)
    (bound : p.free.val+max 1 shape.size<2^256) (es : List (MixedHeapEntry p))
    (ready : prepareHeapInventory p=.ok es) (memory raw : ByteView)
    (oldReads : ∀ e∈es,e.image.Reads memory (p.address e.id))
    (step : ComputedAllocationWrite.prepare h p done data shape found bound memory=some raw)
    (e : MixedHeapEntry (placement h p done data shape found bound)) :
    e.image.Reads raw ((placement h p done data shape found bound).address e.id) := by
  first | (simp only;done) | decide | omega | rfl | skip
  let incremental := ComputedAllocationWrite.placement h p done data shape found bound
  let refreshed := placement h p done data shape found bound
  have extension : ∀ a σ,(h.alloc ⟨τ,data⟩).1.ty a=some σ →
      (h.alloc ⟨τ,data⟩).1.ty a=some σ ∧ incremental.address a=refreshed.address a := by
    intro a σ typed
    exact ⟨typed,addresses h p done data shape found bound a (heap_type_present _ a σ typed)⟩
  let forwarded : MixedHeapEntry incremental :=
    ⟨e.id,e.ty,e.data,e.found,e.image.forward incremental extension⟩
  have actual := objectAllocationView_image_reads h p data (objectShape_memory data shape found)
    shape (objectShape_sound data shape found) p.free.val (ComputedAllocationWrite.nextFree p shape bound)
    (Nat.le_refl _) (ComputedAllocationWrite.computed_fresh h p done) (by dsimp [ComputedAllocationWrite.nextFree];omega)
    es ready memory raw oldReads step forwarded
  have present : ((h.alloc ⟨τ,data⟩).1.cells e.id).isSome := by
    change ((h.alloc ⟨τ,data⟩).1.get e.id).isSome=true
    rw [e.found]
    rfl
  change (e.image.forward incremental extension).Reads raw (incremental.address e.id) at actual
  rw [addresses h p done data shape found bound e.id present] at actual
  exact (e.image.forward_reads incremental extension raw _).mp actual
/-- Subsequent allocation derives its old-image reads from the first checked
encoding. No second view/read/reconstruction law is supplied by the caller. -/
theorem resume {E Γ} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (done : ComputedPlacement.prepare s.2.heap=.ok p)
    {τ υ : Source.STy} (first : Source.Data E.layout τ) (firstShape : MemoryShape)
    (firstFound : objectShape first=some firstShape)
    (firstBound : p.free.val+max 1 firstShape.size<2^256)
    (memory raw : ByteView)
    (step : ComputedAllocationWrite.prepare s.2.heap p done first firstShape firstFound firstBound memory=some raw)
    (ok : Source.MemOK E H s) (firstInner : Source.Data.Inner (E:=E) first)
    (firstValid : Source.DataOK E s.2.heap.ty first) (firstSupported : InventoryTypeSupported E τ)
    (oldSupported : ∀ a σ d,s.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ)
    (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id))
    (second : Source.Data E.layout υ) (secondShape : MemoryShape)
    (secondFound : objectShape second=some secondShape)
    (secondBound : (placement s.2.heap p done first firstShape firstFound firstBound).free.val+
      max 1 secondShape.size<2^256)
    (secondInner : Source.Data.Inner (E:=E) second)
    (secondValid : Source.DataOK E (objectAllocatedState s first).2.heap.ty second)
    (secondSupported : InventoryTypeSupported E υ) :
    let current := objectAllocatedState s first
    let q := placement s.2.heap p done first firstShape firstFound firstBound
    let ready := prepared s.2.heap p done first firstShape firstFound firstBound
    let finalPlacement := ComputedAllocationWrite.placement current.2.heap q ready second secondShape secondFound secondBound
    let after := objectAllocatedState current second
    ∃ finalRaw, ComputedAllocationWrite.prepare current.2.heap q ready second secondShape secondFound secondBound raw=some finalRaw ∧
      (do let _ ← Source.allocRef first; Source.allocRef second : Source.EM E Γ (Source.Val E.layout υ)).run s=
        (.ok (.memRef (objectShape_memory second secondShape secondFound) current.2.heap.next),after) ∧
      Source.MemOK E H after ∧ encodeMixedHeap finalPlacement (generatedHeapEntries finalPlacement) finalRaw=finalRaw ∧
      enumeratedMemoryWriteback after finalPlacement finalPlacement (retainInitial _ _) finalRaw=.ok (some (.ok (),after)) := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  let current := objectAllocatedState s first
  let q := placement s.2.heap p done first firstShape firstFound firstBound
  have ready := prepared s.2.heap p done first firstShape firstFound firstBound
  have initialReady := ownerMemOK_prepares_inventory H s p ok oldSupported
  have derivedReads : ∀ e∈generatedHeapEntries q,e.image.Reads raw (q.address e.id) := by
    intro e _
    exact reads s.2.heap p done first firstShape firstFound firstBound _ initialReady memory raw oldReads step e
  have supported := heapAlloc_inventory_supported s.2.heap first firstSupported oldSupported
  have safe := (objectAllocRef_MemOK H s first (objectShape_memory first firstShape firstFound)
    (objectShape_top first firstShape firstFound) firstInner firstValid ok).1
  obtain ⟨finalRaw,next⟩ := Option.isSome_iff_exists.mp
    (ComputedAllocationWrite.complete current.2.heap q ready second secondShape secondFound secondBound raw
      secondSupported secondInner secondValid)
  have sound := ComputedAllocationWrite.sound H current q ready second secondShape secondFound secondBound
    raw finalRaw next safe secondInner secondValid secondSupported supported derivedReads
  refine ⟨finalRaw,next,?_,sound.2.1,sound.2.2.2.1,sound.2.2.2.2⟩
  rw [Source.Hoare.run_bind,objectAllocRef_run s first (objectShape_memory first firstShape firstFound)]
  exact objectAllocRef_run current second (objectShape_memory second secondShape secondFound)
end Solidity.Yul.Views.AllocationRefresh
