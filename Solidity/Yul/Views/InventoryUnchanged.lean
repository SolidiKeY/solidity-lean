import Solidity.Yul.Views.InventorySequential

namespace Solidity.Yul.Views

def InventoryTypeSupported (E : Source.Env) : Source.STy → Prop
  | .bytes .memory | .string .memory => True
  | .array _ τ _ => ExtendedMemberType E.layout τ
  | .struct _ name => ∀ τ ∈ E.layout.fields name, ExtendedMemberType E.layout τ
  | _ => False

theorem memoryShape_unique {D : Source.Layout} {τ : Source.STy} {d : Source.Data D τ} {a b : MemoryShape}
    (one : HasMemoryShape d a) (two : HasMemoryShape d b) : a = b := by
  cases one <;> cases two <;> rfl

/-- Extract the existing documented header and element reads from an actual
array image; bounds are the intrinsic old values/Placement, not a decoder cap. -/
theorem inventory_array_reads (k : Option Nat) (n : Nat) (hl : ∀ z, k = some z → z = n)
    (bound : n < 2^256) (words : Fin n → Roadmap.Word) (m : ByteView) (base : Nat)
    (reads : ∀ i w, ((if k.isNone then [⟨n,bound⟩] else []) ++ List.ofFn words)[i]? = some w → mload m (base+i*32) = w) :
    arrayLengthChoice k m base = n ∧ ∀ i, mload m (base+arrayPayloadOffset k+i.val*32) = words i := by
  have nth (i : Fin n) : (List.ofFn words)[i.val]? = some (words i) := by
    rw [List.getElem?_eq_getElem (by simp only [List.length_ofFn]; exact i.isLt),List.getElem_ofFn]
  cases k with
  | none =>
    have header := reads 0 ⟨n,bound⟩ rfl
    refine ⟨congrArg Fin.val header,?_⟩
    intro i
    have element := reads (i.val+1) (words i) (nth i)
    have eq : base+(i.val+1)*32 = base+32+i.val*32 := by omega
    simpa only [eq,arrayPayloadOffset,Option.isNone_none,if_true] using element
  | some z =>
    have eq := hl z rfl
    subst z
    exact ⟨rfl,fun i => reads i.val (words i) (nth i)⟩

theorem decodeInventoryObject_unchanged {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) (e : MixedHeapEntry p)
    (supported : InventoryTypeSupported E e.ty) (m : ByteView) (reads : e.image.Reads m (p.address e.id)) :
    ∃ o, decodeInventoryObject p es e.ty m (p.address e.id) = some o ∧ o.data = e.data := by
  rcases e with ⟨id,τ,data,found,image⟩
  cases image with
  | bytes bs bound =>
    exact ⟨snapshotBytes p m (p.address id),rfl,congrArg (Source.Data.bytes (D := E.layout) (l := .memory)) (by rw [reads.1]; exact reads.2)⟩
  | string bs bound =>
    exact ⟨snapshotString p m (p.address id),rfl,congrArg (Source.Data.string (D := E.layout) (l := .memory)) (by rw [reads.1]; exact reads.2)⟩
  | words data ws encoded =>
    cases encoded with
    | value v w element => exact False.elim (no_value_memory_shape v _ (p.typed id _ _ found))
    | @array l τ k n hl bound values words elements =>
      obtain ⟨header,elementsRead⟩ := inventory_array_reads k n hl bound words m (p.address id) reads
      have dec := decodeCanonicalArray_reads p es coverage τ supported n values words elements m _ elementsRead
      have mapData : (decodeInventoryObject p es (.array l τ k) m (p.address id)).map InventoryObject.data =
          some (.array n hl (fun i => .val (values i))) := by
        change (snapshotArray p es l τ k m (p.address id)).map InventoryObject.data = _
        cases header
        unfold snapshotArray
        dsimp only
        rw [dif_pos bound]
        rw [Option.pmap_some' dec,Option.map_some]
      obtain ⟨o,yes,same⟩ := Option.map_eq_some_iff.mp mapData
      exact ⟨o,yes,same⟩
    | @strct l name fs ws fields =>
      have dec := decodeCanonicalFields_reads p es coverage fields supported m (p.address id) reads
      have mapData : (decodeInventoryObject p es (.struct l name) m (p.address id)).map InventoryObject.data = some (.struct fs) := by
        change (snapshotStruct p es l name m (p.address id)).map InventoryObject.data = _
        unfold snapshotStruct
        rw [Option.pmap_some' dec,Option.map_some]
      obtain ⟨o,yes,same⟩ := Option.map_eq_some_iff.mp mapData
      exact ⟨o,yes,same⟩

theorem runInventoryUpdates_unchanged {E : Source.Env} {Γ : Source.RCtx} {origin h : Source.Heap E.layout}
    {allocated : Placement origin} {p : Placement h} (us : List (OwnedInventoryUpdate allocated p)) (s : Source.EMState E Γ)
    (same : ∀ u ∈ us, s.2.heap.get u.entry.id = some ⟨u.entry.ty,u.object.data⟩) :
    (runInventoryUpdates us).run s = (.ok (),s) := by
  induction us with
  | nil => rfl
  | cons u rest ih =>
    have found := same u List.mem_cons_self
    have first : (Source.heapPut u.entry.id ⟨u.entry.ty,u.object.data⟩ : Source.EM E Γ Unit).run s = (.ok (),s) := by
      rw [heapPutConcrete_run s _ _ (heap_ty_of_get s.2.heap u.entry.id _ _ found),heap_write_unchanged s.2.heap _ _ _ found,withSourceHeap_unchanged]
    rw [runInventoryUpdates,Source.Hoare.run_bind,first]
    exact ih (fun v member => same v (List.mem_cons_of_mem _ member))

theorem decodeInventoryUpdate_unchanged {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (history : RetainedAllocation allocated p)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) (e : MixedHeapEntry p)
    (supported : InventoryTypeSupported E e.ty) (m : ByteView) (reads : e.image.Reads m (p.address e.id)) :
    ∃ u, decodeInventoryUpdate allocated p es e m = some u ∧ h.get u.entry.id = some ⟨u.entry.ty,u.object.data⟩ := by
  obtain ⟨o,decoded,same⟩ := decodeInventoryObject_unchanged p es coverage e supported m reads
  have shape : o.shape = p.shape e.id := memoryShape_unique (same ▸ o.shaped) (p.typed e.id _ _ e.found)
  have present : (h.cells e.id).isSome := by change (h.get e.id).isSome = true; rw [e.found]; rfl
  have capacity : o.shape.size ≤ (allocated.shape e.id).size := by rw [shape]; exact history.fits e.id present
  refine ⟨⟨e,o,capacity⟩,?_,?_⟩
  · unfold decodeInventoryUpdate
    rw [decoded]
    change (if fits : o.shape.size ≤ (allocated.shape e.id).size then some (OwnedInventoryUpdate.mk e o fits) else none) = some (OwnedInventoryUpdate.mk e o capacity)
    rw [dif_pos capacity]
  · change h.get e.id = some ⟨e.ty,o.data⟩
    rw [same]; exact e.found

theorem decodeInventoryUpdates_unchanged {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (history : RetainedAllocation allocated p)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) (entries : List (MixedHeapEntry p))
    (supported : ∀ e ∈ entries, InventoryTypeSupported E e.ty) (m : ByteView)
    (reads : ∀ e ∈ entries, e.image.Reads m (p.address e.id)) :
    ∃ us, decodeInventoryUpdates allocated p es entries m = some us ∧
      ∀ u ∈ us, h.get u.entry.id = some ⟨u.entry.ty,u.object.data⟩ := by
  induction entries with
  | nil => exact ⟨[],rfl,fun u member => by cases member⟩
  | cons e entries ih =>
    obtain ⟨u,one,old⟩ := decodeInventoryUpdate_unchanged allocated p history es coverage e (supported e List.mem_cons_self) m (reads e List.mem_cons_self)
    obtain ⟨rest,tail,same⟩ := ih (fun v member => supported v (List.mem_cons_of_mem _ member)) (fun v member => reads v (List.mem_cons_of_mem _ member))
    refine ⟨u::rest,?_,?_⟩
    · unfold decodeInventoryUpdates
      rw [one,tail]
      rfl
    · intro v member
      rcases List.mem_cons.mp member with eq | later
      · subst v; exact old
      · exact same v later

theorem inventoryStateWriteback_unchanged {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es)
    (supported : ∀ e ∈ es, InventoryTypeSupported E e.ty) (m : ByteView)
    (reads : ∀ e ∈ es, e.image.Reads m (p.address e.id)) :
    inventoryStateWriteback s allocated p history es m = some (.ok (),s) := by
  obtain ⟨us,decoded,same⟩ := decodeInventoryUpdates_unchanged allocated p history es coverage es supported m reads
  unfold inventoryStateWriteback
  rw [decoded,Option.map_some,runInventoryUpdates_unchanged us s same]

end Solidity.Yul.Views
