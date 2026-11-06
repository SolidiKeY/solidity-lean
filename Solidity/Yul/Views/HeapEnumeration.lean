import Solidity.Yul.Views.HeapImagePreparation

/-! Actual finite heap enumeration. Empty cells are accounted separately from
occupied unsupported cells. No occupied failure is silently promoted to coverage. -/
namespace Solidity.Yul.Views

def heapEntryAt {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (a : Nat) : Option (MixedHeapEntry p) :=
  (h.get a).pbind (fun x found => (prepareHeapImage p a x.1 x.2 found).map (fun image => ⟨a,x.1,x.2,found,image⟩))

def generatedHeapEntries {D : Source.Layout} {h : Source.Heap D} (p : Placement h) : List (MixedHeapEntry p) :=
  (List.range h.next).filterMap (heapEntryAt p)

def missingHeapCells {D : Source.Layout} {h : Source.Heap D} (_p : Placement h) : List Nat :=
  (List.range h.next).filter (fun a => (h.get a).isNone)

def unsupportedHeapCells {D : Source.Layout} {h : Source.Heap D} (p : Placement h) : List Nat :=
  (List.range h.next).filter (fun a => (h.get a).isSome && (heapEntryAt p a).isNone)

/-- Fail closed for the WHOLE inventory: occupied unsupported cells are reported,
not silently dropped. Missing cells below next are legitimate sparse holes. -/
def prepareHeapInventory {D : Source.Layout} {h : Source.Heap D} (p : Placement h) : Except (List Nat) (List (MixedHeapEntry p)) :=
  match unsupportedHeapCells p with
  | [] => .ok (generatedHeapEntries p)
  | a::as => .error (a::as)

theorem heapEntryAt_id {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (a : Nat)
    (e : MixedHeapEntry p) (yes : heapEntryAt p a = some e) : e.id = a := by
  obtain ⟨x,found,prepared⟩ := Option.pbind_eq_some_iff.mp yes
  obtain ⟨image,_,same⟩ := Option.map_eq_some_iff.mp prepared
  cases same
  rfl

theorem heapEntryAt_present {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (a : Nat)
    (e : MixedHeapEntry p) (yes : heapEntryAt p a = some e) : (h.get a).isSome := by
  rw [← heapEntryAt_id p a e yes,e.found]; rfl

theorem generatedHeapEntries_mem {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (e : MixedHeapEntry p) :
    e ∈ generatedHeapEntries p ↔ ∃ a, a < h.next ∧ heapEntryAt p a = some e := by
  simp only [generatedHeapEntries,List.mem_filterMap,List.mem_range]

theorem generatedHeapEntries_id_bound {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (e : MixedHeapEntry p) (member : e ∈ generatedHeapEntries p) : e.id < h.next := by
  obtain ⟨a,bound,yes⟩ := (generatedHeapEntries_mem p e).mp member
  rw [heapEntryAt_id p a e yes]; exact bound

theorem unsupportedHeapCells_mem {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (a : Nat) :
    a ∈ unsupportedHeapCells p ↔ a < h.next ∧ (h.get a).isSome ∧ heapEntryAt p a = none := by
  simp only [unsupportedHeapCells,List.mem_filter,List.mem_range,Bool.and_eq_true,Option.isNone_iff_eq_none]

theorem missingHeapCells_mem {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (a : Nat) :
    a ∈ missingHeapCells p ↔ a < h.next ∧ h.get a = none := by
  simp only [missingHeapCells,List.mem_filter,List.mem_range,Option.isNone_iff_eq_none]

theorem heap_enumeration_partition {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (a : Nat) (bound : a < h.next) :
    (a ∈ missingHeapCells p ∨ a ∈ unsupportedHeapCells p ∨ ∃ e ∈ generatedHeapEntries p, e.id = a) := by
  cases found : h.get a with
  | none => exact Or.inl ((missingHeapCells_mem p a).mpr ⟨bound,found⟩)
  | some x =>
    cases ready : heapEntryAt p a with
    | none => exact Or.inr (Or.inl ((unsupportedHeapCells_mem p a).mpr ⟨bound,by rw [found]; rfl,ready⟩))
    | some e => exact Or.inr (Or.inr ⟨e,(generatedHeapEntries_mem p e).mpr ⟨a,bound,ready⟩,heapEntryAt_id p a e ready⟩)

theorem generatedHeapEntries_coverage {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (supported : unsupportedHeapCells p = []) : CoversMixedHeap (generatedHeapEntries p) := by
  intro a present
  have bound : a < h.next := by
    apply Nat.lt_of_not_le
    intro no
    have empty := h.bounded a (by omega)
    rw [empty] at present
    cases present
  rcases heap_enumeration_partition p a bound with absent | unsupported | ready
  · have empty := (missingHeapCells_mem p a).mp absent
    change (h.get a).isSome = true at present
    rw [empty.2] at present
    cases present
  · rw [supported] at unsupported; cases unsupported
  · exact ready

/-- Exact successful correspondence: the enumerated entry has the original
intrinsic declared type/data/found lookup, and an actually computed image. -/
theorem heapEntryAt_image {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (a : Nat)
    (e : MixedHeapEntry p) (yes : heapEntryAt p a = some e) :
    prepareHeapImage p e.id e.ty e.data e.found = some e.image := by
  obtain ⟨x,found,prepared⟩ := Option.pbind_eq_some_iff.mp yes
  obtain ⟨image,ready,same⟩ := Option.map_eq_some_iff.mp prepared
  cases same
  exact ready

end Solidity.Yul.Views
