import Solidity.Yul.Views.HeapPreparationComplete

namespace Solidity.Yul.Views

theorem generatedHeapEntries_ids {D : Source.Layout} {h : Source.Heap D} (p : Placement h) :
    (generatedHeapEntries p).map MixedHeapEntry.id = (List.range h.next).filter (fun a => (heapEntryAt p a).isSome) := by
  have general (as : List Nat) : (as.filterMap (heapEntryAt p)).map MixedHeapEntry.id = as.filter (fun a => (heapEntryAt p a).isSome) := by
    induction as with
    | nil => rfl
    | cons a as ih =>
      cases yes : heapEntryAt p a with
      | none => simp only [List.filterMap_cons,yes,Option.isSome_none,List.filter_cons_of_neg,Bool.false_eq_true,not_false_eq_true,ih]
      | some e => simp only [List.filterMap_cons,yes,List.map_cons,Option.isSome_some,List.filter_cons_of_pos,heapEntryAt_id p a e yes,ih]
  exact general _

theorem generatedHeapEntries_nodup {D : Source.Layout} {h : Source.Heap D} (p : Placement h) :
    ((generatedHeapEntries p).map MixedHeapEntry.id).Nodup := by
  rw [generatedHeapEntries_ids]
  exact List.Pairwise.filter _ (List.nodup_range)

theorem heap_enumeration_exclusive {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (a : Nat) :
    (a ∈ missingHeapCells p → a ∉ unsupportedHeapCells p ∧ ∀ e ∈ generatedHeapEntries p, e.id ≠ a) ∧
    (a ∈ unsupportedHeapCells p → ∀ e ∈ generatedHeapEntries p, e.id ≠ a) := by
  constructor
  · intro missing
    have empty := (missingHeapCells_mem p a).mp missing
    constructor
    · intro bad
      have present := ((unsupportedHeapCells_mem p a).mp bad).2.1
      rw [empty.2] at present
      cases present
    · intro e member same
      have found := e.found
      rw [same,empty.2] at found
      cases found
  · intro bad e member same
    obtain ⟨b,_,yes⟩ := (generatedHeapEntries_mem p e).mp member
    have eq : b = a := (heapEntryAt_id p b e yes).symm.trans same
    subst b
    rw [((unsupportedHeapCells_mem p a).mp bad).2.2] at yes
    cases yes

theorem prepareHeapInventory_ok {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (prepared : prepareHeapInventory p = .ok es) :
    es = generatedHeapEntries p ∧ CoversMixedHeap es ∧ (es.map MixedHeapEntry.id).Nodup := by
  unfold prepareHeapInventory at prepared
  cases bad : unsupportedHeapCells p with
  | nil =>
    rw [bad] at prepared
    cases prepared
    exact ⟨rfl,generatedHeapEntries_coverage p bad,generatedHeapEntries_nodup p⟩
  | cons a as => rw [bad] at prepared; cases prepared

theorem prepareHeapInventory_error {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (bad : List Nat) (prepared : prepareHeapInventory p = .error bad) :
    bad = unsupportedHeapCells p ∧ bad ≠ [] ∧ ∀ a ∈ bad, (h.get a).isSome ∧ heapEntryAt p a = none := by
  unfold prepareHeapInventory at prepared
  cases unsupported : unsupportedHeapCells p with
  | nil => rw [unsupported] at prepared; cases prepared
  | cons a as =>
    rw [unsupported] at prepared
    cases prepared
    refine ⟨rfl,List.cons_ne_nil _ _,?_⟩
    intro b member
    exact ((unsupportedHeapCells_mem p b).mp (unsupported ▸ member)).2

end Solidity.Yul.Views
