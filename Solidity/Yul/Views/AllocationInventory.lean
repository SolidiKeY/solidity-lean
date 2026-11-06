import Solidity.Yul.Views.EnumeratedMemory
import Solidity.Yul.Views.RetainedHeapAllocation
import Solidity.Yul.Views.HeapAllocationReads

/-! Actual allocation extends the computed ordinary heap inventory. Sparse
holes stay holes; occupied unsupported cells never become implicit coverage.
The existing owner MemOK and supported declared types construct preparation. -/
namespace Solidity.Yul.Views

theorem heapAlloc_inventory_supported {E : Source.Env} (h : Source.Heap E.layout)
    {τ : Source.STy} (d : Source.Data E.layout τ) (newSupport : InventoryTypeSupported E τ)
    (supported : ∀ a σ x, h.get a=some ⟨σ,x⟩ → InventoryTypeSupported E σ) :
    ∀ a σ x, (h.alloc ⟨τ,d⟩).1.get a=some ⟨σ,x⟩ → InventoryTypeSupported E σ := by
  intro a σ x found
  by_cases same : a=h.next
  · subst a
    rw [show (h.alloc ⟨τ,d⟩).1.get h.next=some ⟨τ,d⟩ from Source.Heap.alloc_get h _] at found
    cases found
    exact newSupport
  · rw [Source.Heap.alloc_other h ⟨τ,d⟩ same] at found
    exact supported a σ x found

/-- Actual typed writes preserve the declared support profile; the old type
is recovered from the real heap lookup, not a supplied target support law. -/
theorem heapWrite_inventory_supported {E : Source.Env} (h : Source.Heap E.layout)
    (a : Nat) {τ : Source.STy} (d : Source.Data E.layout τ) (typed : h.ty a=some τ)
    (supported : ∀ b σ x, h.get b=some ⟨σ,x⟩ → InventoryTypeSupported E σ) :
    ∀ b σ x, (h.write a d typed).get b=some ⟨σ,x⟩ → InventoryTypeSupported E σ := by
  have target : InventoryTypeSupported E τ := by
    change (h.get a).map Sigma.fst=some τ at typed
    obtain ⟨⟨σ,old⟩,found,same⟩ := Option.map_eq_some_iff.mp typed
    cases same
    exact supported a σ old found
  intro b σ x found
  by_cases same : b=a
  · subst b
    rw [Source.Heap.write_get] at found
    cases found
    exact target
  · rw [Source.Heap.write_other h same d typed] at found
    exact supported b σ x found

theorem heapEntryAt_isSome_of_prepared {D : Source.Layout} {h : Source.Heap D}
    (p : Placement h) (es : List (MixedHeapEntry p)) (prepared : prepareHeapInventory p=.ok es) (a : Nat) :
    (heapEntryAt p a).isSome=(h.get a).isSome := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro yes
    obtain ⟨e,found⟩ := Option.isSome_iff_exists.mp yes
    exact heapEntryAt_present p a e found
  · intro present
    obtain ⟨e,member,same⟩ := (prepareHeapInventory_ok p es prepared).2.1 a present
    have entry := (prepareHeapInventory_ok p es prepared).1
    rw [entry] at member
    obtain ⟨b,_,ready⟩ := (generatedHeapEntries_mem p e).mp member
    have eq : b=a := (heapEntryAt_id p b e ready).symm.trans same
    subst b
    rw [ready]
    rfl

theorem generatedHeapEntries_occupied_ids {D : Source.Layout} {h : Source.Heap D}
    (p : Placement h) (es : List (MixedHeapEntry p)) (prepared : prepareHeapInventory p=.ok es) :
    (generatedHeapEntries p).map MixedHeapEntry.id =
      (List.range h.next).filter (fun a => (h.get a).isSome) := by
  rw [generatedHeapEntries_ids]
  exact List.filter_congr (fun a _ => heapEntryAt_isSome_of_prepared p es prepared a)

/-- The actual allocation adds exactly its fresh ID, in declaration-independent
heap order. No equality of dependent entries across different placements is
asserted. Both successful preparations are checked operations, not view laws. -/
theorem heapAlloc_generated_ids {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    {τ : Source.STy} (d : Source.Data D τ) (q : Placement (h.alloc ⟨τ,d⟩).1)
    (es : List (MixedHeapEntry p)) (qs : List (MixedHeapEntry q))
    (before : prepareHeapInventory p=.ok es) (after : prepareHeapInventory q=.ok qs) :
    (generatedHeapEntries q).map MixedHeapEntry.id =
      (generatedHeapEntries p).map MixedHeapEntry.id ++ [h.next] := by
  rw [generatedHeapEntries_occupied_ids p es before,generatedHeapEntries_occupied_ids q qs after]
  change ((List.range (h.next+1)).filter (fun a => ((h.alloc ⟨τ,d⟩).1.get a).isSome)) = _
  rw [List.range_succ,List.filter_append]
  have old : (List.range h.next).filter (fun a => ((h.alloc ⟨τ,d⟩).1.get a).isSome)=
      (List.range h.next).filter (fun a => (h.get a).isSome) := by
    apply List.filter_congr
    intro a member
    rw [Source.Heap.alloc_other h ⟨τ,d⟩ (by change a≠h.next; have bound := List.mem_range.mp member; omega)]
  rw [old]
  have fresh : (h.alloc ⟨τ,d⟩).1.get h.next=some ⟨τ,d⟩ := Source.Heap.alloc_get h _
  simp only [List.filter_cons, fresh,Option.isSome_some,ite_true,List.filter_nil]

/-- Computed coverage and unique fresh-ID extension follow from the real owner
state invariants, old declared support and a valid actual output placement.
No manual inventory, inverse, output-view or safety witness is an input. -/
theorem byteAllocated_inventory {E Γ} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (string : Bool) (bs : List UInt8)
    (q : Placement (byteAllocatedState s string bs).2.heap) (ok : Source.MemOK E H s)
    (supported : ∀ a τ d, s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ) :
    prepareHeapInventory q=.ok (generatedHeapEntries q) ∧ CoversMixedHeap (generatedHeapEntries q) ∧
      ((generatedHeapEntries q).map MixedHeapEntry.id).Nodup ∧
      (generatedHeapEntries q).map MixedHeapEntry.id=(generatedHeapEntries p).map MixedHeapEntry.id ++ [s.2.heap.next] := by
  have newSupport : InventoryTypeSupported E (heapByteType string) := by cases string <;> trivial
  have extended := heapAlloc_inventory_supported s.2.heap (heapByteData E.layout string bs) newSupport supported
  have prepared := ownerMemOK_prepares_inventory H (byteAllocatedState s string bs) q
    (byteAllocRef_MemOK s string bs H ok) extended
  have facts := prepareHeapInventory_ok q _ prepared
  exact ⟨prepared,facts.2.1,facts.2.2,heapAlloc_generated_ids s.2.heap p (heapByteData E.layout string bs) q _ _
    (ownerMemOK_prepares_inventory H s p ok supported) prepared⟩

end Solidity.Yul.Views
