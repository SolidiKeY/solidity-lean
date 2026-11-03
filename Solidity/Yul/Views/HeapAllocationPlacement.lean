import Solidity.Yul.Views.HeapBytePlacement

namespace Solidity.Yul.Views

theorem occupied_ne_next {D} (h : Source.Heap D) (a : Nat) (ha : (h.cells a).isSome) : a ≠ h.next := by
  intro same
  subst a
  rw [h.bounded _ (Nat.le_refl _)] at ha
  cases ha

theorem heap_alloc_old_present {D} (h : Source.Heap D) (x : Σ τ, Source.Data D τ) (a : Nat)
    (different : a ≠ h.next) : ((h.alloc x).1.cells a).isSome = true ↔ (h.cells a).isSome = true := by
  change ((h.alloc x).1.get a).isSome = true ↔ (h.get a).isSome = true
  rw [Source.Heap.alloc_other h x different]

/-- Construct the ACTUAL allocated heap's placement. Freshness of physical
addresses is separate from the automatically fresh logical Heap.next. No new
alignment/cap: base may equal oldfree when it is genuinely a fresh address. -/
def heapAllocPlacement {D} (h : Source.Heap D) (p : Placement h) {τ}
    (d : Source.Data D τ) (shape : MemoryShape) (typed : HasMemoryShape d shape)
    (base : Nat) (free : Roadmap.Word) (after : p.free.val ≤ base)
    (fresh : ∀ a, (h.cells a).isSome → p.address a ≠ base)
    (fits : base + shape.size ≤ free.val) : Placement (h.alloc ⟨τ,d⟩).1 where
  address a := if a=h.next then base else p.address a
  shape a := if a=h.next then shape else p.shape a
  free := free
  free_start := by have old := p.free_start; omega
  distinct a b ha hb same := by
    by_cases ea : a=h.next
    · by_cases eb : b=h.next
      · exact ea.trans eb.symm
      · have old := (heap_alloc_old_present h ⟨τ,d⟩ b eb).mp hb
        simp only [if_pos ea,if_neg eb] at same
        exact False.elim (fresh b old same.symm)
    · by_cases eb : b=h.next
      · have old := (heap_alloc_old_present h ⟨τ,d⟩ a ea).mp ha
        simp only [if_neg ea,if_pos eb] at same
        exact False.elim (fresh a old same)
      · exact p.distinct a b ((heap_alloc_old_present h ⟨τ,d⟩ a ea).mp ha)
          ((heap_alloc_old_present h ⟨τ,d⟩ b eb).mp hb) (by simpa only [if_neg ea,if_neg eb] using same)
  typed a σ x found := by
    change (h.alloc ⟨τ,d⟩).1.get a=some ⟨σ,x⟩ at found
    by_cases same : a=h.next
    · subst a
      change (h.alloc ⟨τ,d⟩).1.get (h.alloc ⟨τ,d⟩).2=some ⟨σ,x⟩ at found
      rw [Source.Heap.alloc_get] at found
      cases found
      simpa only [if_true] using typed
    · simp only [if_neg same]
      exact p.typed a σ x (by rw [Source.Heap.alloc_other h ⟨τ,d⟩ same] at found; exact found)
  starts a ha := by
    by_cases same : a=h.next
    · simp only [if_pos same]; exact Nat.le_trans p.free_start after
    · simp only [if_neg same]
      exact p.starts a ((heap_alloc_old_present h ⟨τ,d⟩ a same).mp ha)
  ends a ha := by
    by_cases same : a=h.next
    · simpa only [if_pos same] using fits
    · simp only [if_neg same]
      have old := p.ends a ((heap_alloc_old_present h ⟨τ,d⟩ a same).mp ha)
      omega
  separate a b ha hb different := by
    by_cases ea : a=h.next
    · by_cases eb : b=h.next
      · exact False.elim (different (ea.trans eb.symm))
      · simp only [if_pos ea,if_neg eb]
        exact Or.inr (Nat.le_trans (p.ends b ((heap_alloc_old_present h ⟨τ,d⟩ b eb).mp hb)) after)
    · by_cases eb : b=h.next
      · simp only [if_neg ea,if_pos eb]
        exact Or.inl (Nat.le_trans (p.ends a ((heap_alloc_old_present h ⟨τ,d⟩ a ea).mp ha)) after)
      · simpa only [if_neg ea,if_neg eb] using
          p.separate a b ((heap_alloc_old_present h ⟨τ,d⟩ a ea).mp ha)
            ((heap_alloc_old_present h ⟨τ,d⟩ b eb).mp hb) different

/-- Positive existing extents justify conventional allocation at oldfree.
No positivity is assumed for arbitrary owner heaps/metadata. -/
theorem heap_bump_fresh {D} (h : Source.Heap D) (p : Placement h)
    (positive : ∀ a, (h.cells a).isSome → 0 < (p.shape a).size) :
    ∀ a, (h.cells a).isSome → p.address a ≠ p.free.val := by
  intro a ha same
  have old := p.ends a ha
  have pos := positive a ha
  omega

theorem heap_later_fresh {D} (h : Source.Heap D) (p : Placement h) (base : Nat)
    (later : p.free.val < base) : ∀ a, (h.cells a).isSome → p.address a ≠ base := by
  intro a ha same
  have old := p.ends a ha
  omega

theorem heapAllocPlacement_old {D} (h : Source.Heap D) (p : Placement h) {τ}
    (d : Source.Data D τ) (shape : MemoryShape) (typed : HasMemoryShape d shape)
    (base : Nat) (free : Roadmap.Word) (after : p.free.val ≤ base)
    (fresh : ∀ a, (h.cells a).isSome → p.address a ≠ base) (fits : base+shape.size ≤ free.val)
    (a : Nat) (present : (h.cells a).isSome) :
    (heapAllocPlacement h p d shape typed base free after fresh fits).address a=p.address a ∧
      (heapAllocPlacement h p d shape typed base free after fresh fits).shape a=p.shape a := by
  have hn := occupied_ne_next h a present
  exact ⟨if_neg hn,if_neg hn⟩

end Solidity.Yul.Views
