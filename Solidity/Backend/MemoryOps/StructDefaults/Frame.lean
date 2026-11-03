import Solidity.Backend.MemoryOps.StructDefaults.SourcePair

namespace Solidity.Backend.MemoryOps.StructDefaults

/-- The actual two allocations, in evaluator order. -/
def pairHeap {E : Source.Env} (h : Source.Heap E.layout) (dn : Source.DeclName)
    (fields : Source.DataList E.layout (E.layout.fields dn)) : Source.Heap E.layout :=
  ((h.alloc ⟨SourceBoolArrayTy, sourceBoolMemory []⟩).1.alloc
    ⟨.struct .memory dn, Source.Data.struct fields⟩).1

theorem pairHeap_cursor {E : Source.Env} (h : Source.Heap E.layout) (dn : Source.DeclName)
    (fields : Source.DataList E.layout (E.layout.fields dn)) :
    (pairHeap h dn fields).next = h.next+2 := by rfl

theorem pairHeap_child {E : Source.Env} (h : Source.Heap E.layout) (dn : Source.DeclName)
    (fields : Source.DataList E.layout (E.layout.fields dn)) :
    (pairHeap h dn fields).get h.next = some ⟨SourceBoolArrayTy, sourceBoolMemory []⟩ := by
  simp only [pairHeap, Source.Heap.alloc, Source.Heap.get, Nat.ne_add_one, if_false, if_true]

theorem pairHeap_parent {E : Source.Env} (h : Source.Heap E.layout) (dn : Source.DeclName)
    (fields : Source.DataList E.layout (E.layout.fields dn)) :
    (pairHeap h dn fields).get (h.next+1) =
      some ⟨.struct .memory dn, Source.Data.struct fields⟩ := by
  simp only [pairHeap, Source.Heap.alloc, Source.Heap.get, if_true]

/-- Any occupied old address keeps its object, so aliases of it keep theirs;
no distinctness or injectivity of aliases is needed. -/
theorem pairHeap_old {E : Source.Env} (h : Source.Heap E.layout) (dn : Source.DeclName)
    (fields : Source.DataList E.layout (E.layout.fields dn)) (a : Nat)
    (occupied : h.get a ≠ none) : (pairHeap h dn fields).get a = h.get a := by
  have below : a < h.next := by
    by_cases hn : a < h.next
    · exact hn
    · exact False.elim (occupied (h.bounded a (by omega)))
  have ne1 : a ≠ h.next := by omega
  have ne2 : a ≠ h.next+1 := by omega
  simp only [pairHeap, Source.Heap.alloc, Source.Heap.get, ne1, ne2, if_false]

/-- The unallocated source tail is still empty; this is a source-object fact,
not the separate intrinsic/word zero-region invariant. -/
theorem pairHeap_free {E : Source.Env} (h : Source.Heap E.layout) (dn : Source.DeclName)
    (fields : Source.DataList E.layout (E.layout.fields dn)) (a : Nat)
    (beyond : h.next+2 ≤ a) : (pairHeap h dn fields).get a = none := by
  exact (pairHeap h dn fields).bounded a beyond

/-- Explicit source failure control: no allocation has happened at fuel zero. -/
theorem pair_timeout {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (dn : Source.DeclName) :
    (Source.zeroVal (E := E) (Γ := Γ) 0 (.struct .memory dn)).run y =
      (.error .timeout, y) := by rfl

#print axioms pairHeap_old
#print axioms pairHeap_free
#print axioms pair_timeout
end Solidity.Backend.MemoryOps.StructDefaults
