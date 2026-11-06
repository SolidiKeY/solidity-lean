import Solidity.Yul.Views.AggregateStorageCollect

namespace Solidity.Yul.Views

/-- Stable first-occurrence union BEFORE constructing any typed codec. Natural
recursion over the actual finite visited/event list; no imposed size bound. -/
def uniqueVisitIndices (seen : List Nat) : List Nat → List Nat
  | [] => []
  | i::rest => if i ∈ seen then uniqueVisitIndices seen rest else i::uniqueVisitIndices (i::seen) rest

theorem uniqueVisitIndices_mem (seen xs : List Nat) (i : Nat) :
    i ∈ uniqueVisitIndices seen xs ↔ i ∈ xs ∧ i ∉ seen := by
  induction xs generalizing seen with
  | nil => simp only [uniqueVisitIndices,List.not_mem_nil,false_and]
  | cons head tail ih =>
    rw [uniqueVisitIndices]
    by_cases present : head ∈ seen
    · rw [if_pos present,ih]
      simp only [List.mem_cons]
      constructor
      · intro h; exact ⟨Or.inr h.1,h.2⟩
      · intro h
        rcases h.1 with same | inside
        · subst i; exact False.elim (h.2 present)
        · exact ⟨inside,h.2⟩
    · rw [if_neg present]
      simp only [List.mem_cons,ih]
      constructor
      · intro h
        rcases h with same | h
        · subst i; exact ⟨Or.inl rfl,present⟩
        · exact ⟨Or.inr h.1,fun inside => h.2 (Or.inr inside)⟩
      · intro h
        rcases h.1 with same | inside
        · exact Or.inl same
        · by_cases same : i=head
          · exact Or.inl same
          · exact Or.inr ⟨inside,fun h' => h'.elim same h.2⟩

theorem uniqueVisitIndices_nodup (seen xs : List Nat) : (uniqueVisitIndices seen xs).Nodup := by
  induction xs generalizing seen with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
    rw [uniqueVisitIndices]
    split
    · exact ih seen
    · apply List.nodup_cons.mpr
      refine ⟨?_,ih (head::seen)⟩
      intro member
      exact (uniqueVisitIndices_mem (head::seen) tail head).mp member |>.2 List.mem_cons_self

end Solidity.Yul.Views
