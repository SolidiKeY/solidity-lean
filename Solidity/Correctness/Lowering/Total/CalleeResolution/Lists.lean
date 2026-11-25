/-!
# List facts for callee name resolution

Generic facts used to read Source declaration filters over an assembled
function table: a filter of a list that corresponds pointwise to optional
translations is a `filterMap` of the original entries, and a `filterMap` with
exactly one productive position is a singleton.
-/
namespace Solidity.Correctness.Lowering.Total.CalleeResolution

/-- A filter over the successful translations of a list is the `filterMap` of
the original entries through the filtered translation. -/
theorem filter_of_map_some {α β : Type} (g : α → Option β) (p : β → Bool) :
    ∀ (F : List β) (l : List α), F.map some = l.map g →
      F.filter p = l.filterMap fun a => (g a).filter p
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | b :: F, a :: l, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨hb, ht⟩ := h
      rw [List.filterMap_cons, ← hb, List.filter_cons, filter_of_map_some g p F l ht]
      cases hp : p b <;> simp [Option.filter, hp]

/-- A `filterMap` whose only productive position is `i` is the singleton of
that position's result. -/
theorem filterMap_singleton {α β : Type} (g : α → Option β) :
    ∀ (l : List α) {i : Nat} {a : α} {o : β}, l[i]? = some a → g a = some o →
      (∀ j b o', l[j]? = some b → g b = some o' → j = i) → l.filterMap g = [o]
  | [], _, _, _, hi, _, _ => by cases hi
  | x :: xs, 0, a, o, hi, ho, hu => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      rw [List.filterMap_cons, ho, List.cons.injEq]
      refine ⟨rfl, List.filterMap_eq_nil_iff.mpr fun b hb => ?_⟩
      obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem hb
      cases hg : g b with
      | none => rfl
      | some o' =>
          have := hu (j + 1) b o' (by simp [hj, hjb]) hg
          omega
  | x :: xs, i + 1, a, o, hi, ho, hu => by
      have hx : g x = none := by
        cases hg : g x with
        | none => rfl
        | some o' => exact absurd (hu 0 x o' rfl hg) (by omega)
      rw [List.filterMap_cons, hx]
      exact filterMap_singleton g xs hi ho fun j b o' hj hb =>
        Nat.succ.inj (hu (j + 1) b o' (by simpa using hj) hb)

end Solidity.Correctness.Lowering.Total.CalleeResolution
