import Solidity.Frontend.OverrideValidation.Identity

/-!
# Finite declaration-graph routes

A route is an edge-by-edge derivation that consumes a departing occurrence.
The finite set is the graph itself, rather than a guessed recursion budget.
The decision procedure searches neighbours by declaration position; its
certificate retains endpoints and never quotients vertices by name or scope.
-/

namespace Solidity.Frontend.OverrideValidation

/-- An occurrence-consuming route. With duplicate-free availability a
departed vertex cannot be revisited. The terminal vertex need not be
available: reaching it is the success condition. -/
inductive Route {n : Nat} (edge : Fin n → Fin n → Bool) :
    List (Fin n) → Fin n → Fin n → Prop where
  | done {available : List (Fin n)} {a : Fin n} : Route edge available a a
  | step {available : List (Fin n)} {a b next : Fin n} :
      a ≠ b → a ∈ available → edge a next = true →
      Route edge (available.erase a) next b → Route edge available a b

theorem erase_length_lt {n : Nat} {available : List (Fin n)} {a : Fin n}
    (ha : a ∈ available) : (available.erase a).length < available.length := by
  rw [List.length_erase_of_mem ha]
  have hp : 0 < available.length := List.length_pos_of_mem ha
  omega

/-- Search the finite graph, deleting a departed vertex on every descent. -/
def routeB {n : Nat} (edge : Fin n → Fin n → Bool)
    (available : List (Fin n)) (a b : Fin n) : Bool :=
  if a = b then true
  else if a ∈ available then
    (List.finRange n).any fun next => edge a next && routeB edge (available.erase a) next b
  else false
termination_by available.length
decreasing_by
  apply erase_length_lt
  assumption

/-- Every successful search supplies an edge-by-edge route. -/
theorem routeB_sound {n : Nat} (edge : Fin n → Fin n → Bool)
    (available : List (Fin n)) (a b : Fin n)
    (h : routeB edge available a b = true) : Route edge available a b := by
  rw [routeB] at h
  split at h
  · rename_i hab
    subst b
    exact .done
  · rename_i hab
    split at h
    · rename_i ha
      obtain ⟨next, _, he⟩ := List.any_eq_true.mp h
      obtain ⟨he, hr⟩ := Bool.and_eq_true_iff.mp he
      exact .step hab ha he (routeB_sound edge (available.erase a) next b hr)
    · cases h
termination_by available.length
decreasing_by
  apply erase_length_lt
  assumption

/-- Every route is found; induction is on its relational derivation. -/
theorem routeB_complete {n : Nat} {edge : Fin n → Fin n → Bool}
    {available : List (Fin n)} {a b : Fin n}
    (h : Route edge available a b) : routeB edge available a b = true := by
  induction h with
  | done => rw [routeB]; exact if_pos rfl
  | @step available a b next hne ha he _ ih =>
    rw [routeB, if_neg hne, if_pos ha]
    exact List.any_eq_true.mpr ⟨next, List.mem_ofFn.mpr ⟨next, rfl⟩,
      Bool.and_eq_true_iff.mpr ⟨he, ih⟩⟩

/-- The search decides the independent edge-by-edge route judgment. -/
theorem routeB_iff {n : Nat} (edge : Fin n → Fin n → Bool)
    (available : List (Fin n)) (a b : Fin n) :
    routeB edge available a b = true ↔ Route edge available a b :=
  ⟨routeB_sound edge available a b, routeB_complete⟩

end Solidity.Frontend.OverrideValidation
