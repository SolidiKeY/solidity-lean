import Solidity.AST

/-!
# First-match positions of `Semantics.lookupBy`

`Semantics.lookupBy` answers the value of the first entry whose key matches.
`firstIndex` names that entry's position in the original ordered list, so a
successful lookup can be connected to a position-indexed construction. Later
entries with the same key are shadowed; the lookup never reports them and no
uniqueness of keys is assumed.
-/
namespace Solidity.Correctness.Lowering.Total.CalleeAliases

open Semantics (lookupBy)

/-- Position of the first entry whose key is `k`, if any. -/
def firstIndex {κ α : Type} [DecidableEq κ] (k : κ) : List (κ × α) → Option Nat
  | [] => none
  | (k', _) :: rest => if k = k' then some 0 else (firstIndex k rest).map (· + 1)

variable {κ α : Type} [DecidableEq κ]

/-- A successful lookup is exactly a first match: the value sits at a position
whose key is `k`, and every earlier key differs from `k`. -/
theorem lookupBy_eq_some_iff {k : κ} {v : α} :
    ∀ {l : List (κ × α)}, lookupBy k l = some v ↔
      ∃ i, firstIndex k l = some i ∧ l[i]? = some (k, v)
  | [] => by simp [lookupBy, firstIndex]
  | (k', v') :: rest => by
      by_cases h : k = k'
      · subst h
        simp only [lookupBy, firstIndex, if_true, Option.some.injEq]
        constructor
        · rintro rfl; exact ⟨0, rfl, rfl⟩
        · rintro ⟨i, rfl, hi⟩; simpa using hi
      · simp only [lookupBy, firstIndex, h, if_false, lookupBy_eq_some_iff,
          Option.map_eq_some_iff]
        constructor
        · rintro ⟨i, hi, hv⟩; exact ⟨i + 1, ⟨i, hi, rfl⟩, by simpa using hv⟩
        · rintro ⟨_, ⟨i, hi, rfl⟩, hv⟩; exact ⟨i, hi, by simpa using hv⟩

/-- The first-match position holds an entry with key `k`. -/
theorem firstIndex_key {k : κ} :
    ∀ {l : List (κ × α)} {i}, firstIndex k l = some i → ∃ v, l[i]? = some (k, v)
  | [], _, h => by cases h
  | (k', v') :: rest, i, h => by
      by_cases hk : k = k'
      · subst hk; simp only [firstIndex, if_true, Option.some.injEq] at h; subst h
        exact ⟨v', rfl⟩
      · simp only [firstIndex, hk, if_false, Option.map_eq_some_iff] at h
        obtain ⟨j, hj, rfl⟩ := h
        simpa using firstIndex_key hj

/-- Shadowing boundary: no entry before the first-match position has key `k`. -/
theorem firstIndex_before {k : κ} :
    ∀ {l : List (κ × α)} {i j}, firstIndex k l = some i → j < i →
      ∀ e, l[j]? = some e → e.1 ≠ k
  | [], _, _, h, _, _, _ => by cases h
  | (k', v') :: rest, i, j, h, hj, e, he => by
      by_cases hk : k = k'
      · subst hk; simp only [firstIndex, if_true, Option.some.injEq] at h; omega
      · simp only [firstIndex, hk, if_false, Option.map_eq_some_iff] at h
        obtain ⟨i', hi', rfl⟩ := h
        cases j with
        | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at he
                  subst he; exact Ne.symm hk
        | succ j => exact firstIndex_before (j := j) hi' (by omega) e (by simpa using he)

/-- The first-match position is the least position with key `k`: any entry
with key `k` lies at or after it. Duplicate keys are allowed and shadowed. -/
theorem firstIndex_le {k : κ} {l : List (κ × α)} {i j v}
    (h : firstIndex k l = some i) (hj : l[j]? = some (k, v)) : i ≤ j :=
  Nat.not_lt.mp fun hlt => firstIndex_before h hlt _ hj rfl

/-- Failure boundary: the first-match search fails exactly when no key is `k`. -/
theorem firstIndex_eq_none_iff {k : κ} :
    ∀ {l : List (κ × α)}, firstIndex k l = none ↔ ∀ e ∈ l, e.1 ≠ k
  | [] => by simp [firstIndex]
  | (k', v') :: rest => by
      by_cases hk : k = k'
      · subst hk; simp [firstIndex]
      · simp only [firstIndex, hk, if_false, Option.map_eq_none_iff, firstIndex_eq_none_iff,
          List.mem_cons, forall_eq_or_imp]
        exact ⟨fun h => ⟨Ne.symm hk, h⟩, fun h => h.2⟩

/-- Lookup fails exactly when the first-match search does. -/
theorem lookupBy_eq_none_iff {k : κ} {l : List (κ × α)} :
    lookupBy k l = none ↔ firstIndex k l = none := by
  constructor
  · intro h
    cases hi : firstIndex k l with
    | none => rfl
    | some i =>
        obtain ⟨v, hv⟩ := firstIndex_key hi
        cases (h.symm.trans ((Iff.mpr lookupBy_eq_some_iff) ⟨i, hi, hv⟩))
  · intro h
    cases hv : lookupBy k l with
    | none => rfl
    | some v =>
        obtain ⟨i, hi, _⟩ := Iff.mp lookupBy_eq_some_iff hv
        cases h.symm.trans hi

/-- An entry preceded only by other keys is found, whatever follows it,
including later entries with the same key. -/
theorem lookupBy_shadow {k : κ} {v : α} (pre post : List (κ × α))
    (hpre : ∀ e ∈ pre, e.1 ≠ k) : lookupBy k (pre ++ (k, v) :: post) = some v := by
  induction pre with
  | nil => simp [lookupBy]
  | cons e pre ih =>
      obtain ⟨k', v'⟩ := e
      have hk : k ≠ k' := fun h => hpre _ (List.mem_cons_self ..) h.symm
      simp only [List.cons_append, lookupBy, hk, if_false]
      exact ih fun e he => hpre e (List.mem_cons_of_mem _ he)

/-- A filter with a single result has a single satisfying position. -/
theorem filter_singleton_index {β : Type} {p : β → Bool} {o : β} :
    ∀ {l : List β}, l.filter p = [o] → ∀ {i j : Nat} {x y : β}, l[i]? = some x → p x = true →
      l[j]? = some y → p y = true → i = j
  | [], h, _, _, _, _, _, _, _, _ => by cases h
  | a :: l, h, i, j, x, y, hi, hx, hj, hy => by
      by_cases ha : p a = true
      · simp only [List.filter_cons, ha, if_true, List.cons.injEq] at h
        have hnil : ∀ z ∈ l, ¬ p z = true := List.filter_eq_nil_iff.mp h.2
        cases i with
        | zero => cases j with
          | zero => rfl
          | succ j => exact absurd hy (hnil y (List.mem_of_getElem? (by simpa using hj)))
        | succ i => exact absurd hx (hnil x (List.mem_of_getElem? (by simpa using hi)))
      · simp only [List.filter_cons, ha] at h
        cases i with
        | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
                  subst hi; exact absurd hx ha
        | succ i => cases j with
          | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
                    subst hj; exact absurd hy ha
          | succ j => simpa using filter_singleton_index (l := l) (by simpa using h)
                        (by simpa using hi) hx (by simpa using hj) hy

end Solidity.Correctness.Lowering.Total.CalleeAliases
