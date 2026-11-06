import Solidity.Frontend.ExpressionUniqueness.YieldBalance

/-!
# Function-type attribute layout preserves delimiter balance

Only the existing token-layout combinators are analyzed. This is required by
`new` and `type` expression descendants containing arbitrary function types.
It proves no statement, function or unit uniqueness result.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def BalancedAttrs (entries : List (Slot × List Tok)) : Prop :=
  ∀ entry, entry ∈ entries → Balanced entry.2

theorem balancedAttrs_append {xs ys : List (Slot × List Tok)}
    (hx : BalancedAttrs xs) (hy : BalancedAttrs ys) : BalancedAttrs (xs ++ ys) := by
  intro entry h
  rcases List.mem_append.mp h with h | h
  · exact hx entry h
  · exact hy entry h

theorem balanced_single (slot : Slot) (ts : List Tok) (h : Balanced ts) :
    BalancedAttrs (single slot ts) := by
  unfold single
  split
  · intro entry he; cases he
  · intro entry he
    have heq : entry = (slot, ts) := by simpa only [List.mem_singleton] using he
    exact heq ▸ h

theorem arrange_nonModifier (slot : Slot) (h : slot ≠ .modInv)
    (order : List Slot) (singles : List (Slot × List Tok)) (mods : List (List Tok)) :
    arrange (slot :: order) singles mods =
      (singles.find? (·.1 == slot)).bind (fun entry =>
        (arrange order (singles.filter (·.1 != slot)) mods).map (entry.2 ++ ·)) := by
  cases slot <;> first
    | exact False.elim (h rfl)
    | (cases mods <;> simp only [arrange, beq_iff_eq, h, ↓reduceIte, Option.bind] <;> split <;> rename_i heq <;> rw [heq])

theorem arrange_balanced (order : List Slot) (singles : List (Slot × List Tok))
    (mods : List (List Tok)) (ts : List Tok) (hs : BalancedAttrs singles)
    (hm : BalancedItems mods) (h : arrange order singles mods = some ts) : Balanced ts := by
  induction order generalizing singles mods ts with
  | nil =>
    cases singles <;> cases mods <;> cases h
    exact balanced_nil
  | cons slot order ih =>
    by_cases hslot : slot = .modInv
    · subst slot
      cases mods with
      | nil => cases h
      | cons word mods =>
        change (arrange order singles mods).map (word ++ ·) = some ts at h
        cases hr : arrange order singles mods with
        | none => rw [hr] at h; cases h
        | some suffix =>
          rw [hr] at h
          have heq : word ++ suffix = ts := Option.some.inj h
          apply heq ▸ balanced_append (hm word (List.mem_cons.mpr (Or.inl rfl)))
          exact ih singles mods suffix hs (balancedItems_tail hm) hr
    · rw [arrange_nonModifier slot hslot] at h
      cases hf : singles.find? (·.1 == slot) with
      | none => rw [hf] at h; cases h
      | some entry =>
        rw [hf] at h
        have he : Balanced entry.2 := hs entry (List.mem_of_find?_eq_some hf)
        have hs' : BalancedAttrs (singles.filter (·.1 != slot)) := by
          intro value hv
          exact hs value (List.mem_filter.mp hv).1
        cases hr : arrange order (singles.filter (·.1 != slot)) mods with
        | none => rw [hr] at h; cases h
        | some suffix =>
          rw [hr] at h
          have heq : entry.2 ++ suffix = ts := Option.some.inj h
          exact heq ▸ balanced_append he (ih _ mods suffix hs' hm hr)

theorem attrsP_balanced (singles : List (Slot × List Tok)) (mods : List (List Tok))
    (order : List Slot) (hs : BalancedAttrs singles) (hm : BalancedItems mods) :
    Produces (attrsP singles mods order) Balanced := by
  intro initial ts rest h
  change (arrange order singles mods).map (fun word => (word, initial)) = some (ts, rest) at h
  cases ha : arrange order singles mods with
  | none => rw [ha] at h; cases h
  | some word =>
    rw [ha] at h
    have heq : word = ts := (Prod.mk.inj (Option.some.inj h)).1
    exact heq ▸ arrange_balanced order singles mods word hs hm ha

end Solidity.Frontend.ExpressionUniqueness
