import Solidity.Frontend.ExpressionUniqueness.TypePrefixAlgebra

/-!
# Actual function-type attribute tokens belong to their keyword run

The original arbitrary layout order is retained. Successful arrange execution
preserves token membership in a concrete alphabet, derived from the existing
visibility/mutability fields, without assuming a canonical layout or root cut.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def TokenItems (p : Tok → Bool) (items : List (List Tok)) : Prop :=
  ∀ word, word ∈ items → AllTokens p word

def TokenAttrs (p : Tok → Bool) (entries : List (Slot × List Tok)) : Prop :=
  ∀ entry, entry ∈ entries → AllTokens p entry.2

theorem allTokens_nil (p : Tok → Bool) : AllTokens p [] := by
  intro t ht
  cases ht

theorem allTokens_append (p : Tok → Bool) (xs ys : List Tok) (hx : AllTokens p xs) (hy : AllTokens p ys) :
    AllTokens p (xs ++ ys) := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hx t ht
  · exact hy t ht

theorem tokenItems_nil (p : Tok → Bool) : TokenItems p [] := by intro word hw; cases hw

theorem tokenAttrs_append (p : Tok → Bool) (xs ys : List (Slot × List Tok))
    (hx : TokenAttrs p xs) (hy : TokenAttrs p ys) : TokenAttrs p (xs ++ ys) := by
  intro entry ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hx entry ht
  · exact hy entry ht

theorem tokenAttrs_single (p : Tok → Bool) (slot : Slot) (word : List Tok) (h : AllTokens p word) :
    TokenAttrs p (single slot word) := by
  unfold single
  split
  · intro entry ht; cases ht
  · intro entry ht
    have equal : entry = (slot, word) := List.mem_singleton.mp ht
    exact equal ▸ h

theorem arrange_allTokens (p : Tok → Bool) (order : List Slot)
    (singles : List (Slot × List Tok)) (mods : List (List Tok)) (word : List Tok)
    (hs : TokenAttrs p singles) (hm : TokenItems p mods) (h : arrange order singles mods = some word) :
    AllTokens p word := by
  induction order generalizing singles mods word with
  | nil =>
    cases singles <;> cases mods <;> cases h
    exact allTokens_nil p
  | cons slot order ih =>
    by_cases hslot : slot = .modInv
    · subst slot
      cases mods with
      | nil => cases h
      | cons first rest =>
        change (arrange order singles rest).map (first ++ ·) = some word at h
        cases hr : arrange order singles rest with
        | none => rw [hr] at h; cases h
        | some suffix =>
          rw [hr] at h
          have equal : first ++ suffix = word := Option.some.inj h
          apply equal ▸ allTokens_append p first suffix (hm first (List.mem_cons.mpr (Or.inl rfl)))
          exact ih singles rest suffix hs
            (fun value hv => hm value (List.mem_cons.mpr (Or.inr hv))) hr
    · rw [arrange_nonModifier slot hslot] at h
      cases hf : singles.find? (·.1 == slot) with
      | none => rw [hf] at h; cases h
      | some entry =>
        rw [hf] at h
        have he : AllTokens p entry.2 := hs entry (List.mem_of_find?_eq_some hf)
        have hs' : TokenAttrs p (singles.filter (·.1 != slot)) := by
          intro value hv
          exact hs value (List.mem_filter.mp hv).1
        cases hr : arrange order (singles.filter (·.1 != slot)) mods with
        | none => rw [hr] at h; cases h
        | some suffix =>
          rw [hr] at h
          have equal : entry.2 ++ suffix = word := Option.some.inj h
          exact equal ▸ allTokens_append p entry.2 suffix he (ih _ mods suffix hs' hm hr)

theorem attrsP_allTokens (p : Tok → Bool) (singles : List (Slot × List Tok))
    (mods : List (List Tok)) (order : List Slot) (hs : TokenAttrs p singles) (hm : TokenItems p mods) :
    Produces (attrsP singles mods order) (AllTokens p) := by
  intro initial word final h
  change (arrange order singles mods).map (fun value => (value, initial)) = some (word, final) at h
  cases ha : arrange order singles mods with
  | none => rw [ha] at h; cases h
  | some value =>
    rw [ha] at h
    have equal : value = word := (Prod.mk.inj (Option.some.inj h)).1
    exact equal ▸ arrange_allTokens p order singles mods value hs hm ha

theorem allTokens_visibility (v : Visibility) : AllTokens typeAttributeToken v.toks := by
  cases v <;> intro t ht <;> cases (List.mem_singleton.mp ht) <;> rfl

theorem allTokens_mutability (m : Mutability) : AllTokens typeAttributeToken m.toks := by
  cases m <;> intro t ht <;> cases (List.mem_singleton.mp ht) <;> rfl

theorem allTokens_optToks {α : Type} (p : Tok → Bool) (f : α → List Tok)
    (h : ∀ a, AllTokens p (f a)) (value : Option α) : AllTokens p (optToks f value) := by
  cases value with
  | none => exact allTokens_nil p
  | some a => exact h a

theorem attrsP_typeAttributes (vis : Option Visibility) (mu : Option Mutability) (order : List Slot) :
    Produces (attrsP (single .vis (optToks Visibility.toks vis) ++
      single .mutab (optToks Mutability.toks mu)) [] order) (AllTokens typeAttributeToken) := by
  apply attrsP_allTokens
  · exact tokenAttrs_append _ _ _
      (tokenAttrs_single _ _ _ (allTokens_optToks _ _ allTokens_visibility vis))
      (tokenAttrs_single _ _ _ (allTokens_optToks _ _ allTokens_mutability mu))
  · exact tokenItems_nil _

end Solidity.Frontend.ExpressionUniqueness
