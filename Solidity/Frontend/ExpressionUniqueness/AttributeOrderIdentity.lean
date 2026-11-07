import Solidity.Frontend.ExpressionUniqueness.AttributeTokens

/-!
# Successful two-field attribute orders are exhaustive

Arbitrary layout lists are inverted, not bounded by an assumed length or
canonical order. These token-printer lemmas recover the complete actual run for
the original visibility/mutability fields.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem map_append_success (result : Option (List Tok)) (before word : List Tok)
    (h : result.map (before ++ ·) = some word) :
    ∃ suffix, result = some suffix ∧ word = before ++ suffix := by
  cases result with
  | none => cases h
  | some suffix => exact ⟨suffix, rfl, (Option.some.inj h).symm⟩

theorem arrange_empty_success (order : List Slot) (word : List Tok)
    (h : arrange order [] [] = some word) : order = [] ∧ word = [] := by
  cases order with
  | nil => exact ⟨rfl, (Option.some.inj h).symm⟩
  | cons slot rest => cases slot <;> cases h

theorem arrange_vis_success (order : List Slot) (payload word : List Tok)
    (h : arrange order [(.vis, payload)] [] = some word) : order = [.vis] ∧ word = payload := by
  cases order with
  | nil => cases h
  | cons slot rest =>
    cases slot with
    | vis =>
      change (arrange rest [] []).map (payload ++ ·) = some word at h
      obtain ⟨suffix, hs, shape⟩ := map_append_success _ payload word h
      obtain ⟨emptyOrder, emptyWord⟩ := arrange_empty_success rest suffix hs
      exact ⟨by rw [emptyOrder], by rw [shape, emptyWord, List.append_nil]⟩
    | mutab => cases h
    | modInv => cases h
    | virt => cases h
    | over => cases h
    | payable => cases h
    | ext => cases h
    | const => cases h
    | transient => cases h

theorem arrange_mutab_success (order : List Slot) (payload word : List Tok)
    (h : arrange order [(.mutab, payload)] [] = some word) : order = [.mutab] ∧ word = payload := by
  cases order with
  | nil => cases h
  | cons slot rest =>
    cases slot with
    | mutab =>
      change (arrange rest [] []).map (payload ++ ·) = some word at h
      obtain ⟨suffix, hs, shape⟩ := map_append_success _ payload word h
      obtain ⟨emptyOrder, emptyWord⟩ := arrange_empty_success rest suffix hs
      exact ⟨by rw [emptyOrder], by rw [shape, emptyWord, List.append_nil]⟩
    | vis => cases h
    | modInv => cases h
    | virt => cases h
    | over => cases h
    | payable => cases h
    | ext => cases h
    | const => cases h
    | transient => cases h

theorem arrange_vis_mutab_success (order : List Slot) (vis mu word : List Tok)
    (h : arrange order [(.vis, vis), (.mutab, mu)] [] = some word) :
    (order = [.vis, .mutab] ∧ word = vis ++ mu) ∨
      (order = [.mutab, .vis] ∧ word = mu ++ vis) := by
  cases order with
  | nil => cases h
  | cons slot rest =>
    cases slot with
    | vis =>
      change (arrange rest [(.mutab, mu)] []).map (vis ++ ·) = some word at h
      obtain ⟨suffix, hs, shape⟩ := map_append_success _ vis word h
      obtain ⟨orderTail, payload⟩ := arrange_mutab_success rest mu suffix hs
      exact Or.inl ⟨by rw [orderTail], by rw [shape, payload]⟩
    | mutab =>
      change (arrange rest [(.vis, vis)] []).map (mu ++ ·) = some word at h
      obtain ⟨suffix, hs, shape⟩ := map_append_success _ mu word h
      obtain ⟨orderTail, payload⟩ := arrange_vis_success rest vis suffix hs
      exact Or.inr ⟨by rw [orderTail], by rw [shape, payload]⟩
    | modInv => cases h
    | virt => cases h
    | over => cases h
    | payable => cases h
    | ext => cases h
    | const => cases h
    | transient => cases h

end Solidity.Frontend.ExpressionUniqueness
