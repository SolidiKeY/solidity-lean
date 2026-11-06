import Solidity.Frontend.ExpressionUniqueness.AttributeOrderIdentity

/-!
# Actual attribute words determine existing function-type fields

Arbitrary successful orders reduce to the exact field run. Disjoint token tags
recover optional visibility and mutability without selecting a canonical order
or equating layout witnesses.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def visibilityToken : Tok → Bool
  | .kw .internal | .kw .external | .kw .private_ | .kw .public_ => true | _ => false

def mutabilityToken : Tok → Bool
  | .kw .pure | .kw .view | .kw .payable => true | _ => false

theorem single_visibility (v : Visibility) : single .vis v.toks = [(.vis, v.toks)] := by
  cases v <;> rfl

theorem single_mutability (m : Mutability) : single .mutab m.toks = [(.mutab, m.toks)] := by
  cases m <;> rfl

theorem type_attributes_word_shape (vis : Option Visibility) (mu : Option Mutability)
    (order : List Slot) (word : List Tok)
    (h : arrange order (single .vis (optToks Visibility.toks vis) ++
      single .mutab (optToks Mutability.toks mu)) [] = some word) :
    word = optToks Visibility.toks vis ++ optToks Mutability.toks mu ∨
      word = optToks Mutability.toks mu ++ optToks Visibility.toks vis := by
  cases vis with
  | none =>
    cases mu with
    | none => exact Or.inl (arrange_empty_success order word h).2
    | some m =>
      change arrange order (single .mutab m.toks) [] = some word at h
      rw [single_mutability] at h
      exact Or.inl (arrange_mutab_success order m.toks word h).2
  | some v =>
    cases mu with
    | none =>
      change arrange order (single .vis v.toks ++ []) [] = some word at h
      rw [List.append_nil, single_visibility] at h
      exact Or.inr (arrange_vis_success order v.toks word h).2
    | some m =>
      change arrange order (single .vis v.toks ++ single .mutab m.toks) [] = some word at h
      rw [single_visibility, single_mutability] at h
      rcases arrange_vis_mutab_success order v.toks m.toks word h with forward | backward
      · exact Or.inl forward.2
      · exact Or.inr backward.2

theorem attrsP_arrange_success (singles : List (Slot × List Tok)) (mods : List (List Tok))
    (order : List Slot) (initial final : List Choice) (word : List Tok)
    (h : attrsP singles mods order initial = some (word, final)) : arrange order singles mods = some word := by
  change (arrange order singles mods).map (fun value => (value, initial)) = some (word, final) at h
  cases ha : arrange order singles mods with
  | none => rw [ha] at h; cases h
  | some value =>
    rw [ha] at h
    have equal : value = word := (Prod.mk.inj (Option.some.inj h)).1
    exact congrArg some equal

theorem visibility_optional_filter (value : Option Visibility) :
    (optToks Visibility.toks value).filter visibilityToken = optToks Visibility.toks value := by
  cases value with
  | none => rfl
  | some value => cases value <;> rfl

theorem visibility_optional_skip_mu (value : Option Visibility) :
    (optToks Visibility.toks value).filter mutabilityToken = [] := by
  cases value with
  | none => rfl
  | some value => cases value <;> rfl

theorem mutability_optional_filter (value : Option Mutability) :
    (optToks Mutability.toks value).filter mutabilityToken = optToks Mutability.toks value := by
  cases value with
  | none => rfl
  | some value => cases value <;> rfl

theorem mutability_optional_skip_vis (value : Option Mutability) :
    (optToks Mutability.toks value).filter visibilityToken = [] := by
  cases value with
  | none => rfl
  | some value => cases value <;> rfl

theorem type_attributes_filter_fields (vis : Option Visibility) (mu : Option Mutability) (word : List Tok)
    (shape : word = optToks Visibility.toks vis ++ optToks Mutability.toks mu ∨
      word = optToks Mutability.toks mu ++ optToks Visibility.toks vis) :
    word.filter visibilityToken = optToks Visibility.toks vis ∧
      word.filter mutabilityToken = optToks Mutability.toks mu := by
  rcases shape with shape | shape <;> constructor
    <;> simp only [shape, List.filter_append, visibility_optional_filter, mutability_optional_skip_vis,
      visibility_optional_skip_mu, mutability_optional_filter, List.append_nil, List.nil_append]

theorem optional_visibility_tokens_injective (a b : Option Visibility)
    (words : optToks Visibility.toks a = optToks Visibility.toks b) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => cases b <;> cases words
  | some a =>
    cases b with
    | none => cases a <;> cases words
    | some b => cases a <;> cases b <;> cases words <;> rfl

theorem optional_mutability_tokens_injective (a b : Option Mutability)
    (words : optToks Mutability.toks a = optToks Mutability.toks b) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => cases b <;> cases words
  | some a =>
    cases b with
    | none => cases a <;> cases words
    | some b => cases a <;> cases b <;> cases words <;> rfl

theorem type_attributes_fields_unique (vis vis' : Option Visibility) (mu mu' : Option Mutability)
    (order order' : List Slot) (initial final initial' final' : List Choice) (word word' : List Tok)
    (h : attrsP (single .vis (optToks Visibility.toks vis) ++ single .mutab (optToks Mutability.toks mu))
      [] order initial = some (word, final))
    (h' : attrsP (single .vis (optToks Visibility.toks vis') ++ single .mutab (optToks Mutability.toks mu'))
      [] order' initial' = some (word', final')) (words : word = word') : vis = vis' ∧ mu = mu' := by
  have fields := type_attributes_filter_fields vis mu word
    (type_attributes_word_shape vis mu order word (attrsP_arrange_success _ _ _ _ _ _ h))
  have fields' := type_attributes_filter_fields vis' mu' word'
    (type_attributes_word_shape vis' mu' order' word' (attrsP_arrange_success _ _ _ _ _ _ h'))
  exact ⟨optional_visibility_tokens_injective vis vis' (fields.1.symm.trans
      ((congrArg (List.filter visibilityToken) words).trans fields'.1)),
    optional_mutability_tokens_injective mu mu' (fields.2.symm.trans
      ((congrArg (List.filter mutabilityToken) words).trans fields'.2))⟩

end Solidity.Frontend.ExpressionUniqueness
