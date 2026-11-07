import Solidity.Frontend.ExpressionUniqueness.MappingKeyIdentity

/-!
# Actual intrinsic mapping identity induction step

The actual key-name/arrow and value-name fields derive their own maximal-prefix
boundaries. Only the original value-type structural induction fact is recursive.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem mapping_type_prec_child (key : MapKey) (kn : Option String) (value : Syn .typeName) (vn : Option String)
    (hp : (Syn.mapping key kn value vn).prec = true) : value.prec = true := by
  have hall : (Syn.mapping key kn value vn).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.mapping key kn value vn).precNode && value.all Syn.precNode) = true at hall
  exact all_prec_implies_prec value (Bool.and_eq_true_iff.mp hall).2

theorem mapping_type_same_constructor_unique (key key' : MapKey) (kn kn' : Option String)
    (value value' : Syn .typeName) (vn vn' : Option String) (ih : WordUnique value)
    (initial final initial' final' : List Choice) (items items' : List (List Tok))
    (hp : (Syn.mapping key kn value vn).prec = true) (hp' : (Syn.mapping key' kn' value' vn').prec = true)
    (hy : (Syn.mapping key kn value vn).yield initial = some (items, final))
    (hy' : (Syn.mapping key' kn' value' vn').yield initial' = some (items', final'))
    (words : items.flatten = items'.flatten) : Syn.mapping key kn value vn = Syn.mapping key' kn' value' vn' := by
  obtain ⟨xs, hx, shape⟩ := mapping_type_yield_parts key kn value vn initial final items hy
  obtain ⟨ys, hyb, shape'⟩ := mapping_type_yield_parts key' kn' value' vn' initial' final' items' hy'
  have shapeWord : items.flatten = tk .mapping ++ parens
      (mapKeyWord key ++ optToks idt kn ++ pu .doubleArrow ++ xs.flatten ++ optToks idt vn) := by
    rw [shape]
    cases key <;> simp only [mapKeyWord, List.flatten_cons, List.flatten_nil, List.append_nil]
  have shapeWord' : items'.flatten = tk .mapping ++ parens
      (mapKeyWord key' ++ optToks idt kn' ++ pu .doubleArrow ++ ys.flatten ++ optToks idt vn') := by
    rw [shape']
    cases key' <;> simp only [mapKeyWord, List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [shapeWord, shapeWord'] at words
  have bodies := parens_word_injective _ _ (List.cons.inj words).2
  simp only [List.append_assoc] at bodies
  obtain ⟨keys, afterKeys⟩ := mapKey_word_prefix_unique key key'
    (optToks idt kn ++ pu .doubleArrow ++ (xs.flatten ++ optToks idt vn))
    (optToks idt kn' ++ pu .doubleArrow ++ (ys.flatten ++ optToks idt vn'))
    (mapping_key_tail_boundary kn _) (mapping_key_tail_boundary kn' _)
      (by simpa only [List.append_assoc] using bodies)
  obtain ⟨keyNames, values⟩ := mapping_name_arrow_unique kn kn'
    (xs.flatten ++ optToks idt vn) (ys.flatten ++ optToks idt vn') afterKeys
  have vb : TypeBoundary (optToks idt vn) := parameter_tail_boundary none vn
  have vb' : TypeBoundary (optToks idt vn') := parameter_tail_boundary none vn'
  obtain ⟨types, names⟩ := type_yield_prefix_unique value value' initial final initial' final' xs ys
    (optToks idt vn) (optToks idt vn') vb vb' hx hyb values
  have valueNames : vn = vn' := (parameter_tail_unique none none vn vn' names).2
  have typesEq : value = value' := ih value' initial final initial' final' xs ys
    (mapping_type_prec_child key kn value vn hp) (mapping_type_prec_child key' kn' value' vn' hp') hx hyb types
  rw [keys, keyNames, typesEq, valueNames]

theorem mapping_type_word_unique (key : MapKey) (kn : Option String) (value : Syn .typeName) (vn : Option String)
    (ih : WordUnique value) : WordUnique (Syn.mapping key kn value vn) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have atom := same_yield_type_atom (.mapping key kn value vn) other initial final initial' final' items items' rfl hy hy' words
  have kind := same_yield_type_atom_kind (.mapping key kn value vn) other initial final initial' final' items items' rfl hy hy' words
  rcases typeAtom_cases other atom with ⟨e, rfl⟩ | ⟨path, rfl⟩ | ⟨key', kn', value', vn', rfl⟩ |
    ⟨params, vis, mu, returns, rfl⟩
  · cases kind
  · cases kind
  · exact mapping_type_same_constructor_unique key key' kn kn' value value' vn vn' ih
      initial final initial' final' items items' hp hp' hy hy' words
  · cases kind

end Solidity.Frontend.ExpressionUniqueness
