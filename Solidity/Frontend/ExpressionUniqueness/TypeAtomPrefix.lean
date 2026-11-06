import Solidity.Frontend.ExpressionUniqueness.TypeAtomStart
import Solidity.Frontend.ExpressionUniqueness.FnTypePrefix

/-!
# Existing non-array type words reconstruct their maximal prefix

Every root and payload property is derived from actual type executions. The
concrete follower boundary is a token condition, not a producer premise; the
certified primary theorem must establish it from the original surrounding syntax.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem elem_type_yield_prefix_unique (e f : Elem)
    (initial final initial' final' : List Choice) (items items' : List (List Tok)) (tail tail' : List Tok)
    (hb : TypeAtomBoundary tail) (hb' : TypeAtomBoundary tail')
    (hy : (Syn.elem e).yield initial = some (items, final))
    (hy' : (Syn.elem f).yield initial' = some (items', final'))
    (words : items.flatten ++ tail = items'.flatten ++ tail') :
    items.flatten = items'.flatten ∧ tail = tail' := by
  have shape : items = [e.toks] := (pure_success_split [e.toks] items initial final hy).1
  have shape' : items' = [f.toks] := (pure_success_split [f.toks] items' initial' final' hy').1
  rw [shape, shape'] at words ⊢
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at words ⊢
  exact elementary_type_prefix_unique e f tail tail' hb hb' words

theorem user_type_yield_prefix_unique (p q : IdPath)
    (initial final initial' final' : List Choice) (items items' : List (List Tok)) (tail tail' : List Tok)
    (hb : TypeAtomBoundary tail) (hb' : TypeAtomBoundary tail')
    (hy : (Syn.userType p).yield initial = some (items, final))
    (hy' : (Syn.userType q).yield initial' = some (items', final'))
    (words : items.flatten ++ tail = items'.flatten ++ tail') :
    items.flatten = items'.flatten ∧ tail = tail' := by
  have shape : items = [p.toks] := (pure_success_split [p.toks] items initial final hy).1
  have shape' : items' = [q.toks] := (pure_success_split [q.toks] items' initial' final' hy').1
  rw [shape, shape'] at words ⊢
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at words ⊢
  exact path_type_prefix_unique p q tail tail' hb hb' words

theorem mapping_type_actual_parens (key : MapKey) (kn : Option String)
    (value : Syn .typeName) (vn : Option String) (initial final : List Choice)
    (items : List (List Tok)) (hy : (Syn.mapping key kn value vn).yield initial = some (items, final)) :
    ∃ payload, Balanced payload ∧ items = [tk .mapping ++ parens payload] := by
  cases key with
  | elem e allowed =>
    obtain ⟨xs, hx, shape⟩ := mapping_type_yield_parts (.elem e allowed) kn value vn initial final items hy
    exact ⟨_, balanced_append (balanced_append (balanced_append (balanced_append
      (balanced_elem e) (balanced_optToks idt balanced_idt kn)) (balanced_atom rfl))
      (balancedItems_flatten (expressionCategory_yield_balanced value rfl initial xs final hx)))
      (balanced_optToks idt balanced_idt vn), shape⟩
  | path p =>
    obtain ⟨xs, hx, shape⟩ := mapping_type_yield_parts (.path p) kn value vn initial final items hy
    exact ⟨_, balanced_append (balanced_append (balanced_append (balanced_append
      (balanced_path p) (balanced_optToks idt balanced_idt kn)) (balanced_atom rfl))
      (balancedItems_flatten (expressionCategory_yield_balanced value rfl initial xs final hx)))
      (balanced_optToks idt balanced_idt vn), shape⟩

theorem mapping_type_yield_prefix_unique (key key' : MapKey) (kn kn' : Option String)
    (value value' : Syn .typeName) (vn vn' : Option String)
    (initial final initial' final' : List Choice) (items items' : List (List Tok)) (tail tail' : List Tok)
    (hy : (Syn.mapping key kn value vn).yield initial = some (items, final))
    (hy' : (Syn.mapping key' kn' value' vn').yield initial' = some (items', final'))
    (words : items.flatten ++ tail = items'.flatten ++ tail') :
    items.flatten = items'.flatten ∧ tail = tail' := by
  obtain ⟨payload, bal, shape⟩ := mapping_type_actual_parens key kn value vn initial final items hy
  obtain ⟨payload', bal', shape'⟩ := mapping_type_actual_parens key' kn' value' vn' initial' final' items' hy'
  rw [shape, shape'] at words ⊢
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at words ⊢
  have expanded := words
  simp only [tk, List.cons_append, List.nil_append] at expanded
  obtain ⟨body, following⟩ := parens_prefix_unique payload payload' tail tail' bal bal' (List.cons.inj expanded).2
  exact ⟨by rw [body], following⟩

theorem fn_type_yield_prefix_unique (params params' : Syn (.list .param))
    (vis vis' : Option Visibility) (mu mu' : Option Mutability) (returns returns' : Syn (.list .param))
    (initial final initial' final' : List Choice) (items items' : List (List Tok)) (tail tail' : List Tok)
    (hb : TypeAtomBoundary tail) (hb' : TypeAtomBoundary tail')
    (hy : (Syn.fnType params vis mu returns).yield initial = some (items, final))
    (hy' : (Syn.fnType params' vis' mu' returns').yield initial' = some (items', final'))
    (words : items.flatten ++ tail = items'.flatten ++ tail') :
    items.flatten = items'.flatten ∧ tail = tail' := by
  obtain ⟨ps, attrs, rs, hp, ha, hr, shape⟩ := fn_type_actual_attribute_run params vis mu returns initial final items hy
  obtain ⟨ps', attrs', rs', hp', ha', hr', shape'⟩ :=
    fn_type_actual_attribute_run params' vis' mu' returns' initial' final' items' hy'
  rw [shape, shape'] at words ⊢
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at words ⊢
  exact fn_type_word_prefix_unique (commaSep ps) (commaSep ps') attrs attrs' rs rs' tail tail'
    hp hp' ha ha' hr hr' hb hb' words

theorem typeAtom_cases (e : Syn .typeName) (ha : isTypeAtom e = true) :
    (∃ value, e = Syn.elem value) ∨ (∃ path, e = Syn.userType path) ∨
    (∃ key kn value vn, e = Syn.mapping key kn value vn) ∨
    (∃ params vis mu returns, e = Syn.fnType params vis mu returns) := by
  cases e with
  | elem value => exact Or.inl ⟨value, rfl⟩
  | userType path => exact Or.inr (Or.inl ⟨path, rfl⟩)
  | mapping key kn value vn => exact Or.inr (Or.inr (Or.inl ⟨key, kn, value, vn, rfl⟩))
  | fnType params vis mu returns => exact Or.inr (Or.inr (Or.inr ⟨params, vis, mu, returns, rfl⟩))
  | array => cases ha

theorem type_atom_yield_prefix_unique (a b : Syn .typeName)
    (initial final initial' final' : List Choice) (items items' : List (List Tok)) (tail tail' : List Tok)
    (atomA : isTypeAtom a = true) (atomB : isTypeAtom b = true)
    (hb : TypeAtomBoundary tail) (hb' : TypeAtomBoundary tail')
    (hy : a.yield initial = some (items, final)) (hy' : b.yield initial' = some (items', final'))
    (words : items.flatten ++ tail = items'.flatten ++ tail') :
    items.flatten = items'.flatten ∧ tail = tail' := by
  have kinds := typeAtom_prefix_kinds_equal a b initial final initial' final' items items' tail tail' atomA atomB hy hy' words
  rcases typeAtom_cases a atomA with ⟨e, rfl⟩ | ⟨p, rfl⟩ | ⟨key, kn, value, vn, rfl⟩ |
    ⟨params, vis, mu, returns, rfl⟩ <;>
    rcases typeAtom_cases b atomB with ⟨e', rfl⟩ | ⟨p', rfl⟩ | ⟨key', kn', value', vn', rfl⟩ |
      ⟨params', vis', mu', returns', rfl⟩
  all_goals first | (cases kinds; done) | skip
  all_goals first
    | exact elem_type_yield_prefix_unique (hb := hb) (hb' := hb') (hy := hy) (hy' := hy') (words := words)
    | exact user_type_yield_prefix_unique (hb := hb) (hb' := hb') (hy := hy) (hy' := hy') (words := words)
    | exact mapping_type_yield_prefix_unique (hy := hy) (hy' := hy') (words := words)
    | exact fn_type_yield_prefix_unique (hb := hb) (hb' := hb') (hy := hy) (hy' := hy') (words := words)

end Solidity.Frontend.ExpressionUniqueness
