import Solidity.Frontend.ExpressionUniqueness.PrimaryYieldSplit
import Solidity.Frontend.ExpressionUniqueness.LiteralPrefix

/-!
# Primary word-prefix cuts from actual intrinsic executions

Keyword and enclosure boundaries come from successful existing printers. New
uses the type boundary derived from its guarded postfix follower. No desired
primary span or tree uniqueness is a premise.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem ident_yield_prefix_unique (a b : String)
    (initial final initial' final' : List Choice) (items items' : List (List Tok)) (tail tail' : List Tok)
    (hy : (Syn.ident a).yield initial = some (items, final))
    (hy' : (Syn.ident b).yield initial' = some (items', final'))
    (words : items.flatten ++ tail = items'.flatten ++ tail') :
    items.flatten = items'.flatten ∧ tail = tail' := by
  have shape : items = [idt a] := (pure_success_split [idt a] items initial final hy).1
  have shape' : items' = [idt b] := (pure_success_split [idt b] items' initial' final' hy').1
  rw [shape, shape'] at words ⊢
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, idt, List.singleton_append] at words ⊢
  obtain ⟨token, following⟩ := List.cons.inj words
  exact ⟨congrArg (fun t => [t]) token, following⟩

theorem elem_expr_yield_prefix_unique (a b : Elem) (allowed : a ≠ .addressPayable) (allowed' : b ≠ .addressPayable)
    (initial final initial' final' : List Choice) (items items' : List (List Tok)) (tail tail' : List Tok)
    (hy : (Syn.elemType a allowed).yield initial = some (items, final))
    (hy' : (Syn.elemType b allowed').yield initial' = some (items', final'))
    (words : items.flatten ++ tail = items'.flatten ++ tail') :
    items.flatten = items'.flatten ∧ tail = tail' := by
  have shape : items = [[.elem a]] := (pure_success_split [[Tok.elem a]] items initial final hy).1
  have shape' : items' = [[.elem b]] := (pure_success_split [[Tok.elem b]] items' initial' final' hy').1
  rw [shape, shape'] at words ⊢
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.singleton_append] at words ⊢
  obtain ⟨token, following⟩ := List.cons.inj words
  exact ⟨congrArg (fun t => [t]) token, following⟩

theorem new_yield_prefix_unique (a b : Syn .typeName)
    (initial final initial' final' : List Choice) (items items' : List (List Tok)) (tail tail' : List Tok)
    (hb : PostfixFollower true tail) (hb' : PostfixFollower true tail')
    (hy : (Syn.new a).yield initial = some (items, final))
    (hy' : (Syn.new b).yield initial' = some (items', final'))
    (words : items.flatten ++ tail = items'.flatten ++ tail') :
    items.flatten = items'.flatten ∧ tail = tail' := by
  obtain ⟨xs, hx, shape⟩ := new_yield_parts a initial final items hy
  obtain ⟨ys, hyb, shape'⟩ := new_yield_parts b initial' final' items' hy'
  rw [shape, shape'] at words ⊢
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at words ⊢
  have expanded := words
  simp only [tk, List.cons_append, List.nil_append] at expanded
  obtain ⟨types, following⟩ := type_yield_prefix_unique a b initial final initial' final' xs ys tail tail'
    (new_postfixFollower_typeBoundary tail hb) (new_postfixFollower_typeBoundary tail' hb')
    hx hyb (List.cons.inj expanded).2
  exact ⟨by rw [types], following⟩

theorem payable_yield_prefix_unique (a b : Syn .callArgs)
    (initial final initial' final' : List Choice) (items items' : List (List Tok)) (tail tail' : List Tok)
    (hy : (Syn.payableConv a).yield initial = some (items, final))
    (hy' : (Syn.payableConv b).yield initial' = some (items', final'))
    (words : items.flatten ++ tail = items'.flatten ++ tail') :
    items.flatten = items'.flatten ∧ tail = tail' := by
  obtain ⟨payload, bal, shape⟩ := payable_actual_parens a initial final items hy
  obtain ⟨payload', bal', shape'⟩ := payable_actual_parens b initial' final' items' hy'
  rw [shape, shape'] at words ⊢
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at words ⊢
  have expanded := words
  simp only [tk, List.cons_append, List.nil_append] at expanded
  obtain ⟨body, following⟩ := parens_prefix_unique payload payload' tail tail' bal bal' (List.cons.inj expanded).2
  exact ⟨by rw [body], following⟩

theorem meta_yield_prefix_unique (a b : Syn .typeName)
    (initial final initial' final' : List Choice) (items items' : List (List Tok)) (tail tail' : List Tok)
    (hy : (Syn.metaType a).yield initial = some (items, final))
    (hy' : (Syn.metaType b).yield initial' = some (items', final'))
    (words : items.flatten ++ tail = items'.flatten ++ tail') :
    items.flatten = items'.flatten ∧ tail = tail' := by
  obtain ⟨payload, bal, shape⟩ := meta_actual_parens a initial final items hy
  obtain ⟨payload', bal', shape'⟩ := meta_actual_parens b initial' final' items' hy'
  rw [shape, shape'] at words ⊢
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at words ⊢
  have expanded := words
  simp only [tk, List.cons_append, List.nil_append] at expanded
  obtain ⟨body, following⟩ := parens_prefix_unique payload payload' tail tail' bal bal' (List.cons.inj expanded).2
  exact ⟨by rw [body], following⟩

theorem tuple_yield_prefix_unique (first first' : Syn (.opt .expr))
    (rest rest' : Syn (.list (.opt .expr))) (initial final initial' final' : List Choice)
    (items items' : List (List Tok)) (tail tail' : List Tok)
    (hy : (Syn.tuple first rest).yield initial = some (items, final))
    (hy' : (Syn.tuple first' rest').yield initial' = some (items', final'))
    (words : items.flatten ++ tail = items'.flatten ++ tail') :
    items.flatten = items'.flatten ∧ tail = tail' := by
  obtain ⟨payload, bal, shape⟩ := tuple_actual_parens first rest initial final items hy
  obtain ⟨payload', bal', shape'⟩ := tuple_actual_parens first' rest' initial' final' items' hy'
  rw [shape, shape'] at words ⊢
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at words ⊢
  obtain ⟨body, following⟩ := parens_prefix_unique payload payload' tail tail' bal bal' words
  exact ⟨by rw [body], following⟩

theorem inline_yield_prefix_unique (first first' : Syn .expr) (rest rest' : Syn (.list .expr))
    (initial final initial' final' : List Choice) (items items' : List (List Tok)) (tail tail' : List Tok)
    (hy : (Syn.inlineArray first rest).yield initial = some (items, final))
    (hy' : (Syn.inlineArray first' rest').yield initial' = some (items', final'))
    (words : items.flatten ++ tail = items'.flatten ++ tail') :
    items.flatten = items'.flatten ∧ tail = tail' := by
  obtain ⟨payload, bal, shape⟩ := inline_actual_square first rest initial final items hy
  obtain ⟨payload', bal', shape'⟩ := inline_actual_square first' rest' initial' final' items' hy'
  rw [shape, shape'] at words ⊢
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at words ⊢
  have enclosed : openTok .square :: (payload ++ closeTok .square :: tail) =
      openTok .square :: (payload' ++ closeTok .square :: tail') := by
    simpa only [pu, openTok, closeTok, List.append_assoc, List.singleton_append] using words
  obtain ⟨body, following⟩ := enclosed_payload_unique .square payload payload' tail tail' bal bal' enclosed
  exact ⟨by rw [body], following⟩

end Solidity.Frontend.ExpressionUniqueness
