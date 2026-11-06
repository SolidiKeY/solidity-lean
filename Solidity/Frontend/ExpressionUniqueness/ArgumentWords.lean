import Solidity.Frontend.ExpressionUniqueness.ExpressionStart
import Solidity.Frontend.ExpressionUniqueness.ExpressionCommaFree

/-!
# Actual argument vectors preserve nonempty words and comma boundaries

Empty vectors are permitted; empty expression/named-argument component words are
not. This removes the existing generic commaSep [] versus [[]] collision without
an added producer premise: nonemptiness follows from actual child executions.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def NonemptyWords (items : List (List Tok)) : Prop := ∀ ts, ts ∈ items → ts ≠ []

theorem startFree_commaSep (items : List (List Tok)) (h : StartFreeItems items) : StartFree (commaSep items) := by
  induction items with
  | nil => exact startFree_nil
  | cons x xs ih =>
    cases xs with
    | nil => simpa only [commaSep_single] using h x (List.mem_cons.mpr (Or.inl rfl))
    | cons y ys =>
      rw [commaSep_cons_cons]
      have word : StartFree (x ++ [.punct .comma] ++ commaSep (y :: ys)) :=
        startFree_append (startFree_append (h x (List.mem_cons.mpr (Or.inl rfl)))
          (startFree_atom (t := .punct .comma) rfl rfl))
          (ih (fun ts ht => h ts (List.mem_cons.mpr (Or.inr ht))))
      simpa only [List.append_assoc, List.singleton_append] using word

theorem commaSep_nonempty_word_head (word : List Tok) (rest : List (List Tok)) (h : word ≠ []) :
    commaSep (word :: rest) ≠ [] := by
  cases rest with
  | nil => simpa only [commaSep_single] using h
  | cons next tail =>
    rw [commaSep_cons_cons]
    intro empty
    have lengths := congrArg List.length empty
    simp only [List.length_append, List.length_cons, List.length_nil] at lengths
    omega

theorem commaSep_unique_nonempty_words (xs ys : List (List Tok))
    (hx : CommaFreeItems xs) (hy : CommaFreeItems ys)
    (nx : NonemptyWords xs) (ny : NonemptyWords ys) (he : commaSep xs = commaSep ys) : xs = ys := by
  cases xs with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      exact False.elim (commaSep_nonempty_word_head y ys (ny y (List.mem_cons.mpr (Or.inl rfl))) he.symm)
  | cons x xs =>
    cases ys with
    | nil => exact False.elim (commaSep_nonempty_word_head x xs (nx x (List.mem_cons.mpr (Or.inl rfl))) he)
    | cons y ys => exact commaSep_nonempty_unique x y xs ys hx hy he

theorem namedArg_yield_nonemptyWord (arg : Syn .namedArg) (initial final : List Choice)
    (items : List (List Tok)) (h : arg.yield initial = some (items, final)) : items.flatten ≠ [] := by
  cases arg with
  | namedArg name value =>
    obtain ⟨xs, hx, shape⟩ := namedArg_yield_parts name value initial final items h
    rw [shape]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, idt, pu,
      List.cons_append, List.nil_append]
    intro empty
    cases empty

def ArgumentVectorProperty {c : Cat} (e : Syn c) : Prop :=
  match c with
  | .list .expr | .list .namedArg => Produces e.yield NonemptyWords
  | _ => True

theorem argument_vector_property {c : Cat} (e : Syn c) : ArgumentVectorProperty e := by
  induction e with
  | @nil c =>
    cases c <;> first
      | trivial
      | exact produces_pure _ _ (by intro word member; cases member)
  | @cons c head tail ihHead ihTail =>
    cases c with
    | expr =>
      apply produces_bind head.yield _ (fun items => items.flatten ≠ []) NonemptyWords
        (fun initial items final hy => nonemptyItem_flatten (expr_yield_nonempty head initial items final hy))
      intro first hf
      apply produces_bind tail.yield _ NonemptyWords NonemptyWords ihTail
      intro rest hr
      apply produces_pure
      intro word member
      rcases List.mem_cons.mp member with equal | inside
      · exact equal ▸ hf
      · exact hr word inside
    | namedArg =>
      apply produces_bind head.yield _ (fun items => items.flatten ≠ []) NonemptyWords
        (fun initial items final hy => namedArg_yield_nonemptyWord head initial final items hy)
      intro first hf
      apply produces_bind tail.yield _ NonemptyWords NonemptyWords ihTail
      intro rest hr
      apply produces_pure
      intro word member
      rcases List.mem_cons.mp member with equal | inside
      · exact equal ▸ hf
      · exact hr word inside
    | _ => trivial
  | _ => trivial

theorem expressionList_yield_nonemptyWords (es : Syn (.list .expr)) : Produces es.yield NonemptyWords :=
  argument_vector_property es

theorem namedArgList_yield_nonemptyWords (args : Syn (.list .namedArg)) : Produces args.yield NonemptyWords :=
  argument_vector_property args

end Solidity.Frontend.ExpressionUniqueness
