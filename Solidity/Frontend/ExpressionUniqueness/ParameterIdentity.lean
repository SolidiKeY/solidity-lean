import Solidity.Frontend.ExpressionUniqueness.RecursiveProperty
import Solidity.Frontend.ExpressionUniqueness.TypePrefix

/-!
# Actual parameter fields and recursive identity step

The concrete parameter suffix supplies the type-prefix follower boundary
internally. Optional storage locations and names reconstruct from disjoint token
tags. The only recursive identity premise is the existing type child induction
predicate, not an additional producer/global theorem assumption.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem option_location_cases (loc : Option DataLoc) :
    loc = none ∨ loc = some .memory ∨ loc = some .storage ∨ loc = some .calldata := by
  cases loc with
  | none => exact Or.inl rfl
  | some loc =>
    cases loc with
    | memory => exact Or.inr (Or.inl rfl)
    | storage => exact Or.inr (Or.inr (Or.inl rfl))
    | calldata => exact Or.inr (Or.inr (Or.inr rfl))

theorem parameter_tail_boundary (loc : Option DataLoc) (name : Option String) :
    TypeBoundary (optToks DataLoc.toks loc ++ optToks idt name) := by
  rcases option_location_cases loc with rfl | rfl | rfl | rfl
    <;> cases name <;> constructor
    <;> first | exact tokenBoundary_nil _ | exact tokenBoundary_cons _ _ _ rfl

theorem parameter_tail_unique (loc loc' : Option DataLoc) (name name' : Option String)
    (words : optToks DataLoc.toks loc ++ optToks idt name =
      optToks DataLoc.toks loc' ++ optToks idt name') : loc = loc' ∧ name = name' := by
  rcases option_location_cases loc with rfl | rfl | rfl | rfl
    <;> rcases option_location_cases loc' with rfl | rfl | rfl | rfl
    <;> cases name <;> cases name'
    <;> simp only [optToks, DataLoc.toks, tk, idt, List.nil_append, List.cons_append] at words
    <;> cases words <;> exact ⟨rfl, rfl⟩

theorem parameter_yield_parts (ty : Syn .typeName) (loc : Option DataLoc) (name : Option String)
    (initial final : List Choice) (items : List (List Tok))
    (hy : (Syn.param ty loc name).yield initial = some (items, final)) :
    ∃ xs, ty.yield initial = some (xs, final) ∧
      items = [xs.flatten ++ optToks DataLoc.toks loc ++ optToks idt name] :=
  one_pure_success_split ty.yield
    (fun xs => [xs.flatten ++ optToks DataLoc.toks loc ++ optToks idt name]) initial final items hy

theorem parameter_prec_child (ty : Syn .typeName) (loc : Option DataLoc) (name : Option String)
    (hp : (Syn.param ty loc name).prec = true) : ty.prec = true := by
  have hall : (Syn.param ty loc name).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.param ty loc name).precNode && ty.all Syn.precNode) = true at hall
  exact all_prec_implies_prec ty (Bool.and_eq_true_iff.mp hall).2

theorem parameter_word_unique (ty : Syn .typeName) (loc : Option DataLoc) (name : Option String)
    (ih : WordUnique ty) : WordUnique (Syn.param ty loc name) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  cases other with
  | param ty' loc' name' =>
    obtain ⟨xs, hx, shape⟩ := parameter_yield_parts ty loc name initial final items hy
    obtain ⟨ys, hyb, shape'⟩ := parameter_yield_parts ty' loc' name' initial' final' items' hy'
    rw [shape, shape'] at words
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] at words
    obtain ⟨types, tails⟩ := type_yield_prefix_unique ty ty' initial final initial' final' xs ys
      (optToks DataLoc.toks loc ++ optToks idt name) (optToks DataLoc.toks loc' ++ optToks idt name')
      (parameter_tail_boundary loc name) (parameter_tail_boundary loc' name') hx hyb words
    obtain ⟨locations, names⟩ := parameter_tail_unique loc loc' name name' tails
    have child : ty = ty' := ih ty' initial final initial' final' xs ys
      (parameter_prec_child ty loc name hp) (parameter_prec_child ty' loc' name' hp') hx hyb types
    rw [child, locations, names]

end Solidity.Frontend.ExpressionUniqueness
