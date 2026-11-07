import Solidity.Frontend.ExpressionUniqueness.RecursiveProperty
import Solidity.Frontend.ExpressionUniqueness.PrimaryPrefix

/-!
# Primary expression leaf identity against every certified competitor

Actual certified root levels and token heads derive the family internally.
Literal/unit overlap is separated by the original follower boundary; fragment
layout witnesses remain independent and byte payload reconstruction is reused.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem primary_competitor_kind (a b : Syn .expr)
    (initial final initial' final' : List Choice) (items items' : List (List Tok))
    (level : a.level = 16) (hp : a.prec = true) (hp' : b.prec = true)
    (hy : a.yield initial = some (items, final)) (hy' : b.yield initial' = some (items', final'))
    (words : items.flatten = items'.flatten) : b.level = 16 ∧ primaryRootKind a = primaryRootKind b := by
  have levels : b.level = 16 := (partial_root_levels_equal a b initial final initial' final' items items' hp hp' hy hy' words).symm.trans level
  exact ⟨levels, primary_prefix_kinds_equal a b initial final initial' final' items items' [] [] level levels hy hy'
    (by simpa only [List.append_nil] using words)⟩

theorem ident_word_unique (name : String) : WordUnique (Syn.ident name) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  obtain ⟨level, kind⟩ := primary_competitor_kind (Syn.ident name) other
    initial final initial' final' items items' rfl hp hp' hy hy' words
  rcases expr_level_sixteen_cases other level with ⟨ty', rfl⟩ | ⟨ty', rfl⟩ | ⟨args', rfl⟩ | ⟨first', rest', rfl⟩ |
    ⟨first', rest', rfl⟩ | ⟨name', rfl⟩ | ⟨value', allowed', rfl⟩ | ⟨literal', rfl⟩ | ⟨number', unit', rfl⟩
  all_goals first | (cases kind; done) | skip
  have payload : name = name' := ident_same_yield name name' items.flatten
    (expression_partial_derives _ initial final items hy)
    (by rw [words]; exact expression_partial_derives _ initial' final' items' hy')
  rw [payload]

theorem elementary_expr_word_unique (value : Elem) (allowed : value ≠ .addressPayable) : WordUnique (Syn.elemType value allowed) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  obtain ⟨level, kind⟩ := primary_competitor_kind (Syn.elemType value allowed) other
    initial final initial' final' items items' rfl hp hp' hy hy' words
  rcases expr_level_sixteen_cases other level with ⟨ty', rfl⟩ | ⟨ty', rfl⟩ | ⟨args', rfl⟩ | ⟨first', rest', rfl⟩ |
    ⟨first', rest', rfl⟩ | ⟨name', rfl⟩ | ⟨value', allowed', rfl⟩ | ⟨literal', rfl⟩ | ⟨number', unit', rfl⟩
  all_goals first | (cases kind; done) | skip
  have shape : items = [[.elem value]] := (pure_success_split [[Tok.elem value]] items initial final hy).1
  have shape' : items' = [[.elem value']] := (pure_success_split [[Tok.elem value']] items' initial' final' hy').1
  rw [shape, shape'] at words
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at words
  have values : value = value' := Tok.elem.inj (List.cons.inj words).1
  cases values
  rfl

theorem literal_word_unique (literal : Lit) : WordUnique (Syn.lit literal) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  obtain ⟨level, kind⟩ := primary_competitor_kind (Syn.lit literal) other
    initial final initial' final' items items' rfl hp hp' hy hy' words
  rcases expr_level_sixteen_cases other level with ⟨ty', rfl⟩ | ⟨ty', rfl⟩ | ⟨args', rfl⟩ | ⟨first', rest', rfl⟩ |
    ⟨first', rest', rfl⟩ | ⟨name', rfl⟩ | ⟨value', allowed', rfl⟩ | ⟨literal', rfl⟩ | ⟨number', unit', rfl⟩
  all_goals first | (cases kind; done) | skip
  · have payload : literal = literal' := literal_same_yield literal literal' items.flatten
      (expression_partial_derives _ initial final items hy)
      (by rw [words]; exact expression_partial_derives _ initial' final' items' hy')
    rw [payload]
  · exact (literal_unit_prefix_disjoint literal number' unit' initial final initial' final' items items' [] []
      (postfixFollower_nil false) hy hy' (by simpa only [List.append_nil] using words)).elim

theorem unit_word_unique (number : NumLit) (unit : Denom) : WordUnique (Syn.litUnit number unit) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  obtain ⟨level, kind⟩ := primary_competitor_kind (Syn.litUnit number unit) other
    initial final initial' final' items items' rfl hp hp' hy hy' words
  rcases expr_level_sixteen_cases other level with ⟨ty', rfl⟩ | ⟨ty', rfl⟩ | ⟨args', rfl⟩ | ⟨first', rest', rfl⟩ |
    ⟨first', rest', rfl⟩ | ⟨name', rfl⟩ | ⟨value', allowed', rfl⟩ | ⟨literal', rfl⟩ | ⟨number', unit', rfl⟩
  all_goals first | (cases kind; done) | skip
  · exact (literal_unit_prefix_disjoint literal' number unit initial' final' initial final items' items [] []
      (postfixFollower_nil false) hy' hy (by simpa only [List.append_nil] using words.symm)).elim
  · have shape : items = [[.num number, .denom unit]] :=
      (pure_success_split [[Tok.num number, .denom unit]] items initial final hy).1
    have shape' : items' = [[.num number', .denom unit']] :=
      (pure_success_split [[Tok.num number', .denom unit']] items' initial' final' hy').1
    rw [shape, shape'] at words
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at words
    have numbers : number = number' := Tok.num.inj (List.cons.inj words).1
    have units : unit = unit' := Tok.denom.inj (List.cons.inj (List.cons.inj words).2).1
    rw [numbers, units]

end Solidity.Frontend.ExpressionUniqueness
