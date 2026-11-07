import Solidity.Frontend.ExpressionUniqueness.ContainerIdentity
import Solidity.Frontend.ExpressionUniqueness.TypeAtomPrefix
import Solidity.Frontend.ExpressionUniqueness.PostfixSpans

/-!
# Reconstruct intrinsic array type roots and recursive identity

Balanced dimension words and maximal actual atom prefixes separate arrays from
all non-array types, even mapping/function atoms with arbitrary descendants.
The array identity step uses only its actual structural child induction facts.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem squareWords_nonempty_last (before : List (List Tok)) (last : List Tok) :
    squareWords (before ++ [last]) ≠ [] := by
  rw [squareWords_append, squareWords_cons, squareWords_nil]
  apply word_append_nonempty_right
  intro empty
  change Tok.punct .lbrack :: _ = [] at empty
  cases empty

theorem array_atom_yields_disjoint (base : Syn .typeName) (length : Syn (.opt .expr)) (other : Syn .typeName)
    (initial final initial' final' : List Choice) (items items' : List (List Tok))
    (atomOther : isTypeAtom other = true)
    (hy : (Syn.array base length).yield initial = some (items, final))
    (hy' : other.yield initial' = some (items', final')) : items.flatten ≠ items'.flatten := by
  intro words
  obtain ⟨xs, ys, middle, hx, hl, shape⟩ := array_type_yield_parts base length initial final items hy
  obtain ⟨atom, atomItems, atomFinal, payloads, atomFact, atomYield, payloadsBalance, spine⟩ :=
    type_yield_spine base initial middle xs hx
  have arrayWord : items.flatten = atomItems.flatten ++ squareWords (payloads ++ [ys.flatten]) := by
    rw [shape]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [spine, squareWords_append, squareWords_cons, squareWords_nil]
    simp only [List.append_nil, List.append_assoc]
  have following : TypeAtomBoundary (squareWords (payloads ++ [ys.flatten])) := by
    have bound := squareWords_boundary typeAtomForbidden (payloads ++ [ys.flatten]) [] rfl
      (tokenBoundary_nil typeAtomForbidden)
    simpa only [List.append_nil] using bound
  have prefixWords : atomItems.flatten ++ squareWords (payloads ++ [ys.flatten]) = items'.flatten ++ [] := by
    rw [List.append_nil, ← arrayWord, words]
  have cuts := type_atom_yield_prefix_unique atom other initial atomFinal initial' final'
    atomItems items' (squareWords (payloads ++ [ys.flatten])) [] atomFact atomOther following
    (tokenBoundary_nil typeAtomForbidden) atomYield hy' prefixWords
  exact squareWords_nonempty_last payloads ys.flatten cuts.2

theorem array_type_child_spans (base base' : Syn .typeName) (length length' : Syn (.opt .expr))
    (initial final initial' final' : List Choice) (items items' : List (List Tok))
    (hy : (Syn.array base length).yield initial = some (items, final))
    (hy' : (Syn.array base' length').yield initial' = some (items', final'))
    (words : items.flatten = items'.flatten) : PairYieldSpans base length base' length' initial final initial' final' := by
  obtain ⟨xs, ys, middle, hx, hl, shape⟩ := array_type_yield_parts base length initial final items hy
  obtain ⟨xs', ys', middle', hx', hl', shape'⟩ := array_type_yield_parts base' length' initial' final' items' hy'
  have bal : Balanced ys.flatten := balancedItems_flatten
    (expressionCategory_yield_balanced length rfl middle ys final hl)
  have bal' : Balanced ys'.flatten := balancedItems_flatten
    (expressionCategory_yield_balanced length' rfl middle' ys' final' hl')
  rw [shape, shape'] at words
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at words
  obtain ⟨bases, lengths⟩ := last_square_cut_unique xs.flatten ys.flatten xs'.flatten ys'.flatten bal bal' words
  exact ⟨xs, ys, xs', ys', middle, middle', hx, hl, hx', hl', bases, lengths⟩

theorem array_type_prec_children (base : Syn .typeName) (length : Syn (.opt .expr))
    (hp : (Syn.array base length).prec = true) : base.prec = true ∧ length.prec = true := by
  have hall : (Syn.array base length).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.array base length).precNode && base.all Syn.precNode && length.all Syn.precNode) = true at hall
  exact ⟨all_prec_implies_prec base (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).2,
    all_prec_implies_prec length (Bool.and_eq_true_iff.mp hall).2⟩

theorem array_type_word_unique (base : Syn .typeName) (length : Syn (.opt .expr))
    (ihBase : WordUnique base) (ihLength : WordUnique length) : WordUnique (Syn.array base length) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  cases other with
  | array base' length' =>
    obtain ⟨xs, ys, xs', ys', middle, middle', hx, hl, hx', hl', bases, lengths⟩ :=
      array_type_child_spans base base' length length' initial final initial' final' items items' hy hy' words
    obtain ⟨hpb, hpl⟩ := array_type_prec_children base length hp
    obtain ⟨hpb', hpl'⟩ := array_type_prec_children base' length' hp'
    have eb : base = base' := ihBase base' initial middle initial' middle' xs xs' hpb hpb' hx hx' bases
    have el : length = length' := ihLength length' middle final middle' final' ys ys' hpl hpl' hl hl' lengths
    rw [eb, el]
  | elem value => exact (array_atom_yields_disjoint base length _ initial final initial' final' items items' rfl hy hy' words).elim
  | userType path => exact (array_atom_yields_disjoint base length _ initial final initial' final' items items' rfl hy hy' words).elim
  | mapping key kn value vn => exact (array_atom_yields_disjoint base length _ initial final initial' final' items items' rfl hy hy' words).elim
  | fnType params vis mu returns => exact (array_atom_yields_disjoint base length _ initial final initial' final' items items' rfl hy hy' words).elim

end Solidity.Frontend.ExpressionUniqueness
