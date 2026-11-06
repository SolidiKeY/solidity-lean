import Solidity.Frontend.ExpressionUniqueness.TypeAtomPrefix

/-!
# Arbitrary intrinsic type words reconstruct their maximal prefix

Actual execution derives the existing type atom and balanced array spine.
Concrete follower conditions determine the maximal cut; certified expression
results must establish those conditions from their original syntax/precedence.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem type_yield_prefix_unique (a b : Syn .typeName)
    (initial final initial' final' : List Choice) (items items' : List (List Tok)) (tail tail' : List Tok)
    (hb : TypeBoundary tail) (hb' : TypeBoundary tail')
    (hy : a.yield initial = some (items, final)) (hy' : b.yield initial' = some (items', final'))
    (words : items.flatten ++ tail = items'.flatten ++ tail') :
    items.flatten = items'.flatten ∧ tail = tail' := by
  obtain ⟨atom, atomItems, atomFinal, payloads, kind, atomYield, bal, shape⟩ :=
    type_yield_spine a initial final items hy
  obtain ⟨atom', atomItems', atomFinal', payloads', kind', atomYield', bal', shape'⟩ :=
    type_yield_spine b initial' final' items' hy'
  have atomFollowing : atomItems.flatten ++ (squareWords payloads ++ tail) =
      atomItems'.flatten ++ (squareWords payloads' ++ tail') := by
    rw [shape, shape'] at words
    simpa only [List.append_assoc] using words
  obtain ⟨atomWords, afterAtom⟩ := type_atom_yield_prefix_unique atom atom' initial atomFinal initial' atomFinal'
    atomItems atomItems' (squareWords payloads ++ tail) (squareWords payloads' ++ tail') kind kind'
    (typeAtomBoundary_squareWords payloads tail hb) (typeAtomBoundary_squareWords payloads' tail' hb')
    atomYield atomYield' atomFollowing
  obtain ⟨spines, following⟩ := squareWords_cut_unique payloads payloads' tail tail' bal bal' hb.2 hb'.2 afterAtom
  exact ⟨by rw [shape, shape', atomWords, spines], following⟩

end Solidity.Frontend.ExpressionUniqueness
