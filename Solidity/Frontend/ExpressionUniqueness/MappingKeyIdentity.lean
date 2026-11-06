import Solidity.Frontend.ExpressionUniqueness.TypeLeafIdentity

/-!
# Existing intrinsic mapping key word reconstruction

MapKey is the existing unindexed intrinsic sum. These words and concrete
followers are derived from mapping syntax, never another AST or an assumed root
split. Elementary and path spellings are disjoint at the first token.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def mapKeyWord : MapKey → List Tok
  | .elem e _ => e.toks
  | .path p => p.toks

theorem elementary_path_prefix_disjoint (e : Elem) (path : IdPath) (tail tail' : List Tok) :
    e.toks ++ tail ≠ path.toks ++ tail' := by
  intro words
  rcases elem_tokens_shape e with rfl | single
  · cases words
  · rw [single] at words
    cases words

theorem mapKey_word_prefix_unique (a b : MapKey) (tail tail' : List Tok)
    (hb : TypeAtomBoundary tail) (hb' : TypeAtomBoundary tail')
    (words : mapKeyWord a ++ tail = mapKeyWord b ++ tail') : a = b ∧ tail = tail' := by
  cases a with
  | elem e allowed =>
    cases b with
    | elem f allowed' =>
      obtain ⟨keys, following⟩ := elementary_type_prefix_unique e f tail tail' hb hb' words
      have key : e = f := elementary_tokens_injective e f keys
      cases key
      exact ⟨rfl, following⟩
    | path q => exact (elementary_path_prefix_disjoint e q tail tail' words).elim
  | path p =>
    cases b with
    | elem f allowed' => exact (elementary_path_prefix_disjoint f p tail' tail words.symm).elim
    | path q =>
      obtain ⟨keys, following⟩ := path_type_prefix_unique p q tail tail' hb hb' words
      have key : p = q := path_tokens_injective p q keys
      cases key
      exact ⟨rfl, following⟩

theorem mapping_key_tail_boundary (name : Option String) (afterArrow : List Tok) :
    TypeAtomBoundary (optToks idt name ++ pu .doubleArrow ++ afterArrow) := by
  cases name <;> exact tokenBoundary_cons _ _ _ rfl

theorem mapping_name_arrow_unique (name name' : Option String) (after after' : List Tok)
    (words : optToks idt name ++ pu .doubleArrow ++ after = optToks idt name' ++ pu .doubleArrow ++ after') :
    name = name' ∧ after = after' := by
  cases name with
  | none =>
    cases name' with
    | none => exact ⟨rfl, (List.cons.inj words).2⟩
    | some name' => cases words
  | some name =>
    cases name' with
    | none => cases words
    | some name' =>
      have names : name = name' := Tok.ident.inj (List.cons.inj words).1
      exact ⟨congrArg some names, (List.cons.inj (List.cons.inj words).2).2⟩

theorem parens_word_injective (xs ys : List Tok) (words : parens xs = parens ys) : xs = ys := by
  have tails : xs ++ [Tok.punct .rparen] = ys ++ [Tok.punct .rparen] := (List.cons.inj words).2
  simpa only [List.append_cancel_right_eq] using tails

end Solidity.Frontend.ExpressionUniqueness
