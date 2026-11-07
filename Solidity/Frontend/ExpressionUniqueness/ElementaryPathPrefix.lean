import Solidity.Frontend.ExpressionUniqueness.TypePrefixAlgebra

/-!
# Elementary type and path words have maximal prefix cuts

The concrete type-atom boundary rejects payable and period continuations. It
will be derived from the original surrounding syntax in certificate results.
All element dimensions and arbitrary path/string lengths remain quantified.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem tokenBoundary_not_selected (p : Tok → Bool) (tail : List Tok) (hb : TokenBoundary p tail)
    (token : Tok) (hit : p token = true) (rest : List Tok) : tail ≠ token :: rest := by
  intro words
  have miss : p token = false := hb token rest words
  rw [hit] at miss
  cases miss

theorem elem_tokens_shape (e : Elem) : e = .addressPayable ∨ e.toks = [.elem e] := by
  cases e <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem elementary_type_prefix_unique (e f : Elem) (tail tail' : List Tok)
    (hb : TypeAtomBoundary tail) (hb' : TypeAtomBoundary tail')
    (words : e.toks ++ tail = f.toks ++ tail') : e.toks = f.toks ∧ tail = tail' := by
  rcases elem_tokens_shape e with rfl | single
  · rcases elem_tokens_shape f with rfl | single'
    · exact ⟨rfl, (List.cons.inj (List.cons.inj words).2).2⟩
    · rw [single'] at words
      have remainder : .kw .payable :: tail = tail' := (List.cons.inj words).2
      exact False.elim (tokenBoundary_not_selected typeAtomForbidden tail' hb' (.kw .payable) rfl tail remainder.symm)
  · rcases elem_tokens_shape f with rfl | single'
    · rw [single] at words
      have remainder : tail = .kw .payable :: tail' := (List.cons.inj words).2
      exact False.elim (tokenBoundary_not_selected typeAtomForbidden tail hb (.kw .payable) rfl tail' remainder)
    · rw [single, single'] at words
      obtain ⟨token, following⟩ := List.cons.inj words
      exact ⟨by rw [single, single', token], following⟩

theorem path_pieces_prefix_unique (xs ys : List String) (tail tail' : List Tok)
    (hb : TypeAtomBoundary tail) (hb' : TypeAtomBoundary tail')
    (words : xs.flatMap (fun name => [Tok.punct .period, .ident name]) ++ tail =
      ys.flatMap (fun name => [Tok.punct .period, .ident name]) ++ tail') :
    xs.flatMap (fun name => [Tok.punct .period, .ident name]) =
      ys.flatMap (fun name => [Tok.punct .period, .ident name]) ∧ tail = tail' := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact ⟨rfl, words⟩
    | cons first rest =>
      exact False.elim (tokenBoundary_not_selected typeAtomForbidden tail hb (.punct .period) rfl _ words)
  | cons first rest ih =>
    cases ys with
    | nil =>
      exact False.elim (tokenBoundary_not_selected typeAtomForbidden tail' hb' (.punct .period) rfl _ words.symm)
    | cons first' rest' =>
      have names : first = first' := Tok.ident.inj (List.cons.inj (List.cons.inj words).2).1
      subst first'
      have remaining : rest.flatMap (fun name => [Tok.punct .period, .ident name]) ++ tail =
          rest'.flatMap (fun name => [Tok.punct .period, .ident name]) ++ tail' :=
        (List.cons.inj (List.cons.inj words).2).2
      obtain ⟨pieces, following⟩ := ih rest' remaining
      refine ⟨?_, following⟩
      simp only [List.flatMap_cons, List.cons_append, List.nil_append]
      rw [pieces]

theorem path_type_prefix_unique (p q : IdPath) (tail tail' : List Tok)
    (hb : TypeAtomBoundary tail) (hb' : TypeAtomBoundary tail')
    (words : p.toks ++ tail = q.toks ++ tail') : p.toks = q.toks ∧ tail = tail' := by
  have heads : Tok.ident p.head = Tok.ident q.head := (List.cons.inj words).1
  have remaining : p.tail.flatMap (fun name => [Tok.punct .period, .ident name]) ++ tail =
      q.tail.flatMap (fun name => [Tok.punct .period, .ident name]) ++ tail' := (List.cons.inj words).2
  obtain ⟨pieces, following⟩ := path_pieces_prefix_unique p.tail q.tail tail tail' hb hb' remaining
  refine ⟨?_, following⟩
  change Tok.ident p.head :: _ = Tok.ident q.head :: _
  rw [heads, pieces]

end Solidity.Frontend.ExpressionUniqueness
