import Solidity.Frontend.ExpressionUniqueness.ElementaryPathPrefix
import Solidity.Frontend.ExpressionUniqueness.TypeYieldSplit

/-!
# Function-type words have maximal parameter, attribute and returns cuts

The helpers use concrete keyword-run and follower conditions, supplied by actual
printer execution and surrounding syntax in the final certificate results.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem typeAttribute_of_forbidden_false (t : Tok) (h : typeAtomForbidden t = false) :
    typeAttributeToken t = false := by
  cases t <;> try rfl
  case kw k => cases k <;> first | rfl | exact h

theorem typeAtomBoundary_attributes (tail : List Tok) (hb : TypeAtomBoundary tail) :
    TokenBoundary typeAttributeToken tail := by
  intro t rest he
  exact typeAttribute_of_forbidden_false t (hb t rest he)

theorem tokenBoundary_cons (p : Tok → Bool) (token : Tok) (rest : List Tok) (hp : p token = false) :
    TokenBoundary p (token :: rest) := by
  intro t suffix he
  have same : token = t := (List.cons.inj he).1
  rw [← same]
  exact hp

theorem type_returns_attribute_boundary (rs : List (List Tok)) (tail : List Tok)
    (hb : TypeAtomBoundary tail) : TokenBoundary typeAttributeToken
      ((if rs.isEmpty then [] else tk .returns ++ parens (commaSep rs)) ++ tail) := by
  split
  · exact typeAtomBoundary_attributes tail hb
  · simpa only [tk, List.append_assoc, List.singleton_append] using
      tokenBoundary_cons typeAttributeToken (.kw .returns) (parens (commaSep rs) ++ tail) rfl

theorem type_returns_prefix_unique (rs rs' : List (List Tok)) (tail tail' : List Tok)
    (hr : Balanced (commaSep rs)) (hr' : Balanced (commaSep rs'))
    (hb : TypeAtomBoundary tail) (hb' : TypeAtomBoundary tail')
    (words : (if rs.isEmpty then [] else tk .returns ++ parens (commaSep rs)) ++ tail =
      (if rs'.isEmpty then [] else tk .returns ++ parens (commaSep rs')) ++ tail') :
    (if rs.isEmpty then [] else tk .returns ++ parens (commaSep rs)) =
      (if rs'.isEmpty then [] else tk .returns ++ parens (commaSep rs')) ∧ tail = tail' := by
  cases empty : rs.isEmpty with
  | false =>
    cases empty' : rs'.isEmpty with
    | false =>
      simp only [empty, empty', Bool.false_eq_true, ↓reduceIte, tk,
        List.singleton_append] at words ⊢
      obtain ⟨payload, following⟩ := parens_prefix_unique (commaSep rs) (commaSep rs') tail tail'
        hr hr' (List.cons.inj words).2
      exact ⟨by rw [payload], following⟩
    | true =>
      simp only [empty, empty', Bool.false_eq_true, ↓reduceIte, List.nil_append, tk,
        List.singleton_append] at words ⊢
      exact False.elim (tokenBoundary_not_selected typeAtomForbidden tail' hb' (.kw .returns) rfl _ words.symm)
  | true =>
    cases empty' : rs'.isEmpty with
    | false =>
      simp only [empty, empty', Bool.false_eq_true, ↓reduceIte, List.nil_append, tk,
        List.singleton_append] at words ⊢
      exact False.elim (tokenBoundary_not_selected typeAtomForbidden tail hb (.kw .returns) rfl _ words)
    | true =>
      simp only [empty, empty', ↓reduceIte, List.nil_append] at words ⊢
      exact ⟨True.intro, words⟩

theorem fn_type_word_parts_unique (ps ps' attrs attrs' : List Tok)
    (rs rs' : List (List Tok)) (tail tail' : List Tok)
    (hp : Balanced ps) (hp' : Balanced ps')
    (ha : AllTokens typeAttributeToken attrs) (ha' : AllTokens typeAttributeToken attrs')
    (hr : Balanced (commaSep rs)) (hr' : Balanced (commaSep rs'))
    (hb : TypeAtomBoundary tail) (hb' : TypeAtomBoundary tail')
    (words : (tk .function ++ parens ps ++ attrs ++
        (if rs.isEmpty then [] else tk .returns ++ parens (commaSep rs))) ++ tail =
      (tk .function ++ parens ps' ++ attrs' ++
        (if rs'.isEmpty then [] else tk .returns ++ parens (commaSep rs'))) ++ tail') :
    ps = ps' ∧ attrs = attrs' ∧
      (if rs.isEmpty then [] else tk .returns ++ parens (commaSep rs)) =
        (if rs'.isEmpty then [] else tk .returns ++ parens (commaSep rs')) ∧ tail = tail'  := by
  have body : parens ps ++ (attrs ++ ((if rs.isEmpty then [] else tk .returns ++ parens (commaSep rs)) ++ tail)) =
      parens ps' ++ (attrs' ++ ((if rs'.isEmpty then [] else tk .returns ++ parens (commaSep rs')) ++ tail')) := by
    have expanded := words
    simp only [tk, List.cons_append, List.nil_append, List.append_assoc] at expanded
    exact (List.cons.inj expanded).2
  obtain ⟨params, afterParams⟩ := parens_prefix_unique ps ps' _ _ hp hp' body
  obtain ⟨attributes, afterAttrs⟩ := maximal_token_run_unique typeAttributeToken attrs attrs' _ _ ha ha'
    (type_returns_attribute_boundary rs tail hb) (type_returns_attribute_boundary rs' tail' hb') afterParams
  obtain ⟨returns, following⟩ := type_returns_prefix_unique rs rs' tail tail' hr hr' hb hb' afterAttrs
  exact ⟨params, attributes, returns, following⟩

theorem fn_type_word_prefix_unique (ps ps' attrs attrs' : List Tok)
    (rs rs' : List (List Tok)) (tail tail' : List Tok)
    (hp : Balanced ps) (hp' : Balanced ps')
    (ha : AllTokens typeAttributeToken attrs) (ha' : AllTokens typeAttributeToken attrs')
    (hr : Balanced (commaSep rs)) (hr' : Balanced (commaSep rs'))
    (hb : TypeAtomBoundary tail) (hb' : TypeAtomBoundary tail')
    (words : (tk .function ++ parens ps ++ attrs ++
        (if rs.isEmpty then [] else tk .returns ++ parens (commaSep rs))) ++ tail =
      (tk .function ++ parens ps' ++ attrs' ++
        (if rs'.isEmpty then [] else tk .returns ++ parens (commaSep rs'))) ++ tail') :
    (tk .function ++ parens ps ++ attrs ++
        (if rs.isEmpty then [] else tk .returns ++ parens (commaSep rs))) =
      (tk .function ++ parens ps' ++ attrs' ++
        (if rs'.isEmpty then [] else tk .returns ++ parens (commaSep rs'))) ∧ tail = tail' := by
  obtain ⟨params, attributes, returns, following⟩ := fn_type_word_parts_unique ps ps' attrs attrs'
    rs rs' tail tail' hp hp' ha ha' hr hr' hb hb' words
  exact ⟨by rw [params, attributes, returns], following⟩

end Solidity.Frontend.ExpressionUniqueness
