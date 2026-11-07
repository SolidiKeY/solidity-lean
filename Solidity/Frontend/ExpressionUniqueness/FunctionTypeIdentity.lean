import Solidity.Frontend.ExpressionUniqueness.ParameterWords
import Solidity.Frontend.ExpressionUniqueness.AttributeFieldIdentity
import Solidity.Frontend.ExpressionUniqueness.FnTypePrefix
import Solidity.Frontend.ExpressionUniqueness.ExpressionCommaFree

/-!
# Actual function-type vectors and field identity

Successful original printers supply parameter nonemptiness, comma freedom,
attribute fields and optional returns boundaries. All recursive premises are
structural identity facts for the actual parameter/returns children.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem type_returns_vectors_unique (xs ys : List (List Tok))
    (fx : CommaFreeItems xs) (fy : CommaFreeItems ys) (nx : NonemptyWords xs) (ny : NonemptyWords ys)
    (words : (if xs.isEmpty then [] else tk .returns ++ parens (commaSep xs)) =
      (if ys.isEmpty then [] else tk .returns ++ parens (commaSep ys))) : xs = ys := by
  cases xs with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      change [] = Tok.kw .returns :: _ at words
      cases words
  | cons x xs =>
    cases ys with
    | nil =>
      change Tok.kw .returns :: _ = [] at words
      cases words
    | cons y ys =>
      have enclosures : parens (commaSep (x :: xs)) = parens (commaSep (y :: ys)) := (List.cons.inj words).2
      have bodies := (last_parens_cut_unique [] (commaSep (x :: xs)) [] (commaSep (y :: ys))
        (balanced_commaSep (commaFreeItems_balanced fx))
        (balanced_commaSep (commaFreeItems_balanced fy)) enclosures).2
      exact commaSep_unique_nonempty_words (x :: xs) (y :: ys) fx fy nx ny bodies

theorem fn_type_prec_children (params returns : Syn (.list .param))
    (vis : Option Visibility) (mu : Option Mutability)
    (hp : (Syn.fnType params vis mu returns).prec = true) : params.prec = true ∧ returns.prec = true := by
  have hall : (Syn.fnType params vis mu returns).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.fnType params vis mu returns).precNode && params.all Syn.precNode && returns.all Syn.precNode) = true at hall
  exact ⟨all_prec_implies_prec params (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).2,
    all_prec_implies_prec returns (Bool.and_eq_true_iff.mp hall).2⟩

theorem fn_type_same_constructor_unique (params returns params' returns' : Syn (.list .param))
    (vis vis' : Option Visibility) (mu mu' : Option Mutability)
    (ihParams : VectorUnique params) (ihReturns : VectorUnique returns)
    (initial final initial' final' : List Choice) (items items' : List (List Tok))
    (hp : (Syn.fnType params vis mu returns).prec = true)
    (hp' : (Syn.fnType params' vis' mu' returns').prec = true)
    (hy : (Syn.fnType params vis mu returns).yield initial = some (items, final))
    (hy' : (Syn.fnType params' vis' mu' returns').yield initial' = some (items', final'))
    (words : items.flatten = items'.flatten) : Syn.fnType params vis mu returns = Syn.fnType params' vis' mu' returns' := by
  obtain ⟨order, ps, attrs, rs, afterOrder, afterParams, afterAttrs, ho, hps, ha, hr, shape⟩ :=
    fn_type_yield_parts params vis mu returns initial final items hy
  obtain ⟨order', ps', attrs', rs', afterOrder', afterParams', afterAttrs', ho', hps', ha', hr', shape'⟩ :=
    fn_type_yield_parts params' vis' mu' returns' initial' final' items' hy'
  have fp : CommaFreeItems ps := expressionCategory_yield_commaFree params rfl afterOrder ps afterParams hps
  have fp' : CommaFreeItems ps' := expressionCategory_yield_commaFree params' rfl afterOrder' ps' afterParams' hps'
  have fr : CommaFreeItems rs := expressionCategory_yield_commaFree returns rfl afterAttrs rs final hr
  have fr' : CommaFreeItems rs' := expressionCategory_yield_commaFree returns' rfl afterAttrs' rs' final' hr'
  rw [shape, shape'] at words
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at words
  have framed : (tk .function ++ parens (commaSep ps) ++ attrs ++
      (if rs.isEmpty then [] else tk .returns ++ parens (commaSep rs))) ++ [] =
      (tk .function ++ parens (commaSep ps') ++ attrs' ++
      (if rs'.isEmpty then [] else tk .returns ++ parens (commaSep rs'))) ++ [] := by
    simpa only [List.append_nil] using words
  obtain ⟨paramsWords, attrWords, returnWords, following⟩ := fn_type_word_parts_unique
    (commaSep ps) (commaSep ps') attrs attrs' rs rs' [] []
    (balanced_commaSep (commaFreeItems_balanced fp)) (balanced_commaSep (commaFreeItems_balanced fp'))
    (attrsP_typeAttributes vis mu order afterParams attrs afterAttrs ha)
    (attrsP_typeAttributes vis' mu' order' afterParams' attrs' afterAttrs' ha')
    (balanced_commaSep (commaFreeItems_balanced fr)) (balanced_commaSep (commaFreeItems_balanced fr'))
    (tokenBoundary_nil _) (tokenBoundary_nil _) framed
  have pVector : ps = ps' := commaSep_unique_nonempty_words ps ps' fp fp'
    (parameterList_yield_nonemptyWords params afterOrder afterParams ps hps)
    (parameterList_yield_nonemptyWords params' afterOrder' afterParams' ps' hps') paramsWords
  have rVector : rs = rs' := type_returns_vectors_unique rs rs' fr fr'
    (parameterList_yield_nonemptyWords returns afterAttrs final rs hr)
    (parameterList_yield_nonemptyWords returns' afterAttrs' final' rs' hr') returnWords
  obtain ⟨visEq, muEq⟩ := type_attributes_fields_unique vis vis' mu mu' order order'
    afterParams afterAttrs afterParams' afterAttrs' attrs attrs' ha ha' attrWords
  obtain ⟨hpp, hpr⟩ := fn_type_prec_children params returns vis mu hp
  obtain ⟨hpp', hpr'⟩ := fn_type_prec_children params' returns' vis' mu' hp'
  have pEq : params = params' := ihParams params' afterOrder afterParams afterOrder' afterParams' ps ps' hpp hpp' hps hps' pVector
  have rEq : returns = returns' := ihReturns returns' afterAttrs final afterAttrs' final' rs rs' hpr hpr' hr hr' rVector
  rw [pEq, rEq, visEq, muEq]

end Solidity.Frontend.ExpressionUniqueness
