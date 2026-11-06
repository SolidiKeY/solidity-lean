import Solidity.Frontend.ExpressionUniqueness.PostfixYieldSplit
import Solidity.Frontend.ExpressionUniqueness.AttributeTokens

/-!
# Invert actual type printer executions

All existing fields and layout choices are retained. The function-type result
recovers its actual attribute order and successful component executions.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem array_type_yield_parts (base : Syn .typeName) (length : Syn (.opt .expr))
    (initial final : List Choice) (items : List (List Tok))
    (hy : (Syn.array base length).yield initial = some (items, final)) :
    ∃ xs ys middle, base.yield initial = some (xs, middle) ∧ length.yield middle = some (ys, final) ∧
      items = [xs.flatten ++ pu .lbrack ++ ys.flatten ++ pu .rbrack] :=
  pair_pure_success_split base.yield length.yield
    (fun xs ys => [xs.flatten ++ pu .lbrack ++ ys.flatten ++ pu .rbrack]) initial final items hy

theorem mapping_type_yield_parts (key : MapKey) (keyName : Option String)
    (value : Syn .typeName) (valueName : Option String) (initial final : List Choice)
    (items : List (List Tok))
    (hy : (Syn.mapping key keyName value valueName).yield initial = some (items, final)) :
    ∃ xs, value.yield initial = some (xs, final) ∧
      items = [tk .mapping ++ parens ((match key with | .elem e _ => e.toks | .path p => p.toks) ++
        optToks idt keyName ++ pu .doubleArrow ++ xs.flatten ++ optToks idt valueName)] := by
  cases key with
  | elem e allowed =>
    exact one_pure_success_split value.yield (fun xs => [tk .mapping ++ parens
      (e.toks ++ optToks idt keyName ++ pu .doubleArrow ++ xs.flatten ++ optToks idt valueName)])
      initial final items hy
  | path p =>
    exact one_pure_success_split value.yield (fun xs => [tk .mapping ++ parens
      (p.toks ++ optToks idt keyName ++ pu .doubleArrow ++ xs.flatten ++ optToks idt valueName)])
      initial final items hy

theorem fn_type_yield_parts (params : Syn (.list .param)) (vis : Option Visibility)
    (mu : Option Mutability) (returns : Syn (.list .param)) (initial final : List Choice)
    (items : List (List Tok))
    (hy : (Syn.fnType params vis mu returns).yield initial = some (items, final)) :
    ∃ order ps attrs rs afterOrder afterParams afterAttrs,
      popAttrs initial = some (order, afterOrder) ∧ params.yield afterOrder = some (ps, afterParams) ∧
      attrsP (single .vis (optToks Visibility.toks vis) ++ single .mutab (optToks Mutability.toks mu))
        [] order afterParams = some (attrs, afterAttrs) ∧ returns.yield afterAttrs = some (rs, final) ∧
      items = [tk .function ++ parens (commaSep ps) ++ attrs ++
        (if rs.isEmpty then [] else tk .returns ++ parens (commaSep rs))] := by
  obtain ⟨order, afterOrder, ho, remainder⟩ := bind_success_split popAttrs _ initial final items hy
  obtain ⟨ps, afterParams, hp, remainder'⟩ := bind_success_split params.yield _ afterOrder final items remainder
  obtain ⟨attrs, rs, afterAttrs, ha, hr, shape⟩ := pair_pure_success_split
    (attrsP (single .vis (optToks Visibility.toks vis) ++ single .mutab (optToks Mutability.toks mu)) [] order)
    returns.yield (fun attrs rs => [tk .function ++ parens (commaSep ps) ++ attrs ++
      (if rs.isEmpty then [] else tk .returns ++ parens (commaSep rs))]) afterParams final items remainder'
  exact ⟨order, ps, attrs, rs, afterOrder, afterParams, afterAttrs, ho, hp, ha, hr, shape⟩

theorem fn_type_actual_attribute_run (params : Syn (.list .param)) (vis : Option Visibility)
    (mu : Option Mutability) (returns : Syn (.list .param)) (initial final : List Choice)
    (items : List (List Tok))
    (hy : (Syn.fnType params vis mu returns).yield initial = some (items, final)) :
    ∃ ps attrs rs, Balanced (commaSep ps) ∧ AllTokens typeAttributeToken attrs ∧ Balanced (commaSep rs) ∧
      items = [tk .function ++ parens (commaSep ps) ++ attrs ++
        (if rs.isEmpty then [] else tk .returns ++ parens (commaSep rs))] := by
  obtain ⟨order, ps, attrs, rs, afterOrder, afterParams, afterAttrs, ho, hp, ha, hr, shape⟩ :=
    fn_type_yield_parts params vis mu returns initial final items hy
  exact ⟨ps, attrs, rs,
    balanced_commaSep (expressionCategory_yield_balanced params rfl afterOrder ps afterParams hp),
    attrsP_typeAttributes vis mu order afterParams attrs afterAttrs ha,
    balanced_commaSep (expressionCategory_yield_balanced returns rfl afterAttrs rs final hr), shape⟩

end Solidity.Frontend.ExpressionUniqueness
