import Solidity.Frontend.ExpressionUniqueness.BinaryIdentity
import Solidity.Frontend.ExpressionUniqueness.BoundaryIdentity
import Solidity.Frontend.ExpressionUniqueness.PostfixIdentity
import Solidity.Frontend.ExpressionUniqueness.PrimaryChildIdentity
import Solidity.Frontend.ExpressionUniqueness.ArgumentIdentity
import Solidity.Frontend.ExpressionUniqueness.TypeIdentityControls
import Solidity.Frontend.ExpressionUniqueness.Statement

/-!
# Certified expression yield uniqueness over the original intrinsic syntax

Exhaustive structural induction discharges every actual-child identity premise,
including recursive expression/type/parameter/list/optional/argument cycles.
The public theorem compares independent existing Syn.Derives witnesses and the
original Syn.prec certificates. No parser determinism, root split or additional
producer premise is used.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem recursive_yield_property {c : Cat} (e : Syn c) : RecursiveYieldProperty e := by
  induction e with
  | @nil c =>
    cases c with
    | expr => exact nil_vector_unique .expr
    | param => exact nil_vector_unique .param
    | namedArg => exact nil_vector_unique .namedArg
    | opt c =>
      cases c with
      | expr => exact nil_vector_unique (.opt .expr)
      | _ => trivial
    | _ => trivial
  | @cons c head tail ihHead ihTail =>
    cases c with
    | expr => exact cons_vector_unique head tail ihHead ihTail
    | param => exact cons_vector_unique head tail ihHead ihTail
    | namedArg => exact cons_vector_unique head tail ihHead ihTail
    | opt c =>
      cases c with
      | expr => exact cons_vector_unique head tail ihHead ihTail
      | _ => trivial
    | _ => trivial
  | @none c =>
    cases c with
    | expr => exact none_expr_word_unique
    | _ => trivial
  | @some c child ih =>
    cases c with
    | expr => exact some_expr_word_unique child ih
    | _ => trivial
  | positional args ih => exact positional_word_unique args ih
  | named args ih => exact named_word_unique args ih
  | namedArg name value ih => exact namedArg_word_unique name value ih
  | param ty loc name ih => exact parameter_word_unique ty loc name ih
  | elem value => exact elementary_type_word_unique value
  | userType path => exact user_type_word_unique path
  | mapping key kn value vn ih => exact mapping_type_word_unique key kn value vn ih
  | fnType params vis mu returns ihParams ihReturns => exact fn_type_word_unique params returns vis mu ihParams ihReturns
  | array base length ihBase ihLength => exact array_type_word_unique base length ihBase ihLength
  | index base index ihBase ihIndex => exact index_word_unique base index ihBase ihIndex
  | slice base start stop ihBase ihStart ihStop => exact slice_word_unique base start stop ihBase ihStart ihStop
  | member base name ih => exact member_word_unique base name ih
  | callOptions base first args ihBase ihFirst ihArgs => exact callOptions_word_unique base first args ihBase ihFirst ihArgs
  | call base args ihBase ihArgs => exact call_word_unique base args ihBase ihArgs
  | payableConv args ih => exact payableConv_word_unique args ih
  | metaType ty ih => exact metaType_word_unique ty ih
  | unaryPrefix op child ih => exact unaryPrefix_word_unique op child ih
  | unarySuffix op child ih => exact unarySuffix_word_unique op child ih
  | exp left right ihLeft ihRight => exact exp_word_unique left right ihLeft ihRight
  | mulDivMod op left right ihLeft ihRight => exact mulDivMod_word_unique op left right ihLeft ihRight
  | addSub op left right ihLeft ihRight => exact addSub_word_unique op left right ihLeft ihRight
  | shift op left right ihLeft ihRight => exact shift_word_unique op left right ihLeft ihRight
  | bitAnd left right ihLeft ihRight => exact bitAnd_word_unique left right ihLeft ihRight
  | bitXor left right ihLeft ihRight => exact bitXor_word_unique left right ihLeft ihRight
  | bitOr left right ihLeft ihRight => exact bitOr_word_unique left right ihLeft ihRight
  | order op left right ihLeft ihRight => exact order_word_unique op left right ihLeft ihRight
  | equality op left right ihLeft ihRight => exact equality_word_unique op left right ihLeft ihRight
  | and left right ihLeft ihRight => exact and_word_unique left right ihLeft ihRight
  | or left right ihLeft ihRight => exact or_word_unique left right ihLeft ihRight
  | assign op left right ihLeft ihRight => exact assign_word_unique op left right ihLeft ihRight
  | cond condition yes no ihCondition ihYes ihNo => exact cond_word_unique condition yes no ihCondition ihYes ihNo
  | new ty ih => exact new_word_unique ty ih
  | tuple first rest ihFirst ihRest => exact tuple_word_unique first rest ihFirst ihRest
  | inlineArray first rest ihFirst ihRest => exact inlineArray_word_unique first rest ihFirst ihRest
  | ident name => exact ident_word_unique name
  | lit literal => exact literal_word_unique literal
  | litUnit number unit => exact unit_word_unique number unit
  | elemType value allowed => exact elementary_expr_word_unique value allowed
  | _ => trivial

theorem expression_yield_word_unique (e : Syn .expr) : WordUnique e := recursive_yield_property e

theorem type_yield_word_unique (e : Syn .typeName) : WordUnique e := recursive_yield_property e

theorem parameter_yield_word_unique (e : Syn .param) : WordUnique e := recursive_yield_property e

theorem argument_yield_word_unique (e : Syn .callArgs) : WordUnique e := recursive_yield_property e

theorem namedArg_yield_word_unique (e : Syn .namedArg) : WordUnique e := recursive_yield_property e

theorem optional_expression_yield_word_unique (e : Syn (.opt .expr)) : WordUnique e := recursive_yield_property e

theorem certified_expression_yield_unique (a b : Syn .expr) (ts : List Tok)
    (da : a.Derives ts) (ha : a.prec = true) (db : b.Derives ts) (hb : b.prec = true) : a = b := by
  obtain ⟨initial, ht⟩ := da
  obtain ⟨initial', ht'⟩ := db
  exact expression_yield_word_unique a b initial [] initial' [] [ts] [ts] ha hb
    ((expr_toks_iff a initial ts).mp ht) ((expr_toks_iff b initial' ts).mp ht') rfl

theorem certifiedYieldUnique : CertifiedYieldUnique := certified_expression_yield_unique

end Solidity.Frontend.ExpressionUniqueness
