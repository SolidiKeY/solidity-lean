import Solidity.Frontend.ExpressionUniqueness.AttributeBalance
import Solidity.Frontend.ExpressionUniqueness.CommaFreeAlgebra
import Solidity.Frontend.ExpressionUniqueness.DelimiterReconstruction
import Solidity.Frontend.ExpressionUniqueness.ExpressionBalance
import Solidity.Frontend.ExpressionUniqueness.ExpressionCommaFree
import Solidity.Frontend.ExpressionUniqueness.ExpressionLowFree
import Solidity.Frontend.ExpressionUniqueness.Families
import Solidity.Frontend.ExpressionUniqueness.Fixtures
import Solidity.Frontend.ExpressionUniqueness.Fragments
import Solidity.Frontend.ExpressionUniqueness.Grouping
import Solidity.Frontend.ExpressionUniqueness.LowControls
import Solidity.Frontend.ExpressionUniqueness.LowFreeAlgebra
import Solidity.Frontend.ExpressionUniqueness.LowRoot
import Solidity.Frontend.ExpressionUniqueness.Primary
import Solidity.Frontend.ExpressionUniqueness.Refusals
import Solidity.Frontend.ExpressionUniqueness.ReverseSplit
import Solidity.Frontend.ExpressionUniqueness.SeparatorSplit
import Solidity.Frontend.ExpressionUniqueness.Statement
import Solidity.Frontend.ExpressionUniqueness.TokenSplit
import Solidity.Frontend.ExpressionUniqueness.YieldBalance
import Solidity.Frontend.ExpressionUniqueness.YieldShape

/-! Exact kernel-reported axiom pins for every source declaration in this lane. -/

/-- info: 'Solidity.Frontend.ExpressionUniqueness.BalancedAttrs' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.BalancedAttrs

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balancedAttrs_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balancedAttrs_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_single' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrange_nonModifier' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrange_nonModifier

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrange_balanced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrange_balanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.attrsP_balanced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.attrsP_balanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.run_of_skip' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.run_of_skip

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_balanced' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_balanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFreeItems_balanced' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFreeItems_balanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_atom' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_atom

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFreeItems_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFreeItems_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFreeItems_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFreeItems_cons

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFreeItems_single' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFreeItems_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFreeItems_dropHead' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFreeItems_dropHead

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFreeItems_flatten' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFreeItems_flatten

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_flatMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_flatMap

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_of_atoms' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_of_atoms

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_parens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_parens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_braces' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_braces

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_square' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_square

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_tk' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_tk

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_idt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_idt

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_path

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_elem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_elem

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_visibility' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_visibility

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_mutability' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_mutability

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_dataLoc' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_dataLoc

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_optToks' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_optToks

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_prefix' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_prefix

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_suffix' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_suffix

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_mul' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_mul

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_add' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_add

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_shift' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_shift

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_order' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_order

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_equality' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_equality

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_assign' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_assign

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fragsP_commaFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fragsP_commaFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.litP_commaFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.litP_commaFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.CommaFreeAttrs' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.CommaFreeAttrs

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFreeAttrs_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFreeAttrs_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_single' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrange_commaFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrange_commaFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.attrsP_commaFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.attrsP_commaFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.skip_of_run_forbidden_at_empty' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.skip_of_run_forbidden_at_empty

/-- info: 'Solidity.Frontend.ExpressionUniqueness.skip_close_of_balanced' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.skip_close_of_balanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.enclosed_payload_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.enclosed_payload_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.parens_prefix_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.parens_prefix_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expression_parens_prefix_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expression_parens_prefix_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.ExpressionCategory' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.ExpressionCategory

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_mapping_key' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_mapping_key

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expressionCategory_yield_balanced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expressionCategory_yield_balanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expr_yield_balanced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expr_yield_balanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.type_yield_balanced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.type_yield_balanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expr_derives_balanced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expr_derives_balanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expr_cannot_start_close' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expr_cannot_start_close

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expressionCategory_yield_commaFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expressionCategory_yield_commaFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expr_yield_commaFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expr_yield_commaFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expr_derives_commaFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expr_derives_commaFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.certified_expr_spans_commaSep_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.certified_expr_spans_commaSep_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.all_prec_root' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.all_prec_root

/-- info: 'Solidity.Frontend.ExpressionUniqueness.all_prec_implies_prec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.all_prec_implies_prec

/-- info: 'Solidity.Frontend.ExpressionUniqueness.LowYieldProperty' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.LowYieldProperty

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expression_low_property' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expression_low_property

/-- info: 'Solidity.Frontend.ExpressionUniqueness.high_expr_yield_lowFree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.high_expr_yield_lowFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.type_yield_lowFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.type_yield_lowFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.high_expr_derives_lowFree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.high_expr_derives_lowFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.negFamily' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.negFamily

/-- info: 'Solidity.Frontend.ExpressionUniqueness.negTokens' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.negTokens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.negFamily_prec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.negFamily_prec

/-- info: 'Solidity.Frontend.ExpressionUniqueness.prefix_yield' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.prefix_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.negFamily_yield' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.negFamily_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.negFamily_toks' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.negFamily_toks

/-- info: 'Solidity.Frontend.ExpressionUniqueness.negFamily_certified' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.negFamily_certified

/-- info: 'Solidity.Frontend.ExpressionUniqueness.negTokens_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.negTokens_length

/-- info: 'Solidity.Frontend.ExpressionUniqueness.negFamily_injective' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.negFamily_injective

/-- info: 'Solidity.Frontend.ExpressionUniqueness.group' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.group

/-- info: 'Solidity.Frontend.ExpressionUniqueness.group_prec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.group_prec

/-- info: 'Solidity.Frontend.ExpressionUniqueness.groupFamily' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.groupFamily

/-- info: 'Solidity.Frontend.ExpressionUniqueness.groupFamily_prec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.groupFamily_prec

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expressionError' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expressionError

/-- info: 'Solidity.Frontend.ExpressionUniqueness.refusalMessage' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.refusalMessage

/-- info: 'Solidity.Frontend.ExpressionUniqueness.prefix_postfix_fixture' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.prefix_postfix_fixture

/-- info: 'Solidity.Frontend.ExpressionUniqueness.conditional_assignment_fixture' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.conditional_assignment_fixture

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfix_member_fixture' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfix_member_fixture

/-- info: 'Solidity.Frontend.ExpressionUniqueness.double_postfix_fixture' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.double_postfix_fixture

/-- info: 'Solidity.Frontend.ExpressionUniqueness.grouped_disagreements_accepted' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.grouped_disagreements_accepted

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expressionCtor' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expressionCtor

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_index' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_index

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_slice' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_slice

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_member' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_member

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_callOptions' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_callOptions

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_call' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_call

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_payableConv' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_payableConv

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_metaType' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_metaType

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_unaryPrefix' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_unaryPrefix

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_unarySuffix' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_unarySuffix

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_exp' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_exp

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_mulDivMod' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_mulDivMod

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_addSub' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_addSub

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_shift' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_shift

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_bitAnd' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_bitAnd

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_bitXor' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_bitXor

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_bitOr' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_bitOr

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_order' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_order

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_equality' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_equality

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_and' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_and

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_or' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_or

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_cond' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_cond

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_assign' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_assign

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_new' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_new

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_tuple' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_tuple

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_inlineArray' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_inlineArray

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_ident' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_ident

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_lit' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_lit

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_litUnit' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_litUnit

/-- info: 'Solidity.Frontend.ExpressionUniqueness.constructor_elemType' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.constructor_elemType

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfix_index_fixture' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfix_index_fixture

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfix_slice_fixture' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfix_slice_fixture

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfix_options_fixture' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfix_options_fixture

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfix_call_fixture' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfix_call_fixture

/-- info: 'Solidity.Frontend.ExpressionUniqueness.chunks_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.chunks_spec

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fragsP_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fragsP_spec

/-- info: 'Solidity.Frontend.ExpressionUniqueness.stringPayload' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.stringPayload

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fragsP_reconstruct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fragsP_reconstruct

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fragsP_bytes_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fragsP_bytes_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.chunks_single' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.chunks_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fragsP_single' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fragsP_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fragsP_leading_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fragsP_leading_empty

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fragment_layouts_distinct' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fragment_layouts_distinct

/-- info: 'Solidity.Frontend.ExpressionUniqueness.group_yield_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.group_yield_map

/-- info: 'Solidity.Frontend.ExpressionUniqueness.group_toks_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.group_toks_iff

/-- info: 'Solidity.Frontend.ExpressionUniqueness.group_derives_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.group_derives_iff

/-- info: 'Solidity.Frontend.ExpressionUniqueness.group_prefix_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.group_prefix_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.parenTokens' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.parenTokens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.groupFamily_toks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.groupFamily_toks

/-- info: 'Solidity.Frontend.ExpressionUniqueness.groupFamily_certified' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.groupFamily_certified

/-- info: 'Solidity.Frontend.ExpressionUniqueness.parenTokens_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.parenTokens_length

/-- info: 'Solidity.Frontend.ExpressionUniqueness.parenTokens_depth_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.parenTokens_depth_injective

/-- info: 'Solidity.Frontend.ExpressionUniqueness.groupFamily_inhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.groupFamily_inhabited

/-- info: 'Solidity.Frontend.ExpressionUniqueness.groupFamily_certified_depth_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.groupFamily_certified_depth_injective

/-- info: 'Solidity.Frontend.ExpressionUniqueness.assignment_yield_join' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.assignment_yield_join

/-- info: 'Solidity.Frontend.ExpressionUniqueness.conditional_yield_join' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.conditional_yield_join

/-- info: 'Solidity.Frontend.ExpressionUniqueness.assignment_prec_join' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.assignment_prec_join

/-- info: 'Solidity.Frontend.ExpressionUniqueness.conditional_prec_join' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.conditional_prec_join

/-- info: 'Solidity.Frontend.ExpressionUniqueness.middleAssignment' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.middleAssignment

/-- info: 'Solidity.Frontend.ExpressionUniqueness.middleAssignmentTokens' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.middleAssignmentTokens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.middleAssignment_prec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.middleAssignment_prec

/-- info: 'Solidity.Frontend.ExpressionUniqueness.middleAssignment_yield' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.middleAssignment_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.middleAssignment_certified' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.middleAssignment_certified

/-- info: 'Solidity.Frontend.ExpressionUniqueness.middleAssignment_first_question' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.middleAssignment_first_question

/-- info: 'Solidity.Frontend.ExpressionUniqueness.middleAssignment_marker_not_assignment' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.middleAssignment_marker_not_assignment

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowMarker' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowMarker

/-- info: 'Solidity.Frontend.ExpressionUniqueness.LowFree' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.LowFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.LowFreeItems' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.LowFreeItems

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowMarker_atomic' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowMarker_atomic

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.assignment_lowMarker' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.assignment_lowMarker

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_balanced' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_balanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFreeItems_balanced' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFreeItems_balanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_atom' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_atom

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFreeItems_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFreeItems_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFreeItems_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFreeItems_cons

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFreeItems_single' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFreeItems_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFreeItems_dropHead' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFreeItems_dropHead

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFreeItems_flatten' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFreeItems_flatten

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_flatMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_flatMap

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_of_atoms' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_of_atoms

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_parens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_parens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_braces' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_braces

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_square' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_square

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_tk' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_tk

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_idt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_idt

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_path

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_elem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_elem

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_visibility' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_visibility

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_mutability' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_mutability

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_dataLoc' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_dataLoc

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_optToks' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_optToks

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_prefix' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_prefix

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_suffix' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_suffix

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_mul' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_mul

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_add' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_add

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_shift' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_shift

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_order' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_order

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_equality' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_equality

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fragsP_lowFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fragsP_lowFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.litP_lowFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.litP_lowFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.LowFreeAttrs' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.LowFreeAttrs

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFreeAttrs_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFreeAttrs_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lowFree_single' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lowFree_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrange_lowFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrange_lowFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.attrsP_lowFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.attrsP_lowFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.FirstLowIs' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.FirstLowIs

/-- info: 'Solidity.Frontend.ExpressionUniqueness.assignment_yield_firstLow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.assignment_yield_firstLow

/-- info: 'Solidity.Frontend.ExpressionUniqueness.conditional_yield_firstLow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.conditional_yield_firstLow

/-- info: 'Solidity.Frontend.ExpressionUniqueness.derives_firstLow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.derives_firstLow

/-- info: 'Solidity.Frontend.ExpressionUniqueness.assignment_derives_firstLow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.assignment_derives_firstLow

/-- info: 'Solidity.Frontend.ExpressionUniqueness.conditional_derives_firstLow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.conditional_derives_firstLow

/-- info: 'Solidity.Frontend.ExpressionUniqueness.assignment_conditional_disjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.assignment_conditional_disjoint

/-- info: 'Solidity.Frontend.ExpressionUniqueness.assignment_punct_injective' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.assignment_punct_injective

/-- info: 'Solidity.Frontend.ExpressionUniqueness.assignment_operator_reconstructed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.assignment_operator_reconstructed

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expr_level_below_two_cases' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expr_level_below_two_cases

/-- info: 'Solidity.Frontend.ExpressionUniqueness.certified_firstLow_none_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.certified_firstLow_none_iff

/-- info: 'Solidity.Frontend.ExpressionUniqueness.derives_pure_yield' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.derives_pure_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.derives_ident' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.derives_ident

/-- info: 'Solidity.Frontend.ExpressionUniqueness.derives_boolean' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.derives_boolean

/-- info: 'Solidity.Frontend.ExpressionUniqueness.derives_number' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.derives_number

/-- info: 'Solidity.Frontend.ExpressionUniqueness.derives_unit' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.derives_unit

/-- info: 'Solidity.Frontend.ExpressionUniqueness.derives_elementary' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.derives_elementary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.ident_same_yield' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.ident_same_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.boolean_same_yield' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.boolean_same_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.number_same_yield' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.number_same_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.derives_single_item' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.derives_single_item

/-- info: 'Solidity.Frontend.ExpressionUniqueness.str_yield_map' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.str_yield_map

/-- info: 'Solidity.Frontend.ExpressionUniqueness.str_payload' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.str_payload

/-- info: 'Solidity.Frontend.ExpressionUniqueness.str_same_yield' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.str_same_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.hexStr_yield_map' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.hexStr_yield_map

/-- info: 'Solidity.Frontend.ExpressionUniqueness.hexStr_payload' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.hexStr_payload

/-- info: 'Solidity.Frontend.ExpressionUniqueness.hexStr_same_yield' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.hexStr_same_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unicodeStr_yield_map' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unicodeStr_yield_map

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unicodeStr_payload' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unicodeStr_payload

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unicodeStr_same_yield' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unicodeStr_same_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.literalKind' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.literalKind

/-- info: 'Solidity.Frontend.ExpressionUniqueness.tokenLiteralKind' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.tokenLiteralKind

/-- info: 'Solidity.Frontend.ExpressionUniqueness.literal_head_kind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.literal_head_kind

/-- info: 'Solidity.Frontend.ExpressionUniqueness.literal_kind_determined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.literal_kind_determined

/-- info: 'Solidity.Frontend.ExpressionUniqueness.literal_same_yield' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.literal_same_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.refused_of_node_false' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.refused_of_node_false

/-- info: 'Solidity.Frontend.ExpressionUniqueness.prefix_suffix_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.prefix_suffix_refused

/-- info: 'Solidity.Frontend.ExpressionUniqueness.suffix_prefix_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.suffix_prefix_refused

/-- info: 'Solidity.Frontend.ExpressionUniqueness.conditional_assignment_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.conditional_assignment_refused

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfix_bases_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfix_bases_refused

/-- info: 'Solidity.Frontend.ExpressionUniqueness.new_bases_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.new_bases_refused

/-- info: 'Solidity.Frontend.ExpressionUniqueness.or_right_nested_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.or_right_nested_refused

/-- info: 'Solidity.Frontend.ExpressionUniqueness.and_right_nested_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.and_right_nested_refused

/-- info: 'Solidity.Frontend.ExpressionUniqueness.equality_right_nested_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.equality_right_nested_refused

/-- info: 'Solidity.Frontend.ExpressionUniqueness.order_right_nested_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.order_right_nested_refused

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bitOr_right_nested_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bitOr_right_nested_refused

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bitXor_right_nested_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bitXor_right_nested_refused

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bitAnd_right_nested_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bitAnd_right_nested_refused

/-- info: 'Solidity.Frontend.ExpressionUniqueness.shift_right_nested_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.shift_right_nested_refused

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addSub_right_nested_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addSub_right_nested_refused

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mulDivMod_right_nested_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mulDivMod_right_nested_refused

/-- info: 'Solidity.Frontend.ExpressionUniqueness.exp_left_nested_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.exp_left_nested_refused

/-- info: 'Solidity.Frontend.ExpressionUniqueness.conditional_left_nested_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.conditional_left_nested_refused

/-- info: 'Solidity.Frontend.ExpressionUniqueness.assignment_left_nested_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.assignment_left_nested_refused

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mirrorTok' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mirrorTok

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mirrorWord' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mirrorWord

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bracket_open' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bracket_open

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bracket_close' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bracket_close

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mirrorTok_open' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mirrorTok_open

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mirrorTok_close' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mirrorTok_close

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mirrorTok_involutive' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mirrorTok_involutive

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mirrorWord_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mirrorWord_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mirrorWord_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mirrorWord_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mirrorWord_singleton' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mirrorWord_singleton

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mirrorWord_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mirrorWord_cons

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mirrorWord_involutive' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mirrorWord_involutive

/-- info: 'Solidity.Frontend.ExpressionUniqueness.step_reverse' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.step_reverse

/-- info: 'Solidity.Frontend.ExpressionUniqueness.run_reverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.run_reverse

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_mirror' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_mirror

/-- info: 'Solidity.Frontend.ExpressionUniqueness.AtomicSelector' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.AtomicSelector

/-- info: 'Solidity.Frontend.ExpressionUniqueness.atomicSelector_mirror' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.atomicSelector_mirror

/-- info: 'Solidity.Frontend.ExpressionUniqueness.reverse_step_not_hit' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.reverse_step_not_hit

/-- info: 'Solidity.Frontend.ExpressionUniqueness.skip_reverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.skip_reverse

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mirrorWord_injective' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mirrorWord_injective

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lastTop_cut_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lastTop_cut_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lastTop' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lastTop

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lastTop_marker' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lastTop_marker

/-- info: 'Solidity.Frontend.ExpressionUniqueness.skip_nested' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.skip_nested

/-- info: 'Solidity.Frontend.ExpressionUniqueness.nested_last_marker_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.nested_last_marker_control

/-- info: 'Solidity.Frontend.ExpressionUniqueness.isAddMarker' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.isAddMarker

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addMarker_atomic' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addMarker_atomic

/-- info: 'Solidity.Frontend.ExpressionUniqueness.repeated_add_balanced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.repeated_add_balanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.nested_add_markers_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.nested_add_markers_control

/-- info: 'Solidity.Frontend.ExpressionUniqueness.malformed_reverse_scan_control' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.malformed_reverse_scan_control

/-- info: 'Solidity.Frontend.ExpressionUniqueness.isComma' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.isComma

/-- info: 'Solidity.Frontend.ExpressionUniqueness.CommaFree' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.CommaFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.CommaFreeItems' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.CommaFreeItems

/-- info: 'Solidity.Frontend.ExpressionUniqueness.firstTop_none_of_skip' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.firstTop_none_of_skip

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFreeItems_tail' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFreeItems_tail

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaSep_single' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaSep_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaSep_cons_cons' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaSep_cons_cons

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaFree_not_marker_word' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaFree_not_marker_word

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaSep_nonempty_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaSep_nonempty_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaSep_empty_single_empty' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaSep_empty_single_empty

/-- info: 'Solidity.Frontend.ExpressionUniqueness.empty_holes_comma_free' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.empty_holes_comma_free

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arbitrary_holes_reconstructed' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arbitrary_holes_reconstructed

/-- info: 'Solidity.Frontend.ExpressionUniqueness.CertifiedYieldUnique' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.CertifiedYieldUnique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.Bracket' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.Bracket

/-- info: 'Solidity.Frontend.ExpressionUniqueness.openTok' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.openTok

/-- info: 'Solidity.Frontend.ExpressionUniqueness.closeTok' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.closeTok

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bracket' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bracket

/-- info: 'Solidity.Frontend.ExpressionUniqueness.pop' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.pop

/-- info: 'Solidity.Frontend.ExpressionUniqueness.step' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.step

/-- info: 'Solidity.Frontend.ExpressionUniqueness.run' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.run

/-- info: 'Solidity.Frontend.ExpressionUniqueness.Balanced' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.Balanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.open_close_disjoint' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.open_close_disjoint

/-- info: 'Solidity.Frontend.ExpressionUniqueness.step_suffix' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.step_suffix

/-- info: 'Solidity.Frontend.ExpressionUniqueness.run_suffix' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.run_suffix

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_iff_empty' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_iff_empty

/-- info: 'Solidity.Frontend.ExpressionUniqueness.run_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.run_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_atom' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_atom

/-- info: 'Solidity.Frontend.ExpressionUniqueness.step_open' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.step_open

/-- info: 'Solidity.Frontend.ExpressionUniqueness.step_close' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.step_close

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_enclose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_enclose

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_not_close' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_not_close

/-- info: 'Solidity.Frontend.ExpressionUniqueness.skip' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.skip

/-- info: 'Solidity.Frontend.ExpressionUniqueness.offset' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.offset

/-- info: 'Solidity.Frontend.ExpressionUniqueness.firstTop' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.firstTop

/-- info: 'Solidity.Frontend.ExpressionUniqueness.skip_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.skip_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.skip_inside' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.skip_inside

/-- info: 'Solidity.Frontend.ExpressionUniqueness.skip_enclose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.skip_enclose

/-- info: 'Solidity.Frontend.ExpressionUniqueness.nest' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.nest

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_nest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_nest

/-- info: 'Solidity.Frontend.ExpressionUniqueness.firstTop_append_of_skip' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.firstTop_append_of_skip

/-- info: 'Solidity.Frontend.ExpressionUniqueness.firstTop_marker' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.firstTop_marker

/-- info: 'Solidity.Frontend.ExpressionUniqueness.firstTop_cut_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.firstTop_cut_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.BalancedItems' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.BalancedItems

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balancedItems_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balancedItems_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balancedItems_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balancedItems_cons

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balancedItems_single' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balancedItems_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balancedItems_tail' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balancedItems_tail

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balancedItems_flatten' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balancedItems_flatten

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_flatMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_flatMap

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_of_atoms' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_of_atoms

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_commaSep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_commaSep

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_parens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_parens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_braces' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_braces

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_square' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_square

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_tk' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_tk

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_idt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_idt

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_path

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_elem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_elem

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_visibility' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_visibility

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_mutability' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_mutability

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_dataLoc' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_dataLoc

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_optToks' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_optToks

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_prefix' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_prefix

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_suffix' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_suffix

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_mul' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_mul

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_add' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_add

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_shift' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_shift

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_order' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_order

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_equality' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_equality

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_assign' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_assign

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fragsP_balanced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fragsP_balanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.litP_balanced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.litP_balanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.Produces' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.Produces

/-- info: 'Solidity.Frontend.ExpressionUniqueness.produces_pure' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.produces_pure

/-- info: 'Solidity.Frontend.ExpressionUniqueness.produces_bind_all' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.produces_bind_all

/-- info: 'Solidity.Frontend.ExpressionUniqueness.produces_bind' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.produces_bind

/-- info: 'Solidity.Frontend.ExpressionUniqueness.SingleItem' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.SingleItem

/-- info: 'Solidity.Frontend.ExpressionUniqueness.NonemptyItem' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.NonemptyItem

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expr_yield_single' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expr_yield_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.litP_nonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.litP_nonempty

/-- info: 'Solidity.Frontend.ExpressionUniqueness.callArgs_yield_nonempty' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.callArgs_yield_nonempty

/-- info: 'Solidity.Frontend.ExpressionUniqueness.nonemptyItem_flatten' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.nonemptyItem_flatten

/-- info: 'Solidity.Frontend.ExpressionUniqueness.append_nonempty_left' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.append_nonempty_left

/-- info: 'Solidity.Frontend.ExpressionUniqueness.append_nonempty_right' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.append_nonempty_right

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expr_yield_nonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expr_yield_nonempty

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expr_toks_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expr_toks_iff

/-- info: 'Solidity.Frontend.ExpressionUniqueness.derives_nonempty_of_produces' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.derives_nonempty_of_produces

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expr_derives_nonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expr_derives_nonempty

/-- info: 'Solidity.Frontend.ExpressionUniqueness.some_expr_yield_nonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.some_expr_yield_nonempty

/-- info: 'Solidity.Frontend.ExpressionUniqueness.optional_expr_empty_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.optional_expr_empty_iff

/-- info: 'Solidity.Frontend.ExpressionUniqueness.some_expr_yield_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.some_expr_yield_eq

/-- info: 'Solidity.Frontend.ExpressionUniqueness.optional_expr_yield_empty_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.optional_expr_yield_empty_iff

/-- info: 'Solidity.Frontend.ExpressionUniqueness.optional_presence_reconstructed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.optional_presence_reconstructed
