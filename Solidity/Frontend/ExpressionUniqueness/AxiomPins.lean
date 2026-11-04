import Solidity.Frontend.ExpressionUniqueness.Families
import Solidity.Frontend.ExpressionUniqueness.Fixtures
import Solidity.Frontend.ExpressionUniqueness.Fragments
import Solidity.Frontend.ExpressionUniqueness.Primary
import Solidity.Frontend.ExpressionUniqueness.Refusals
import Solidity.Frontend.ExpressionUniqueness.Statement
import Solidity.Frontend.ExpressionUniqueness.TokenSplit

/-! Exact kernel-reported axiom pins for every source declaration in this lane. -/

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
