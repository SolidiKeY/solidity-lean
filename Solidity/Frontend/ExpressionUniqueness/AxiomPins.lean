import Solidity.Frontend.ExpressionUniqueness.Accepted
import Solidity.Frontend.ExpressionUniqueness.AddControls
import Solidity.Frontend.ExpressionUniqueness.AddFreeAlgebra
import Solidity.Frontend.ExpressionUniqueness.AddRoot
import Solidity.Frontend.ExpressionUniqueness.AddScan
import Solidity.Frontend.ExpressionUniqueness.AllRootLevels
import Solidity.Frontend.ExpressionUniqueness.ArgumentIdentity
import Solidity.Frontend.ExpressionUniqueness.ArgumentSpans
import Solidity.Frontend.ExpressionUniqueness.ArgumentWords
import Solidity.Frontend.ExpressionUniqueness.AttributeBalance
import Solidity.Frontend.ExpressionUniqueness.AttributeFieldIdentity
import Solidity.Frontend.ExpressionUniqueness.AttributeOrderIdentity
import Solidity.Frontend.ExpressionUniqueness.AttributeTokens
import Solidity.Frontend.ExpressionUniqueness.BinaryControls
import Solidity.Frontend.ExpressionUniqueness.BinaryFreeAlgebra
import Solidity.Frontend.ExpressionUniqueness.BinaryIdentity
import Solidity.Frontend.ExpressionUniqueness.BinaryRank
import Solidity.Frontend.ExpressionUniqueness.BinaryRoot
import Solidity.Frontend.ExpressionUniqueness.BinarySpans
import Solidity.Frontend.ExpressionUniqueness.BoundaryIdentity
import Solidity.Frontend.ExpressionUniqueness.Certified
import Solidity.Frontend.ExpressionUniqueness.CertifiedControls
import Solidity.Frontend.ExpressionUniqueness.CommaFreeAlgebra
import Solidity.Frontend.ExpressionUniqueness.ConditionalAlgebra
import Solidity.Frontend.ExpressionUniqueness.ConditionalBalance
import Solidity.Frontend.ExpressionUniqueness.ConditionalControls
import Solidity.Frontend.ExpressionUniqueness.ConditionalSpans
import Solidity.Frontend.ExpressionUniqueness.ContainerControls
import Solidity.Frontend.ExpressionUniqueness.ContainerIdentity
import Solidity.Frontend.ExpressionUniqueness.DelimiterReconstruction
import Solidity.Frontend.ExpressionUniqueness.ElementaryPathPrefix
import Solidity.Frontend.ExpressionUniqueness.ExpressionAddFree
import Solidity.Frontend.ExpressionUniqueness.ExpressionBalance
import Solidity.Frontend.ExpressionUniqueness.ExpressionBinaryFree
import Solidity.Frontend.ExpressionUniqueness.ExpressionCommaFree
import Solidity.Frontend.ExpressionUniqueness.ExpressionConditional
import Solidity.Frontend.ExpressionUniqueness.ExpressionLowFree
import Solidity.Frontend.ExpressionUniqueness.ExpressionMode
import Solidity.Frontend.ExpressionUniqueness.ExpressionStart
import Solidity.Frontend.ExpressionUniqueness.ExpressionUnaryFree
import Solidity.Frontend.ExpressionUniqueness.Families
import Solidity.Frontend.ExpressionUniqueness.Fixtures
import Solidity.Frontend.ExpressionUniqueness.FnTypePrefix
import Solidity.Frontend.ExpressionUniqueness.Fragments
import Solidity.Frontend.ExpressionUniqueness.FunctionTypeIdentity
import Solidity.Frontend.ExpressionUniqueness.Grouping
import Solidity.Frontend.ExpressionUniqueness.LastEnclosure
import Solidity.Frontend.ExpressionUniqueness.LayoutBoundary
import Solidity.Frontend.ExpressionUniqueness.LiteralPrefix
import Solidity.Frontend.ExpressionUniqueness.LowControls
import Solidity.Frontend.ExpressionUniqueness.LowFreeAlgebra
import Solidity.Frontend.ExpressionUniqueness.LowRoot
import Solidity.Frontend.ExpressionUniqueness.MappingIdentity
import Solidity.Frontend.ExpressionUniqueness.MappingKeyIdentity
import Solidity.Frontend.ExpressionUniqueness.MemberSpans
import Solidity.Frontend.ExpressionUniqueness.OperandMode
import Solidity.Frontend.ExpressionUniqueness.OperandModeAlgebra
import Solidity.Frontend.ExpressionUniqueness.ParameterIdentity
import Solidity.Frontend.ExpressionUniqueness.ParameterWords
import Solidity.Frontend.ExpressionUniqueness.PostfixControls
import Solidity.Frontend.ExpressionUniqueness.PostfixFollowers
import Solidity.Frontend.ExpressionUniqueness.PostfixIdentity
import Solidity.Frontend.ExpressionUniqueness.PostfixRootKind
import Solidity.Frontend.ExpressionUniqueness.PostfixSpans
import Solidity.Frontend.ExpressionUniqueness.PostfixYieldSplit
import Solidity.Frontend.ExpressionUniqueness.Primary
import Solidity.Frontend.ExpressionUniqueness.PrimaryChildIdentity
import Solidity.Frontend.ExpressionUniqueness.PrimaryLeafIdentity
import Solidity.Frontend.ExpressionUniqueness.PrimaryPrefix
import Solidity.Frontend.ExpressionUniqueness.PrimaryPrefixParts
import Solidity.Frontend.ExpressionUniqueness.PrimarySpine
import Solidity.Frontend.ExpressionUniqueness.PrimaryStart
import Solidity.Frontend.ExpressionUniqueness.PrimaryYieldSplit
import Solidity.Frontend.ExpressionUniqueness.RecursiveProperty
import Solidity.Frontend.ExpressionUniqueness.Refusals
import Solidity.Frontend.ExpressionUniqueness.ReverseSplit
import Solidity.Frontend.ExpressionUniqueness.RootLevelControls
import Solidity.Frontend.ExpressionUniqueness.RootLevels
import Solidity.Frontend.ExpressionUniqueness.SeparatorSplit
import Solidity.Frontend.ExpressionUniqueness.SpanControls
import Solidity.Frontend.ExpressionUniqueness.StartAlgebra
import Solidity.Frontend.ExpressionUniqueness.Statement
import Solidity.Frontend.ExpressionUniqueness.TokenSplit
import Solidity.Frontend.ExpressionUniqueness.TypeArrayIdentity
import Solidity.Frontend.ExpressionUniqueness.TypeAtomPrefix
import Solidity.Frontend.ExpressionUniqueness.TypeAtomStart
import Solidity.Frontend.ExpressionUniqueness.TypeIdentityControls
import Solidity.Frontend.ExpressionUniqueness.TypeLeafIdentity
import Solidity.Frontend.ExpressionUniqueness.TypePrefix
import Solidity.Frontend.ExpressionUniqueness.TypePrefixAlgebra
import Solidity.Frontend.ExpressionUniqueness.TypePrefixControls
import Solidity.Frontend.ExpressionUniqueness.TypeSpine
import Solidity.Frontend.ExpressionUniqueness.TypeYieldSplit
import Solidity.Frontend.ExpressionUniqueness.UnaryControls
import Solidity.Frontend.ExpressionUniqueness.UnaryFreeAlgebra
import Solidity.Frontend.ExpressionUniqueness.UnaryRoot
import Solidity.Frontend.ExpressionUniqueness.YieldBalance
import Solidity.Frontend.ExpressionUniqueness.YieldShape
import Solidity.Frontend.ExpressionUniqueness.YieldSplit

/-! Exact kernel-reported axiom pins for every source declaration in this lane. -/

/-- info: 'Solidity.Frontend.ExpressionUniqueness.parseCat_expression_accepted_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.parseCat_expression_accepted_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.parseCat_expression_same_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.parseCat_expression_same_source

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arbitrary_prefix_addFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arbitrary_prefix_addFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arbitrary_prefix_lastAdd_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arbitrary_prefix_lastAdd_none

/-- info: 'Solidity.Frontend.ExpressionUniqueness.finished_prefix_is_selected' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.finished_prefix_is_selected

/-- info: 'Solidity.Frontend.ExpressionUniqueness.add_prec_join' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.add_prec_join

/-- info: 'Solidity.Frontend.ExpressionUniqueness.add_yield_join' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.add_yield_join

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mixedAddPrefix' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mixedAddPrefix

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mixedAddPrefixTokens' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mixedAddPrefixTokens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mixedAddPrefix_prec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mixedAddPrefix_prec

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mixedAddPrefix_yield' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mixedAddPrefix_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mixedAddPrefix_certified' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mixedAddPrefix_certified

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mixedAddPrefix_outer_marker' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mixedAddPrefix_outer_marker

/-- info: 'Solidity.Frontend.ExpressionUniqueness.AddFree' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.AddFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.AddStable' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.AddStable

/-- info: 'Solidity.Frontend.ExpressionUniqueness.AddPrefix' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.AddPrefix

/-- info: 'Solidity.Frontend.ExpressionUniqueness.AddReset' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.AddReset

/-- info: 'Solidity.Frontend.ExpressionUniqueness.AddDone' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.AddDone

/-- info: 'Solidity.Frontend.ExpressionUniqueness.AddStableItems' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.AddStableItems

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addDone_free' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addDone_free

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addDone_stable' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addDone_stable

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addStable_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addStable_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addStableItems_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addStableItems_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addStableItems_tail' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addStableItems_tail

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addStable_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addStable_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addDone_stable_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addDone_stable_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addFree_stable_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addFree_stable_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addPrefix_free_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addPrefix_free_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addReset_free_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addReset_free_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addFree_binary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addFree_binary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addStable_atom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addStable_atom

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addDone_atom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addDone_atom

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addDone_parens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addDone_parens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addDone_braces' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addDone_braces

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addDone_square' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addDone_square

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addStable_flatMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addStable_flatMap

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addStable_of_atoms' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addStable_of_atoms

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addDone_map_nonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addDone_map_nonempty

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addDone_idt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addDone_idt

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addReset_period' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addReset_period

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addDone_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addDone_path

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addDone_elem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addDone_elem

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addStable_visibility' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addStable_visibility

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addStable_mutability' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addStable_mutability

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addStable_optToks' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addStable_optToks

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addPrefix_prefix' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addPrefix_prefix

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addStable_suffix' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addStable_suffix

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addReset_mul' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addReset_mul

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addReset_exp' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addReset_exp

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addPrefix_new' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addPrefix_new

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fragsP_addDone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fragsP_addDone

/-- info: 'Solidity.Frontend.ExpressionUniqueness.litP_addDone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.litP_addDone

/-- info: 'Solidity.Frontend.ExpressionUniqueness.AddStableAttrs' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.AddStableAttrs

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addStableAttrs_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addStableAttrs_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addStable_single' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addStable_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrange_addStable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrange_addStable

/-- info: 'Solidity.Frontend.ExpressionUniqueness.attrsP_addStable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.attrsP_addStable

/-- info: 'Solidity.Frontend.ExpressionUniqueness.LastAddIs' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.LastAddIs

/-- info: 'Solidity.Frontend.ExpressionUniqueness.add_yield_lastAdd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.add_yield_lastAdd

/-- info: 'Solidity.Frontend.ExpressionUniqueness.derives_lastAdd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.derives_lastAdd

/-- info: 'Solidity.Frontend.ExpressionUniqueness.add_derives_lastAdd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.add_derives_lastAdd

/-- info: 'Solidity.Frontend.ExpressionUniqueness.add_punct_injective' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.add_punct_injective

/-- info: 'Solidity.Frontend.ExpressionUniqueness.add_operator_reconstructed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.add_operator_reconstructed

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expr_level_ten_cases' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expr_level_ten_cases

/-- info: 'Solidity.Frontend.ExpressionUniqueness.add_higher_root_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.add_higher_root_disjoint

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binary_higher_root_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binary_higher_root_disjoint

/-- info: 'Solidity.Frontend.ExpressionUniqueness.certified_binary_root_levels_equal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.certified_binary_root_levels_equal

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addHit' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addHit

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addSkip' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addSkip

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addScan' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addScan

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lastAdd' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lastAdd

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addHit_inside' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addHit_inside

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addHit_open' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addHit_open

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addSkip_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addSkip_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addSkip_atom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addSkip_atom

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addSkip_context' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addSkip_context

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addSkip_enclose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addSkip_enclose

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeRun_of_addSkip' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeRun_of_addSkip

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addScan_of_addSkip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addScan_of_addSkip

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addScan_suffix_found' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addScan_suffix_found

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lastAdd_marker' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lastAdd_marker

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lastAdd_none_of_skip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lastAdd_none_of_skip

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lastAdd_cut_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lastAdd_cut_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expression_level_bound' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expression_level_bound

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfix_primary_yield_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfix_primary_yield_disjoint

/-- info: 'Solidity.Frontend.ExpressionUniqueness.partial_root_levels_equal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.partial_root_levels_equal

/-- info: 'Solidity.Frontend.ExpressionUniqueness.certified_root_levels_equal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.certified_root_levels_equal

/-- info: 'Solidity.Frontend.ExpressionUniqueness.namedArg_prec_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.namedArg_prec_child

/-- info: 'Solidity.Frontend.ExpressionUniqueness.positional_prec_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.positional_prec_child

/-- info: 'Solidity.Frontend.ExpressionUniqueness.named_prec_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.named_prec_child

/-- info: 'Solidity.Frontend.ExpressionUniqueness.namedArg_word_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.namedArg_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.positional_word_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.positional_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.named_word_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.named_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.positional_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.positional_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.named_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.named_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.ArgumentVectorSpans' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.ArgumentVectorSpans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.positional_argument_spans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.positional_argument_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.named_argument_spans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.named_argument_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.positional_named_yields_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.positional_named_yields_disjoint

/-- info: 'Solidity.Frontend.ExpressionUniqueness.NonemptyWords' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.NonemptyWords

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_commaSep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_commaSep

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaSep_nonempty_word_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaSep_nonempty_word_head

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaSep_unique_nonempty_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaSep_unique_nonempty_words

/-- info: 'Solidity.Frontend.ExpressionUniqueness.namedArg_yield_nonemptyWord' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.namedArg_yield_nonemptyWord

/-- info: 'Solidity.Frontend.ExpressionUniqueness.ArgumentVectorProperty' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.ArgumentVectorProperty

/-- info: 'Solidity.Frontend.ExpressionUniqueness.argument_vector_property' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.argument_vector_property

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expressionList_yield_nonemptyWords' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expressionList_yield_nonemptyWords

/-- info: 'Solidity.Frontend.ExpressionUniqueness.namedArgList_yield_nonemptyWords' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.namedArgList_yield_nonemptyWords

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

/-- info: 'Solidity.Frontend.ExpressionUniqueness.visibilityToken' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.visibilityToken

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mutabilityToken' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mutabilityToken

/-- info: 'Solidity.Frontend.ExpressionUniqueness.single_visibility' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.single_visibility

/-- info: 'Solidity.Frontend.ExpressionUniqueness.single_mutability' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.single_mutability

/-- info: 'Solidity.Frontend.ExpressionUniqueness.type_attributes_word_shape' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.type_attributes_word_shape

/-- info: 'Solidity.Frontend.ExpressionUniqueness.attrsP_arrange_success' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.attrsP_arrange_success

/-- info: 'Solidity.Frontend.ExpressionUniqueness.visibility_optional_filter' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.visibility_optional_filter

/-- info: 'Solidity.Frontend.ExpressionUniqueness.visibility_optional_skip_mu' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.visibility_optional_skip_mu

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mutability_optional_filter' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mutability_optional_filter

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mutability_optional_skip_vis' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mutability_optional_skip_vis

/-- info: 'Solidity.Frontend.ExpressionUniqueness.type_attributes_filter_fields' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.type_attributes_filter_fields

/-- info: 'Solidity.Frontend.ExpressionUniqueness.optional_visibility_tokens_injective' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.optional_visibility_tokens_injective

/-- info: 'Solidity.Frontend.ExpressionUniqueness.optional_mutability_tokens_injective' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.optional_mutability_tokens_injective

/-- info: 'Solidity.Frontend.ExpressionUniqueness.type_attributes_fields_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.type_attributes_fields_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.map_append_success' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.map_append_success

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrange_empty_success' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrange_empty_success

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrange_vis_success' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrange_vis_success

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrange_mutab_success' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrange_mutab_success

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrange_vis_mutab_success' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrange_vis_mutab_success

/-- info: 'Solidity.Frontend.ExpressionUniqueness.TokenItems' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.TokenItems

/-- info: 'Solidity.Frontend.ExpressionUniqueness.TokenAttrs' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.TokenAttrs

/-- info: 'Solidity.Frontend.ExpressionUniqueness.allTokens_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.allTokens_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.allTokens_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.allTokens_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.tokenItems_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.tokenItems_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.tokenAttrs_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.tokenAttrs_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.tokenAttrs_single' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.tokenAttrs_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrange_allTokens' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrange_allTokens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.attrsP_allTokens' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.attrsP_allTokens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.allTokens_visibility' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.allTokens_visibility

/-- info: 'Solidity.Frontend.ExpressionUniqueness.allTokens_mutability' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.allTokens_mutability

/-- info: 'Solidity.Frontend.ExpressionUniqueness.allTokens_optToks' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.allTokens_optToks

/-- info: 'Solidity.Frontend.ExpressionUniqueness.attrsP_typeAttributes' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.attrsP_typeAttributes

/-- info: 'Solidity.Frontend.ExpressionUniqueness.successor_prefix_not_binary_ten_free' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.successor_prefix_not_binary_ten_free

/-- info: 'Solidity.Frontend.ExpressionUniqueness.rank_ten_prefix_countercontrol' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.rank_ten_prefix_countercontrol

/-- info: 'Solidity.Frontend.ExpressionUniqueness.grouped_prefix_binary_ten_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.grouped_prefix_binary_ten_free

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryMarker' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryMarker

/-- info: 'Solidity.Frontend.ExpressionUniqueness.BinaryFree' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.BinaryFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.BinaryFreeItems' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.BinaryFreeItems

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryMarker_atomic' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryMarker_atomic

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_balanced' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_balanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFreeItems_balanced' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFreeItems_balanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_atom' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_atom

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFreeItems_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFreeItems_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFreeItems_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFreeItems_cons

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFreeItems_single' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFreeItems_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFreeItems_dropHead' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFreeItems_dropHead

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFreeItems_flatten' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFreeItems_flatten

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_flatMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_flatMap

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_of_atoms' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_of_atoms

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_parens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_parens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_braces' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_braces

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_square' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_square

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_tk' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_tk

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_idt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_idt

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_path

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_elem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_elem

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_visibility' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_visibility

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_mutability' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_mutability

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_dataLoc' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_dataLoc

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_optToks' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_optToks

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_prefix' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_prefix

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_suffix' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_suffix

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_mul' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_mul

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_add' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_add

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_shift' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_shift

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_order' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_order

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_equality' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_equality

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fragsP_binaryFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fragsP_binaryFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.litP_binaryFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.litP_binaryFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.BinaryFreeAttrs' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.BinaryFreeAttrs

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFreeAttrs_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFreeAttrs_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.binaryFree_single' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.binaryFree_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrange_binaryFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrange_binaryFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.attrsP_binaryFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.attrsP_binaryFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.exp_prec_children' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.exp_prec_children

/-- info: 'Solidity.Frontend.ExpressionUniqueness.exp_word_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.exp_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mulDivMod_prec_children' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mulDivMod_prec_children

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mulDivMod_word_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mulDivMod_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addSub_prec_children' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addSub_prec_children

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addSub_word_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addSub_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.shift_prec_children' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.shift_prec_children

/-- info: 'Solidity.Frontend.ExpressionUniqueness.shift_word_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.shift_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bitAnd_prec_children' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bitAnd_prec_children

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bitAnd_word_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bitAnd_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bitXor_prec_children' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bitXor_prec_children

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bitXor_word_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bitXor_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bitOr_prec_children' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bitOr_prec_children

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bitOr_word_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bitOr_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.order_prec_children' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.order_prec_children

/-- info: 'Solidity.Frontend.ExpressionUniqueness.order_word_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.order_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.equality_prec_children' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.equality_prec_children

/-- info: 'Solidity.Frontend.ExpressionUniqueness.equality_word_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.equality_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.and_prec_children' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.and_prec_children

/-- info: 'Solidity.Frontend.ExpressionUniqueness.and_word_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.and_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.or_prec_children' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.or_prec_children

/-- info: 'Solidity.Frontend.ExpressionUniqueness.or_word_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.or_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.assign_prec_children' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.assign_prec_children

/-- info: 'Solidity.Frontend.ExpressionUniqueness.assign_word_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.assign_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.certified_left_binary_marker' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.certified_left_binary_marker

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expr_level_twelve_cases' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expr_level_twelve_cases

/-- info: 'Solidity.Frontend.ExpressionUniqueness.certified_exp_marker' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.certified_exp_marker

/-- info: 'Solidity.Frontend.ExpressionUniqueness.left_binary_higher_root_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.left_binary_higher_root_disjoint

/-- info: 'Solidity.Frontend.ExpressionUniqueness.exp_higher_root_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.exp_higher_root_disjoint

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mul_punct_injective' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mul_punct_injective

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mul_operator_reconstructed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mul_operator_reconstructed

/-- info: 'Solidity.Frontend.ExpressionUniqueness.shift_punct_injective' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.shift_punct_injective

/-- info: 'Solidity.Frontend.ExpressionUniqueness.shift_operator_reconstructed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.shift_operator_reconstructed

/-- info: 'Solidity.Frontend.ExpressionUniqueness.order_punct_injective' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.order_punct_injective

/-- info: 'Solidity.Frontend.ExpressionUniqueness.order_operator_reconstructed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.order_operator_reconstructed

/-- info: 'Solidity.Frontend.ExpressionUniqueness.equality_punct_injective' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.equality_punct_injective

/-- info: 'Solidity.Frontend.ExpressionUniqueness.equality_operator_reconstructed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.equality_operator_reconstructed

/-- info: 'Solidity.Frontend.ExpressionUniqueness.LastBinaryIs' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.LastBinaryIs

/-- info: 'Solidity.Frontend.ExpressionUniqueness.FirstBinaryIs' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.FirstBinaryIs

/-- info: 'Solidity.Frontend.ExpressionUniqueness.derives_lastBinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.derives_lastBinary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.derives_firstBinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.derives_firstBinary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mul_yield_lastBinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mul_yield_lastBinary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mul_derives_lastBinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mul_derives_lastBinary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.shift_yield_lastBinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.shift_yield_lastBinary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.shift_derives_lastBinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.shift_derives_lastBinary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.order_yield_lastBinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.order_yield_lastBinary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.order_derives_lastBinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.order_derives_lastBinary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.equality_yield_lastBinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.equality_yield_lastBinary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.equality_derives_lastBinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.equality_derives_lastBinary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bitAnd_yield_lastBinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bitAnd_yield_lastBinary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bitAnd_derives_lastBinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bitAnd_derives_lastBinary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bitXor_yield_lastBinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bitXor_yield_lastBinary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bitXor_derives_lastBinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bitXor_derives_lastBinary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bitOr_yield_lastBinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bitOr_yield_lastBinary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bitOr_derives_lastBinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bitOr_derives_lastBinary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.and_yield_lastBinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.and_yield_lastBinary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.and_derives_lastBinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.and_derives_lastBinary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.or_yield_lastBinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.or_yield_lastBinary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.or_derives_lastBinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.or_derives_lastBinary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.exp_yield_firstBinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.exp_yield_firstBinary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.exp_derives_firstBinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.exp_derives_firstBinary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.lastTop_none_of_binaryFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.lastTop_none_of_binaryFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.BinaryChildSpans' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.BinaryChildSpans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mul_child_spans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mul_child_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.shift_child_spans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.shift_child_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.order_child_spans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.order_child_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.equality_child_spans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.equality_child_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bitAnd_child_spans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bitAnd_child_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bitXor_child_spans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bitXor_child_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bitOr_child_spans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bitOr_child_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.and_child_spans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.and_child_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.or_child_spans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.or_child_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.add_child_spans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.add_child_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.exp_child_spans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.exp_child_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.assignment_child_spans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.assignment_child_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryPrefix_prec_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryPrefix_prec_child

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryPrefix_word_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryPrefix_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unarySuffix_prec_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unarySuffix_prec_child

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unarySuffix_word_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unarySuffix_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.cond_prec_children' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.cond_prec_children

/-- info: 'Solidity.Frontend.ExpressionUniqueness.cond_word_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.cond_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.recursive_yield_property' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.recursive_yield_property

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expression_yield_word_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expression_yield_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.type_yield_word_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.type_yield_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.parameter_yield_word_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.parameter_yield_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.argument_yield_word_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.argument_yield_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.namedArg_yield_word_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.namedArg_yield_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.optional_expression_yield_word_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.optional_expression_yield_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.certified_expression_yield_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.certified_expression_yield_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.certifiedYieldUnique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.certifiedYieldUnique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.typedParameter' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.typedParameter

/-- info: 'Solidity.Frontend.ExpressionUniqueness.typedParameterWord' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.typedParameterWord

/-- info: 'Solidity.Frontend.ExpressionUniqueness.typedParameter_prec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.typedParameter_prec

/-- info: 'Solidity.Frontend.ExpressionUniqueness.typedParameter_yield' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.typedParameter_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.typedParameters' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.typedParameters

/-- info: 'Solidity.Frontend.ExpressionUniqueness.typedParameters_prec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.typedParameters_prec

/-- info: 'Solidity.Frontend.ExpressionUniqueness.typedParameters_yield' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.typedParameters_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.functionReturns' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.functionReturns

/-- info: 'Solidity.Frontend.ExpressionUniqueness.functionReturnWords' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.functionReturnWords

/-- info: 'Solidity.Frontend.ExpressionUniqueness.functionReturns_prec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.functionReturns_prec

/-- info: 'Solidity.Frontend.ExpressionUniqueness.functionReturns_yield' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.functionReturns_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.functionOrder' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.functionOrder

/-- info: 'Solidity.Frontend.ExpressionUniqueness.functionAttrs' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.functionAttrs

/-- info: 'Solidity.Frontend.ExpressionUniqueness.functionTypeFamily' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.functionTypeFamily

/-- info: 'Solidity.Frontend.ExpressionUniqueness.functionTypeWord' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.functionTypeWord

/-- info: 'Solidity.Frontend.ExpressionUniqueness.functionTypeFamily_prec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.functionTypeFamily_prec

/-- info: 'Solidity.Frontend.ExpressionUniqueness.functionTypeFamily_yield' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.functionTypeFamily_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.wrappedFunctionExpr' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.wrappedFunctionExpr

/-- info: 'Solidity.Frontend.ExpressionUniqueness.wrappedFunctionWord' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.wrappedFunctionWord

/-- info: 'Solidity.Frontend.ExpressionUniqueness.wrappedFunctionExpr_prec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.wrappedFunctionExpr_prec

/-- info: 'Solidity.Frontend.ExpressionUniqueness.wrappedFunctionExpr_yield' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.wrappedFunctionExpr_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.wrappedFunctionExpr_certified' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.wrappedFunctionExpr_certified

/-- info: 'Solidity.Frontend.ExpressionUniqueness.wrappedFunctionExpr_any_competitor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.wrappedFunctionExpr_any_competitor

/-- info: 'Solidity.Frontend.ExpressionUniqueness.direct_function_meta_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.direct_function_meta_refused

/-- info: 'Solidity.Frontend.ExpressionUniqueness.attribute_orders_distinct' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.attribute_orders_distinct

/-- info: 'Solidity.Frontend.ExpressionUniqueness.holeTuple' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.holeTuple

/-- info: 'Solidity.Frontend.ExpressionUniqueness.holeTupleWord' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.holeTupleWord

/-- info: 'Solidity.Frontend.ExpressionUniqueness.holeTuple_prec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.holeTuple_prec

/-- info: 'Solidity.Frontend.ExpressionUniqueness.holeTuple_yield' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.holeTuple_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.holeTuple_certified' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.holeTuple_certified

/-- info: 'Solidity.Frontend.ExpressionUniqueness.holeTuple_any_competitor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.holeTuple_any_competitor

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

/-- info: 'Solidity.Frontend.ExpressionUniqueness.QBalancedItems' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.QBalancedItems

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalancedItems_balanced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalancedItems_balanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalancedItems_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalancedItems_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalancedItems_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalancedItems_cons

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalancedItems_single' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalancedItems_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalancedItems_dropHead' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalancedItems_dropHead

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalancedItems_flatten' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalancedItems_flatten

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_flatMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_flatMap

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_of_atoms' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_of_atoms

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_parens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_parens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_braces' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_braces

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_square' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_square

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_tk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_tk

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_idt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_idt

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_path

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_elem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_elem

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_visibility' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_visibility

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_mutability' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_mutability

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_dataLoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_dataLoc

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_optToks' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_optToks

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_prefix

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_suffix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_suffix

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_mul

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_add

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_shift

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_order' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_order

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_equality' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_equality

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_assign' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_assign

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fragsP_qBalanced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fragsP_qBalanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.litP_qBalanced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.litP_qBalanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.QBalancedAttrs' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.QBalancedAttrs

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalancedAttrs_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalancedAttrs_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_single' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrange_qBalanced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrange_qBalanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.attrsP_qBalanced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.attrsP_qBalanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.QState' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.QState

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qToken' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qToken

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qStep' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qStep

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qRun' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qRun

/-- info: 'Solidity.Frontend.ExpressionUniqueness.QBalanced' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.QBalanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qStep_open' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qStep_open

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qStep_close' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qStep_close

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qStep_atom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qStep_atom

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qStep_context' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qStep_context

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qRun_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qRun_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qRun_context' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qRun_context

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_enclose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_enclose

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_atom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_atom

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_conditional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_conditional

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qNeutral' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qNeutral

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qToken_neutral' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qToken_neutral

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qNeutral_atom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qNeutral_atom

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qStep_projection' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qStep_projection

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qRun_projection' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qRun_projection

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_balanced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_balanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qFailure' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qFailure

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qFailure_after_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qFailure_after_success

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qFailure_marker' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qFailure_marker

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qFailure_cut_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qFailure_cut_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_colon_cut_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_colon_cut_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.middleConditional' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.middleConditional

/-- info: 'Solidity.Frontend.ExpressionUniqueness.middleConditionalTokens' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.middleConditionalTokens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.middleConditional_prec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.middleConditional_prec

/-- info: 'Solidity.Frontend.ExpressionUniqueness.middleConditional_yield' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.middleConditional_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.middleConditional_certified' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.middleConditional_certified

/-- info: 'Solidity.Frontend.ExpressionUniqueness.middleConditional_paired' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.middleConditional_paired

/-- info: 'Solidity.Frontend.ExpressionUniqueness.middleConditionalTokens_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.middleConditionalTokens_length

/-- info: 'Solidity.Frontend.ExpressionUniqueness.middleConditional_outer_colon' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.middleConditional_outer_colon

/-- info: 'Solidity.Frontend.ExpressionUniqueness.rawColon' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.rawColon

/-- info: 'Solidity.Frontend.ExpressionUniqueness.middleConditional_raw_colon' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.middleConditional_raw_colon

/-- info: 'Solidity.Frontend.ExpressionUniqueness.middleConditional_raw_colon_wrong' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.middleConditional_raw_colon_wrong

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bracketed_colons_hidden' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bracketed_colons_hidden

/-- info: 'Solidity.Frontend.ExpressionUniqueness.ConditionalChildSpans' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.ConditionalChildSpans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.conditional_child_spans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.conditional_child_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.qBalanced_not_unpaired_colon' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.qBalanced_not_unpaired_colon

/-- info: 'Solidity.Frontend.ExpressionUniqueness.optional_expr_yield_qBalanced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.optional_expr_yield_qBalanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.slice_payload_colon_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.slice_payload_colon_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.index_slice_payload_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.index_slice_payload_disjoint

/-- info: 'Solidity.Frontend.ExpressionUniqueness.optionalHoles_vector_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.optionalHoles_vector_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.optionalHoles_prec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.optionalHoles_prec

/-- info: 'Solidity.Frontend.ExpressionUniqueness.optionalHoles_actual_vector_identity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.optionalHoles_actual_vector_identity

/-- info: 'Solidity.Frontend.ExpressionUniqueness.optionalHoles_flatten_collision' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.optionalHoles_flatten_collision

/-- info: 'Solidity.Frontend.ExpressionUniqueness.nil_vector_unique' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.nil_vector_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.cons_vector_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.cons_vector_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.none_expr_word_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.none_expr_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.some_expr_word_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.some_expr_word_unique

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

/-- info: 'Solidity.Frontend.ExpressionUniqueness.tokenBoundary_not_selected' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.tokenBoundary_not_selected

/-- info: 'Solidity.Frontend.ExpressionUniqueness.elem_tokens_shape' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.elem_tokens_shape

/-- info: 'Solidity.Frontend.ExpressionUniqueness.elementary_type_prefix_unique' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.elementary_type_prefix_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.path_pieces_prefix_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.path_pieces_prefix_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.path_type_prefix_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.path_type_prefix_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.AddFreeItems' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.AddFreeItems

/-- info: 'Solidity.Frontend.ExpressionUniqueness.AddDoneItems' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.AddDoneItems

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addFreeItems_single' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addFreeItems_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.addDoneItems_single' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.addDoneItems_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.AddYieldProperty' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.AddYieldProperty

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expression_add_property' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expression_add_property

/-- info: 'Solidity.Frontend.ExpressionUniqueness.high_expr_yield_addFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.high_expr_yield_addFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.type_yield_addDone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.type_yield_addDone

/-- info: 'Solidity.Frontend.ExpressionUniqueness.callArgs_yield_addDone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.callArgs_yield_addDone

/-- info: 'Solidity.Frontend.ExpressionUniqueness.high_expr_derives_addFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.high_expr_derives_addFree

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

/-- info: 'Solidity.Frontend.ExpressionUniqueness.BinaryYieldProperty' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.BinaryYieldProperty

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expression_binary_property' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expression_binary_property

/-- info: 'Solidity.Frontend.ExpressionUniqueness.high_expr_yield_binaryFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.high_expr_yield_binaryFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.type_yield_binaryFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.type_yield_binaryFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.high_expr_derives_binaryFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.high_expr_derives_binaryFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expressionCategory_yield_commaFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expressionCategory_yield_commaFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expr_yield_commaFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expr_yield_commaFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expr_derives_commaFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expr_derives_commaFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.certified_expr_spans_commaSep_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.certified_expr_spans_commaSep_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.ConditionalCategory' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.ConditionalCategory

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expressionCategory_yield_qBalanced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expressionCategory_yield_qBalanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expr_yield_qBalanced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expr_yield_qBalanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expr_derives_qBalanced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expr_derives_qBalanced

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

/-- info: 'Solidity.Frontend.ExpressionUniqueness.ModeDoneItems' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.ModeDoneItems

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeDoneItems_single' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeDoneItems_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.ModeYieldProperty' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.ModeYieldProperty

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expression_mode_property' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expression_mode_property

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expr_yield_modeDone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expr_yield_modeDone

/-- info: 'Solidity.Frontend.ExpressionUniqueness.type_yield_modeDone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.type_yield_modeDone

/-- info: 'Solidity.Frontend.ExpressionUniqueness.callArgs_yield_modeDone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.callArgs_yield_modeDone

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expr_derives_modeDone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expr_derives_modeDone

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expressionCategory_yield_startFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expressionCategory_yield_startFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expr_yield_noInitialCurly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expr_yield_noInitialCurly

/-- info: 'Solidity.Frontend.ExpressionUniqueness.UnaryYieldProperty' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.UnaryYieldProperty

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expression_unary_property' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expression_unary_property

/-- info: 'Solidity.Frontend.ExpressionUniqueness.high_expr_yield_unaryFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.high_expr_yield_unaryFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.type_yield_unaryFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.type_yield_unaryFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.high_expr_derives_unaryFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.high_expr_derives_unaryFree

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

/-- info: 'Solidity.Frontend.ExpressionUniqueness.typeAttribute_of_forbidden_false' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.typeAttribute_of_forbidden_false

/-- info: 'Solidity.Frontend.ExpressionUniqueness.typeAtomBoundary_attributes' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.typeAtomBoundary_attributes

/-- info: 'Solidity.Frontend.ExpressionUniqueness.tokenBoundary_cons' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.tokenBoundary_cons

/-- info: 'Solidity.Frontend.ExpressionUniqueness.type_returns_attribute_boundary' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.type_returns_attribute_boundary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.type_returns_prefix_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.type_returns_prefix_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fn_type_word_parts_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fn_type_word_parts_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fn_type_word_prefix_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fn_type_word_prefix_unique

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

/-- info: 'Solidity.Frontend.ExpressionUniqueness.type_returns_vectors_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.type_returns_vectors_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fn_type_prec_children' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fn_type_prec_children

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fn_type_same_constructor_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fn_type_same_constructor_unique

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

/-- info: 'Solidity.Frontend.ExpressionUniqueness.last_enclosed_cut_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.last_enclosed_cut_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.last_parens_cut_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.last_parens_cut_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.last_square_cut_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.last_square_cut_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.last_braces_cut_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.last_braces_cut_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.LayoutExtend' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.LayoutExtend

/-- info: 'Solidity.Frontend.ExpressionUniqueness.LayoutTrim' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.LayoutTrim

/-- info: 'Solidity.Frontend.ExpressionUniqueness.LayoutPrinter' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.LayoutPrinter

/-- info: 'Solidity.Frontend.ExpressionUniqueness.layout_pure' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.layout_pure

/-- info: 'Solidity.Frontend.ExpressionUniqueness.layout_lift' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.layout_lift

/-- info: 'Solidity.Frontend.ExpressionUniqueness.layout_pop' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.layout_pop

/-- info: 'Solidity.Frontend.ExpressionUniqueness.layout_bind' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.layout_bind

/-- info: 'Solidity.Frontend.ExpressionUniqueness.layout_popAttrs' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.layout_popAttrs

/-- info: 'Solidity.Frontend.ExpressionUniqueness.layout_fragsP' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.layout_fragsP

/-- info: 'Solidity.Frontend.ExpressionUniqueness.layout_litP' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.layout_litP

/-- info: 'Solidity.Frontend.ExpressionUniqueness.layout_attrsP' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.layout_attrsP

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expressionCategory_yield_layout' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expressionCategory_yield_layout

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expression_yield_trim' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expression_yield_trim

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expression_partial_derives' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expression_partial_derives

/-- info: 'Solidity.Frontend.ExpressionUniqueness.literalTokenSelect' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.literalTokenSelect

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fragsP_allTokens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fragsP_allTokens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.literalP_allTokens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.literalP_allTokens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.literal_yield_allTokens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.literal_yield_allTokens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.literal_prefix_kinds_equal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.literal_prefix_kinds_equal

/-- info: 'Solidity.Frontend.ExpressionUniqueness.literal_yield_prefix_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.literal_yield_prefix_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.isDenomToken' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.isDenomToken

/-- info: 'Solidity.Frontend.ExpressionUniqueness.literal_unit_prefix_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.literal_unit_prefix_disjoint

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unit_yield_prefix_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unit_yield_prefix_unique

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

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mapping_type_prec_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mapping_type_prec_child

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mapping_type_same_constructor_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mapping_type_same_constructor_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mapping_type_word_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mapping_type_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mapKeyWord' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mapKeyWord

/-- info: 'Solidity.Frontend.ExpressionUniqueness.elementary_path_prefix_disjoint' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.elementary_path_prefix_disjoint

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mapKey_word_prefix_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mapKey_word_prefix_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mapping_key_tail_boundary' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mapping_key_tail_boundary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mapping_name_arrow_unique' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mapping_name_arrow_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.parens_word_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.parens_word_injective

/-- info: 'Solidity.Frontend.ExpressionUniqueness.memberToken' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.memberToken

/-- info: 'Solidity.Frontend.ExpressionUniqueness.member_word_single' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.member_word_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.memberToken_injective' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.memberToken_injective

/-- info: 'Solidity.Frontend.ExpressionUniqueness.member_yield_parts' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.member_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.member_child_spans' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.member_child_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.namedArg_child_spans' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.namedArg_child_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.ModeState' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.ModeState

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeToken' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeToken

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeStep' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeStep

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeRun' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeRun

/-- info: 'Solidity.Frontend.ExpressionUniqueness.ModeAny' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.ModeAny

/-- info: 'Solidity.Frontend.ExpressionUniqueness.ModeDone' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.ModeDone

/-- info: 'Solidity.Frontend.ExpressionUniqueness.ModeStable' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.ModeStable

/-- info: 'Solidity.Frontend.ExpressionUniqueness.append_stack_not_empty' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.append_stack_not_empty

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeStep_open' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeStep_open

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeStep_close' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeStep_close

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeStep_atom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeStep_atom

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeStep_context' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeStep_context

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeRun_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeRun_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeRun_context' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeRun_context

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeRun_of_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeRun_of_run

/-- info: 'Solidity.Frontend.ExpressionUniqueness.balanced_modeAny' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.balanced_modeAny

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeDone_enclose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeDone_enclose

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeDone_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeDone_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeDone_stable' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeDone_stable

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeStable_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeStable_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeStable_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeStable_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeDone_stable_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeDone_stable_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeDone_atom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeDone_atom

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeStable_atom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeStable_atom

/-- info: 'Solidity.Frontend.ExpressionUniqueness.ModeStableItems' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.ModeStableItems

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeStableItems_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeStableItems_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeStableItems_tail' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeStableItems_tail

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeStable_flatMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeStable_flatMap

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeStable_of_atoms' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeStable_of_atoms

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeDone_map_nonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeDone_map_nonempty

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeDone_parens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeDone_parens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeDone_braces' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeDone_braces

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeDone_square' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeDone_square

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeDone_idt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeDone_idt

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeDone_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeDone_path

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeDone_elem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeDone_elem

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeStable_visibility' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeStable_visibility

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeStable_mutability' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeStable_mutability

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeStable_dataLoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeStable_dataLoc

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeStable_optToks' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeStable_optToks

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fragsP_modeDone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fragsP_modeDone

/-- info: 'Solidity.Frontend.ExpressionUniqueness.litP_modeDone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.litP_modeDone

/-- info: 'Solidity.Frontend.ExpressionUniqueness.ModeStableAttrs' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.ModeStableAttrs

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeStableAttrs_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeStableAttrs_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.modeStable_single' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.modeStable_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrange_modeStable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrange_modeStable

/-- info: 'Solidity.Frontend.ExpressionUniqueness.attrsP_modeStable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.attrsP_modeStable

/-- info: 'Solidity.Frontend.ExpressionUniqueness.option_location_cases' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.option_location_cases

/-- info: 'Solidity.Frontend.ExpressionUniqueness.parameter_tail_boundary' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.parameter_tail_boundary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.parameter_tail_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.parameter_tail_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.parameter_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.parameter_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.parameter_prec_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.parameter_prec_child

/-- info: 'Solidity.Frontend.ExpressionUniqueness.parameter_word_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.parameter_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.type_yield_nonemptyWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.type_yield_nonemptyWord

/-- info: 'Solidity.Frontend.ExpressionUniqueness.word_append_nonempty_left' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.word_append_nonempty_left

/-- info: 'Solidity.Frontend.ExpressionUniqueness.parameter_yield_nonemptyWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.parameter_yield_nonemptyWord

/-- info: 'Solidity.Frontend.ExpressionUniqueness.ParameterVectorProperty' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.ParameterVectorProperty

/-- info: 'Solidity.Frontend.ExpressionUniqueness.parameter_vector_property' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.parameter_vector_property

/-- info: 'Solidity.Frontend.ExpressionUniqueness.parameterList_yield_nonemptyWords' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.parameterList_yield_nonemptyWords

/-- info: 'Solidity.Frontend.ExpressionUniqueness.pair_pure_success_join' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.pair_pure_success_join

/-- info: 'Solidity.Frontend.ExpressionUniqueness.triple_pure_success_join' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.triple_pure_success_join

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfixStep' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfixStep

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfixTail' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfixTail

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfixStep_prec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfixStep_prec

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfixStep_yield' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfixStep_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfixTower' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfixTower

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfixTowerTokens' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfixTowerTokens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfixTower_prec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfixTower_prec

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfixTower_yield' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfixTower_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfixTower_certified' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfixTower_certified

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfixTowerTokens_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfixTowerTokens_length

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfixTower_same_yield_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfixTower_same_yield_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.optionalHoles' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.optionalHoles

/-- info: 'Solidity.Frontend.ExpressionUniqueness.optionalHoles_yield' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.optionalHoles_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.optionalHoles_nonemptyWords_refuted' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.optionalHoles_nonemptyWords_refuted

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expressionList_empty_component_impossible' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expressionList_empty_component_impossible

/-- info: 'Solidity.Frontend.ExpressionUniqueness.PostfixFollower' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.PostfixFollower

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfixFollower_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfixFollower_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfixFollower_parens' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfixFollower_parens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfixFollower_braces' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfixFollower_braces

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfixFollower_square' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfixFollower_square

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfixFollower_period' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfixFollower_period

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfixFollower_append' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfixFollower_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.word_append_nonempty_right' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.word_append_nonempty_right

/-- info: 'Solidity.Frontend.ExpressionUniqueness.new_postfixFollower_typeBoundary' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.new_postfixFollower_typeBoundary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfixFollower_tokenBoundary' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfixFollower_tokenBoundary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.index_prec_children' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.index_prec_children

/-- info: 'Solidity.Frontend.ExpressionUniqueness.index_word_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.index_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.slice_prec_children' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.slice_prec_children

/-- info: 'Solidity.Frontend.ExpressionUniqueness.slice_word_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.slice_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.member_prec_children' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.member_prec_children

/-- info: 'Solidity.Frontend.ExpressionUniqueness.member_word_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.member_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.callOptions_prec_children' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.callOptions_prec_children

/-- info: 'Solidity.Frontend.ExpressionUniqueness.callOptions_word_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.callOptions_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.call_prec_children' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.call_prec_children

/-- info: 'Solidity.Frontend.ExpressionUniqueness.call_word_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.call_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfixRootKind' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfixRootKind

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfixEndCode' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfixEndCode

/-- info: 'Solidity.Frontend.ExpressionUniqueness.tokenEndClass' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.tokenEndClass

/-- info: 'Solidity.Frontend.ExpressionUniqueness.PostfixEnd' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.PostfixEnd

/-- info: 'Solidity.Frontend.ExpressionUniqueness.final_token_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.final_token_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfixEnd_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfixEnd_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.index_yield_postfixEnd' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.index_yield_postfixEnd

/-- info: 'Solidity.Frontend.ExpressionUniqueness.slice_yield_postfixEnd' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.slice_yield_postfixEnd

/-- info: 'Solidity.Frontend.ExpressionUniqueness.member_yield_postfixEnd' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.member_yield_postfixEnd

/-- info: 'Solidity.Frontend.ExpressionUniqueness.options_yield_postfixEnd' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.options_yield_postfixEnd

/-- info: 'Solidity.Frontend.ExpressionUniqueness.call_yield_postfixEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.call_yield_postfixEnd

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expr_level_fifteen_cases' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expr_level_fifteen_cases

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfix_yield_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfix_yield_end

/-- info: 'Solidity.Frontend.ExpressionUniqueness.partial_postfix_root_kinds_equal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.partial_postfix_root_kinds_equal

/-- info: 'Solidity.Frontend.ExpressionUniqueness.PairYieldSpans' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.PairYieldSpans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.TripleYieldSpans' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.TripleYieldSpans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.index_child_spans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.index_child_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.slice_child_spans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.slice_child_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.index_slice_yields_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.index_slice_yields_disjoint

/-- info: 'Solidity.Frontend.ExpressionUniqueness.call_child_spans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.call_child_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.options_child_spans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.options_child_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.triple_pure_success_split' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.triple_pure_success_split

/-- info: 'Solidity.Frontend.ExpressionUniqueness.index_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.index_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.slice_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.slice_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.call_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.call_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.options_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.options_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.namedArg_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.namedArg_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.callArgs_yield_parens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.callArgs_yield_parens

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

/-- info: 'Solidity.Frontend.ExpressionUniqueness.commaSep_head_tail' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.commaSep_head_tail

/-- info: 'Solidity.Frontend.ExpressionUniqueness.surround_word_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.surround_word_injective

/-- info: 'Solidity.Frontend.ExpressionUniqueness.new_prec_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.new_prec_child

/-- info: 'Solidity.Frontend.ExpressionUniqueness.new_word_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.new_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.metaType_prec_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.metaType_prec_child

/-- info: 'Solidity.Frontend.ExpressionUniqueness.metaType_word_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.metaType_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.payableConv_prec_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.payableConv_prec_child

/-- info: 'Solidity.Frontend.ExpressionUniqueness.payableConv_word_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.payableConv_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.tuple_prec_children' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.tuple_prec_children

/-- info: 'Solidity.Frontend.ExpressionUniqueness.tuple_word_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.tuple_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.inlineArray_prec_children' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.inlineArray_prec_children

/-- info: 'Solidity.Frontend.ExpressionUniqueness.inlineArray_word_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.inlineArray_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.primary_competitor_kind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.primary_competitor_kind

/-- info: 'Solidity.Frontend.ExpressionUniqueness.ident_word_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.ident_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.elementary_expr_word_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.elementary_expr_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.literal_word_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.literal_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unit_word_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unit_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expr_level_sixteen_cases' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expr_level_sixteen_cases

/-- info: 'Solidity.Frontend.ExpressionUniqueness.primary_yield_prefix_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.primary_yield_prefix_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.ident_yield_prefix_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.ident_yield_prefix_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.elem_expr_yield_prefix_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.elem_expr_yield_prefix_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.new_yield_prefix_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.new_yield_prefix_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.payable_yield_prefix_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.payable_yield_prefix_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.meta_yield_prefix_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.meta_yield_prefix_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.tuple_yield_prefix_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.tuple_yield_prefix_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.inline_yield_prefix_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.inline_yield_prefix_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.PrimarySpine' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.PrimarySpine

/-- info: 'Solidity.Frontend.ExpressionUniqueness.PrimarySpineProperty' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.PrimarySpineProperty

/-- info: 'Solidity.Frontend.ExpressionUniqueness.primary_spine_property' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.primary_spine_property

/-- info: 'Solidity.Frontend.ExpressionUniqueness.high_expr_primary_spine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.high_expr_primary_spine

/-- info: 'Solidity.Frontend.ExpressionUniqueness.primaryRootKind' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.primaryRootKind

/-- info: 'Solidity.Frontend.ExpressionUniqueness.primaryTokenKind' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.primaryTokenKind

/-- info: 'Solidity.Frontend.ExpressionUniqueness.PrimaryStart' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.PrimaryStart

/-- info: 'Solidity.Frontend.ExpressionUniqueness.literalToken_primaryKind' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.literalToken_primaryKind

/-- info: 'Solidity.Frontend.ExpressionUniqueness.primary_yield_start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.primary_yield_start

/-- info: 'Solidity.Frontend.ExpressionUniqueness.primary_prefix_kinds_equal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.primary_prefix_kinds_equal

/-- info: 'Solidity.Frontend.ExpressionUniqueness.new_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.new_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.payable_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.payable_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.meta_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.meta_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.tuple_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.tuple_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.inline_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.inline_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.payable_actual_parens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.payable_actual_parens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.meta_actual_parens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.meta_actual_parens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.tuple_actual_parens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.tuple_actual_parens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.inline_actual_square' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.inline_actual_square

/-- info: 'Solidity.Frontend.ExpressionUniqueness.WordUnique' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.WordUnique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.VectorUnique' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.VectorUnique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.RecursiveYieldProperty' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.RecursiveYieldProperty

/-- info: 'Solidity.Frontend.ExpressionUniqueness.list_prec_children' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.list_prec_children

/-- info: 'Solidity.Frontend.ExpressionUniqueness.some_prec_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.some_prec_child

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

/-- info: 'Solidity.Frontend.ExpressionUniqueness.postfixTower_root_reconstructed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.postfixTower_root_reconstructed

/-- info: 'Solidity.Frontend.ExpressionUniqueness.new_array_root_reconstructed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.new_array_root_reconstructed

/-- info: 'Solidity.Frontend.ExpressionUniqueness.direct_new_square_follower_refuted' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.direct_new_square_follower_refuted

/-- info: 'Solidity.Frontend.ExpressionUniqueness.direct_new_period_follower_refuted' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.direct_new_period_follower_refuted

/-- info: 'Solidity.Frontend.ExpressionUniqueness.new_array_call_follower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.new_array_call_follower

/-- info: 'Solidity.Frontend.ExpressionUniqueness.new_array_options_follower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.new_array_options_follower

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expr_level_thirteen_cases' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expr_level_thirteen_cases

/-- info: 'Solidity.Frontend.ExpressionUniqueness.loose_higher_root_disjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.loose_higher_root_disjoint

/-- info: 'Solidity.Frontend.ExpressionUniqueness.through_unary_higher_root_disjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.through_unary_higher_root_disjoint

/-- info: 'Solidity.Frontend.ExpressionUniqueness.certified_root_levels_equal_through_unary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.certified_root_levels_equal_through_unary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.partial_root_levels_equal_through_unary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.partial_root_levels_equal_through_unary

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

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mixedAddPrefix_partial_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mixedAddPrefix_partial_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mixedAddPrefix_same_yield_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mixedAddPrefix_same_yield_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.NoInitialCurly' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.NoInitialCurly

/-- info: 'Solidity.Frontend.ExpressionUniqueness.StartFree' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.StartFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.StartFreeItems' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.StartFreeItems

/-- info: 'Solidity.Frontend.ExpressionUniqueness.curlyHead' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.curlyHead

/-- info: 'Solidity.Frontend.ExpressionUniqueness.noInitialCurly_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.noInitialCurly_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.noInitialCurly_append_any' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.noInitialCurly_append_any

/-- info: 'Solidity.Frontend.ExpressionUniqueness.noInitialCurly_append' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.noInitialCurly_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_balanced' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_balanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFreeItems_balanced' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFreeItems_balanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_append_any' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_append_any

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_atom' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_atom

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFreeItems_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFreeItems_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFreeItems_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFreeItems_cons

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFreeItems_single' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFreeItems_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFreeItems_dropHead' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFreeItems_dropHead

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFreeItems_flatten' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFreeItems_flatten

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_flatMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_flatMap

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_of_atoms' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_of_atoms

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_parens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_parens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_square' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_square

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_tk' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_tk

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_idt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_idt

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_path

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_elem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_elem

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_visibility' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_visibility

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_mutability' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_mutability

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_dataLoc' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_dataLoc

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_optToks' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_optToks

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_prefix' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_prefix

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_suffix' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_suffix

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_mul' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_mul

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_add' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_add

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_shift' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_shift

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_order' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_order

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_equality' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_equality

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_assign' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_assign

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fragsP_startFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fragsP_startFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.litP_startFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.litP_startFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.StartFreeAttrs' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.StartFreeAttrs

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFreeAttrs_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFreeAttrs_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.startFree_single' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.startFree_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrange_startFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrange_startFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.attrsP_startFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.attrsP_startFree

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

/-- info: 'Solidity.Frontend.ExpressionUniqueness.squareWords_nonempty_last' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.squareWords_nonempty_last

/-- info: 'Solidity.Frontend.ExpressionUniqueness.array_atom_yields_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.array_atom_yields_disjoint

/-- info: 'Solidity.Frontend.ExpressionUniqueness.array_type_child_spans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.array_type_child_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.array_type_prec_children' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.array_type_prec_children

/-- info: 'Solidity.Frontend.ExpressionUniqueness.array_type_word_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.array_type_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.elem_type_yield_prefix_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.elem_type_yield_prefix_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.user_type_yield_prefix_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.user_type_yield_prefix_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mapping_type_actual_parens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mapping_type_actual_parens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mapping_type_yield_prefix_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mapping_type_yield_prefix_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fn_type_yield_prefix_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fn_type_yield_prefix_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.typeAtom_cases' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.typeAtom_cases

/-- info: 'Solidity.Frontend.ExpressionUniqueness.type_atom_yield_prefix_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.type_atom_yield_prefix_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.typeAtomKind' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.typeAtomKind

/-- info: 'Solidity.Frontend.ExpressionUniqueness.typeTokenClass' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.typeTokenClass

/-- info: 'Solidity.Frontend.ExpressionUniqueness.TypeStart' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.TypeStart

/-- info: 'Solidity.Frontend.ExpressionUniqueness.typeAtom_yield_start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.typeAtom_yield_start

/-- info: 'Solidity.Frontend.ExpressionUniqueness.typeAtom_prefix_kinds_equal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.typeAtom_prefix_kinds_equal

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrayTypeFamily_word_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrayTypeFamily_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrayTypeFamily_actual_identity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrayTypeFamily_actual_identity

/-- info: 'Solidity.Frontend.ExpressionUniqueness.empty_function_type_word_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.empty_function_type_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.same_yield_type_atom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.same_yield_type_atom

/-- info: 'Solidity.Frontend.ExpressionUniqueness.same_yield_type_atom_kind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.same_yield_type_atom_kind

/-- info: 'Solidity.Frontend.ExpressionUniqueness.elementary_tokens_injective' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.elementary_tokens_injective

/-- info: 'Solidity.Frontend.ExpressionUniqueness.path_tail_tokens_injective' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.path_tail_tokens_injective

/-- info: 'Solidity.Frontend.ExpressionUniqueness.path_tokens_injective' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.path_tokens_injective

/-- info: 'Solidity.Frontend.ExpressionUniqueness.elementary_type_word_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.elementary_type_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.user_type_word_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.user_type_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fn_type_word_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fn_type_word_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.type_yield_prefix_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.type_yield_prefix_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.AllTokens' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.AllTokens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.TokenBoundary' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.TokenBoundary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.tokenBoundary_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.tokenBoundary_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.maximal_token_run_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.maximal_token_run_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.squareWords' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.squareWords

/-- info: 'Solidity.Frontend.ExpressionUniqueness.isLeftSquare' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.isLeftSquare

/-- info: 'Solidity.Frontend.ExpressionUniqueness.squareWords_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.squareWords_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.squareWords_cons' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.squareWords_cons

/-- info: 'Solidity.Frontend.ExpressionUniqueness.squareWords_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.squareWords_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.squareWords_boundary' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.squareWords_boundary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.squareWords_cut_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.squareWords_cut_unique

/-- info: 'Solidity.Frontend.ExpressionUniqueness.typeAttributeToken' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.typeAttributeToken

/-- info: 'Solidity.Frontend.ExpressionUniqueness.typeAtomForbidden' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.typeAtomForbidden

/-- info: 'Solidity.Frontend.ExpressionUniqueness.TypeAtomBoundary' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.TypeAtomBoundary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.TypeBoundary' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.TypeBoundary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.typeAtomBoundary_squareWords' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.typeAtomBoundary_squareWords

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrayTypeFamily' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrayTypeFamily

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrayTypeTokens' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrayTypeTokens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrayTypeFamily_prec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrayTypeFamily_prec

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrayTypeFamily_yield' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrayTypeFamily_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrayTypeFamily_derives' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrayTypeFamily_derives

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrayTypeTokens_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrayTypeTokens_length

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrayTypeFamily_tokens_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrayTypeFamily_tokens_injective

/-- info: 'Solidity.Frontend.ExpressionUniqueness.nil_type_boundary' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.nil_type_boundary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.array_follow_boundary_refuted' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.array_follow_boundary_refuted

/-- info: 'Solidity.Frontend.ExpressionUniqueness.payable_follow_boundary_refuted' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.payable_follow_boundary_refuted

/-- info: 'Solidity.Frontend.ExpressionUniqueness.view_follow_boundary_refuted' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.view_follow_boundary_refuted

/-- info: 'Solidity.Frontend.ExpressionUniqueness.raw_new_array_index_collision' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.raw_new_array_index_collision

/-- info: 'Solidity.Frontend.ExpressionUniqueness.raw_collision_direct_new_index_refused' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.raw_collision_direct_new_index_refused

/-- info: 'Solidity.Frontend.ExpressionUniqueness.new_arrayTypeFamily_certified' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.new_arrayTypeFamily_certified

/-- info: 'Solidity.Frontend.ExpressionUniqueness.isTypeAtom' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.isTypeAtom

/-- info: 'Solidity.Frontend.ExpressionUniqueness.TypeSpineProperty' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.TypeSpineProperty

/-- info: 'Solidity.Frontend.ExpressionUniqueness.type_spine_property' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.type_spine_property

/-- info: 'Solidity.Frontend.ExpressionUniqueness.type_yield_spine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.type_yield_spine

/-- info: 'Solidity.Frontend.ExpressionUniqueness.array_type_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.array_type_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mapping_type_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mapping_type_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fn_type_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fn_type_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fn_type_actual_attribute_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fn_type_actual_attribute_run

/-- info: 'Solidity.Frontend.ExpressionUniqueness.prefixChain' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.prefixChain

/-- info: 'Solidity.Frontend.ExpressionUniqueness.prefixChainTokens' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.prefixChainTokens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.prefixChain_prec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.prefixChain_prec

/-- info: 'Solidity.Frontend.ExpressionUniqueness.prefixChain_yield' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.prefixChain_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.prefixChain_certified' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.prefixChain_certified

/-- info: 'Solidity.Frontend.ExpressionUniqueness.prefixChain_marker' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.prefixChain_marker

/-- info: 'Solidity.Frontend.ExpressionUniqueness.suffixChain' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.suffixChain

/-- info: 'Solidity.Frontend.ExpressionUniqueness.suffixChainTokens' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.suffixChainTokens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.suffixChain_prec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.suffixChain_prec

/-- info: 'Solidity.Frontend.ExpressionUniqueness.suffixChain_yield' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.suffixChain_yield

/-- info: 'Solidity.Frontend.ExpressionUniqueness.suffixChain_certified' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.suffixChain_certified

/-- info: 'Solidity.Frontend.ExpressionUniqueness.suffixChainTokens_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.suffixChainTokens_length

/-- info: 'Solidity.Frontend.ExpressionUniqueness.suffixChain_marker' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.suffixChain_marker

/-- info: 'Solidity.Frontend.ExpressionUniqueness.ungrouped_suffix_chain_refused' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.ungrouped_suffix_chain_refused

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryMarker' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryMarker

/-- info: 'Solidity.Frontend.ExpressionUniqueness.UnaryFree' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.UnaryFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.UnaryFreeItems' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.UnaryFreeItems

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryMarker_atomic' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryMarker_atomic

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFree_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFree_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFree_balanced' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFree_balanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFreeItems_balanced' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFreeItems_balanced

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFree_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFree_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFree_atom' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFree_atom

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFreeItems_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFreeItems_nil

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFreeItems_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFreeItems_cons

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFreeItems_single' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFreeItems_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFreeItems_dropHead' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFreeItems_dropHead

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFreeItems_flatten' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFreeItems_flatten

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFree_flatMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFree_flatMap

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFree_of_atoms' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFree_of_atoms

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFree_parens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFree_parens

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFree_braces' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFree_braces

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFree_square' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFree_square

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFree_tk' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFree_tk

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFree_idt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFree_idt

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFree_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFree_path

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFree_elem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFree_elem

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFree_visibility' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFree_visibility

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFree_mutability' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFree_mutability

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFree_dataLoc' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFree_dataLoc

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFree_optToks' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFree_optToks

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFree_mul' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFree_mul

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFree_shift' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFree_shift

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFree_order' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFree_order

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFree_equality' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFree_equality

/-- info: 'Solidity.Frontend.ExpressionUniqueness.fragsP_unaryFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.fragsP_unaryFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.litP_unaryFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.litP_unaryFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.UnaryFreeAttrs' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.UnaryFreeAttrs

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFreeAttrs_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFreeAttrs_append

/-- info: 'Solidity.Frontend.ExpressionUniqueness.unaryFree_single' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.unaryFree_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.arrange_unaryFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.arrange_unaryFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.attrsP_unaryFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.attrsP_unaryFree

/-- info: 'Solidity.Frontend.ExpressionUniqueness.prefixToken' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.prefixToken

/-- info: 'Solidity.Frontend.ExpressionUniqueness.prefix_word_single' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.prefix_word_single

/-- info: 'Solidity.Frontend.ExpressionUniqueness.prefixToken_injective' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.prefixToken_injective

/-- info: 'Solidity.Frontend.ExpressionUniqueness.suffix_punct_injective' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.suffix_punct_injective

/-- info: 'Solidity.Frontend.ExpressionUniqueness.UnaryChildSpans' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.UnaryChildSpans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.prefix_child_spans' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.prefix_child_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.suffix_child_spans' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.suffix_child_spans

/-- info: 'Solidity.Frontend.ExpressionUniqueness.prefix_yield_firstUnary' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.prefix_yield_firstUnary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.suffix_yield_firstUnary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.suffix_yield_firstUnary

/-- info: 'Solidity.Frontend.ExpressionUniqueness.high_yield_firstUnary_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.high_yield_firstUnary_none

/-- info: 'Solidity.Frontend.ExpressionUniqueness.suffix_higher_root_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.suffix_higher_root_disjoint

/-- info: 'Solidity.Frontend.ExpressionUniqueness.expr_level_fourteen_cases' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.expr_level_fourteen_cases

/-- info: 'Solidity.Frontend.ExpressionUniqueness.prefix_higher_root_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.prefix_higher_root_disjoint

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

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bind_success_split' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bind_success_split

/-- info: 'Solidity.Frontend.ExpressionUniqueness.pure_success_split' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.pure_success_split

/-- info: 'Solidity.Frontend.ExpressionUniqueness.pair_pure_success_split' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.pair_pure_success_split

/-- info: 'Solidity.Frontend.ExpressionUniqueness.one_pure_success_split' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.one_pure_success_split

/-- info: 'Solidity.Frontend.ExpressionUniqueness.exp_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.exp_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.mul_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.mul_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.add_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.add_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.shift_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.shift_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.order_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.order_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.equality_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.equality_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bitAnd_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bitAnd_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bitXor_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bitXor_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.bitOr_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.bitOr_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.and_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.and_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.or_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.or_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.assignment_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.assignment_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.conditional_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.conditional_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.prefix_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.prefix_yield_parts

/-- info: 'Solidity.Frontend.ExpressionUniqueness.suffix_yield_parts' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.ExpressionUniqueness.suffix_yield_parts
