import Solidity.Frontend.StatementGrammarH28.SyntaxBalance

/-! Exact public theorem signatures and kernel axiom audit for H31 balance. -/
namespace Solidity.Frontend.StatementGrammarH28
set_option pp.universes true
#check balancedParts_nil
#print axioms balancedParts_nil
#check balancedParts_cons
#print axioms balancedParts_cons
#check balancedParts_singleton
#print axioms balancedParts_singleton
#check balancedParts_flat
#print axioms balancedParts_flat
#check ensures_bind_checked
#print axioms ensures_bind_checked
#check balanced_kw
#print axioms balanced_kw
#check balanced_id
#print axioms balanced_id
#check balanced_punct
#print axioms balanced_punct
#check balanced_parens
#print axioms balanced_parens
#check balanced_optToks
#print axioms balanced_optToks
#check balanced_intersperse
#print axioms balanced_intersperse
#check balanced_commaSep
#print axioms balanced_commaSep
#check balanced_flatMap_prefix
#print axioms balanced_flatMap_prefix
#check balanced_map_tokens
#print axioms balanced_map_tokens
#check balancedParts_map
#print axioms balancedParts_map
#check balancedParts_replicate
#print axioms balancedParts_replicate
#check ensures_lift_none
#print axioms ensures_lift_none
#check fragsP_balanced
#print axioms fragsP_balanced
#check balanced_choice
#print axioms balanced_choice
#check balanced_optional
#print axioms balanced_optional
#check balanced_elem_atom
#print axioms balanced_elem_atom
#check balanced_elem
#print axioms balanced_elem
#check balanced_path
#print axioms balanced_path
#check balanced_visibility
#print axioms balanced_visibility
#check balanced_mutability
#print axioms balanced_mutability
#check balanced_dataLoc
#print axioms balanced_dataLoc
#check balanced_yulLit
#print axioms balanced_yulLit
#check litP_balanced
#print axioms litP_balanced
#check balanced_prefix
#print axioms balanced_prefix
#check balanced_suffix
#print axioms balanced_suffix
#check balanced_mul
#print axioms balanced_mul
#check balanced_add
#print axioms balanced_add
#check balanced_shift
#print axioms balanced_shift
#check balanced_order
#print axioms balanced_order
#check balanced_equality
#print axioms balanced_equality
#check balanced_assign
#print axioms balanced_assign
#check balanced_single
#print axioms balanced_single
#check arrange_empty_mods_balanced
#print axioms arrange_empty_mods_balanced
#check attrsP_empty_mods_balanced
#print axioms attrsP_empty_mods_balanced
#check syntax_yield_balanced
#print axioms syntax_yield_balanced
#check expression_yield_balanced
#print axioms expression_yield_balanced
#check statement_yield_balanced
#print axioms statement_yield_balanced
#check arbitrary_block_boundary
#print axioms arbitrary_block_boundary
#check successful_block_boundary
#print axioms successful_block_boundary
#check arbitrary_block_prefix_split
#print axioms arbitrary_block_prefix_split
end Solidity.Frontend.StatementGrammarH28
