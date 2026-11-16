import Solidity.Frontend.StatementGrammarH28.FramedStatementList

open Solidity.Frontend.StatementGrammarH28

#check semiFree_flatten
#print axioms semiFree_flatten
#check SemiFree.wrap
#print axioms SemiFree.wrap
#check semiFreeParts_nil
#print axioms semiFreeParts_nil
#check semiFreeParts_cons
#print axioms semiFreeParts_cons
#check semiFreeParts_singleton
#print axioms semiFreeParts_singleton
#check semiFreeParts_flat
#print axioms semiFreeParts_flat
#check semiFree_kw
#print axioms semiFree_kw
#check semiFree_id
#print axioms semiFree_id
#check semiFree_punct
#print axioms semiFree_punct
#check semiFree_parens
#print axioms semiFree_parens
#check semiFree_optToks
#print axioms semiFree_optToks
#check semiFree_intersperse
#print axioms semiFree_intersperse
#check semiFree_commaSep
#print axioms semiFree_commaSep
#check semiFree_flatMap_prefix
#print axioms semiFree_flatMap_prefix
#check semiFree_map_tokens
#print axioms semiFree_map_tokens
#check semiFreeParts_map
#print axioms semiFreeParts_map
#check semiFreeParts_replicate
#print axioms semiFreeParts_replicate
#check fragsP_semiFree
#print axioms fragsP_semiFree
#check semiFree_choice
#print axioms semiFree_choice
#check semiFree_optional
#print axioms semiFree_optional
#check semiFree_elem_atom
#print axioms semiFree_elem_atom
#check semiFree_elem
#print axioms semiFree_elem
#check semiFree_path
#print axioms semiFree_path
#check semiFree_visibility
#print axioms semiFree_visibility
#check semiFree_mutability
#print axioms semiFree_mutability
#check semiFree_dataLoc
#print axioms semiFree_dataLoc
#check litP_semiFree
#print axioms litP_semiFree
#check semiFree_prefix
#print axioms semiFree_prefix
#check semiFree_suffix
#print axioms semiFree_suffix
#check semiFree_mul
#print axioms semiFree_mul
#check semiFree_add
#print axioms semiFree_add
#check semiFree_shift
#print axioms semiFree_shift
#check semiFree_order
#print axioms semiFree_order
#check semiFree_equality
#print axioms semiFree_equality
#check semiFree_assign
#print axioms semiFree_assign
#check semiFree_single
#print axioms semiFree_single
#check arrange_empty_mods_semiFree
#print axioms arrange_empty_mods_semiFree
#check attrsP_empty_mods_semiFree
#print axioms attrsP_empty_mods_semiFree
#check syntax_yield_semiFree
#print axioms syntax_yield_semiFree
#check expression_yield_semiFree
#print axioms expression_yield_semiFree
#check simple_yield_semiFree
#print axioms simple_yield_semiFree
#check semiFree_scan_frame
#print axioms semiFree_scan_frame
#check semiFree_end_split
#print axioms semiFree_end_split
#check statement_semicolon_shape
#print axioms statement_semicolon_shape
#check semicolon_statement_prefix_split
#print axioms semicolon_statement_prefix_split
#check statement_yield_nonempty
#print axioms statement_yield_nonempty
#check block_statement_prefix_split
#print axioms block_statement_prefix_split
#check framed_statement_prefix_split
#print axioms framed_statement_prefix_split
#check framed_statement_list_split
#print axioms framed_statement_list_split
