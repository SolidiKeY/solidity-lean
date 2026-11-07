import Solidity.Frontend.StatementGrammarH28.ContextualDeclCounterexample

/-! Complete public theorem signature and kernel axiom audit for contract roots
and the independently retained intrinsic-completeness counterexample. -/
namespace Solidity.Frontend.StatementGrammarH28
set_option pp.universes true
#check safe_start_nonempty
#print axioms safe_start_nonempty
#check ensures_both
#print axioms ensures_both
#check nonIdent_append
#print axioms nonIdent_append
#check nonIdent_atom_pair_safe
#print axioms nonIdent_atom_pair_safe
#check paren_separator
#print axioms paren_separator
#check atom_pair_safe_frame
#print axioms atom_pair_safe_frame
#check nonIdent_map
#print axioms nonIdent_map
#check fragsP_nonIdent
#print axioms fragsP_nonIdent
#check litP_nonIdent
#print axioms litP_nonIdent
#check elem_nonIdent
#print axioms elem_nonIdent
#check prefix_nonIdent
#print axioms prefix_nonIdent
#check path_atom_pair_safe
#print axioms path_atom_pair_safe
#check suffix_separator
#print axioms suffix_separator
#check mul_separator
#print axioms mul_separator
#check add_separator
#print axioms add_separator
#check shift_separator
#print axioms shift_separator
#check order_separator
#print axioms order_separator
#check equality_separator
#print axioms equality_separator
#check assign_separator
#print axioms assign_separator
#check syntax_pair_invariant
#print axioms syntax_pair_invariant
#check expression_pair_safe
#print axioms expression_pair_safe
#check type_pair_safe
#print axioms type_pair_safe
#check call_args_paren_start
#print axioms call_args_paren_start
#check atom_pair_no_bad_triple
#print axioms atom_pair_no_bad_triple
#check nonIdent_frame_safe
#print axioms nonIdent_frame_safe
#check decl_head_no_bad_triple
#print axioms decl_head_no_bad_triple
#check path_append_member
#print axioms path_append_member
#check revert_bad_triple
#print axioms revert_bad_triple
#check syntax_path_yield
#print axioms syntax_path_yield
#check var_decl_yield_shape
#print axioms var_decl_yield_shape
#check simple_semicolon_frame
#print axioms simple_semicolon_frame
#check simple_statement_frame
#print axioms simple_statement_frame
#check revert_statement_bad_frame
#print axioms revert_statement_bad_frame
#check simple_revert_prefix_distinct
#print axioms simple_revert_prefix_distinct
#check simple_revert_root_prefix_distinct
#print axioms simple_revert_root_prefix_distinct
#check statement_root_unique_node_contract
#print axioms statement_root_unique_node_contract
#check statement_root_unique
#print axioms statement_root_unique
#check contextual_decl_successful_yield
#print axioms contextual_decl_successful_yield
#check contextual_decl_existing_guards
#print axioms contextual_decl_existing_guards
#check contextual_decl_ascii_lexer
#print axioms contextual_decl_ascii_lexer
#check contextual_decl_refused
#print axioms contextual_decl_refused
#check contextual_decl_no_success
#print axioms contextual_decl_no_success
#check contextual_decl_not_complete
#print axioms contextual_decl_not_complete
end Solidity.Frontend.StatementGrammarH28
