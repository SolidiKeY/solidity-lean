import Solidity.Frontend.StatementGrammarH28.RootHead

/-! All public H31 leading-token/root theorem signatures and axiom sets. -/
namespace Solidity.Frontend.StatementGrammarH28
set_option pp.universes true
#check safe_start_append
#print axioms safe_start_append
#check safe_start_fixed
#print axioms safe_start_fixed
#check safe_start_map
#print axioms safe_start_map
#check lift_post
#print axioms lift_post
#check chunks_cons_nonempty
#print axioms chunks_cons_nonempty
#check fragsP_safe_start
#print axioms fragsP_safe_start
#check litP_safe_start
#print axioms litP_safe_start
#check elem_safe_start
#print axioms elem_safe_start
#check path_safe_start
#print axioms path_safe_start
#check prefix_safe_start
#print axioms prefix_safe_start
#check syntax_head_invariant
#print axioms syntax_head_invariant
#check expression_yield_safe_start
#print axioms expression_yield_safe_start
#check type_yield_safe_start
#print axioms type_yield_safe_start
#check simple_yield_safe_start
#print axioms simple_yield_safe_start
#check simple_statement_yield_safe
#print axioms simple_statement_yield_safe
#check simple_root_yield_safe
#print axioms simple_root_yield_safe
#check root_hard_token
#print axioms root_hard_token
#check simple_hard_prefix_distinct
#print axioms simple_hard_prefix_distinct
#check statement_root_collision_cases
#print axioms statement_root_collision_cases
end Solidity.Frontend.StatementGrammarH28
