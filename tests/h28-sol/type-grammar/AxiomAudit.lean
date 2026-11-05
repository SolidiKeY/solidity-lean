import Solidity.Frontend.TypeGrammarH28.Boundaries
import Solidity.Frontend.TypeGrammarH28.Composition
import Solidity.Frontend.TypeGrammarH28.Counterexamples
import Solidity.Frontend.TypeGrammarH28.Exactness
import Solidity.Frontend.TypeGrammarH28.Layouts
import Solidity.Frontend.TypeGrammarH28.ParserArrays
import Solidity.Frontend.TypeGrammarH28.ParserBasics
import Solidity.Frontend.TypeGrammarH28.ParserChecks
import Solidity.Frontend.TypeGrammarH28.ParserContexts
import Solidity.Frontend.TypeGrammarH28.ParserDynamicClosure
import Solidity.Frontend.TypeGrammarH28.ParserFnAttrs
import Solidity.Frontend.TypeGrammarH28.ParserFunctions
import Solidity.Frontend.TypeGrammarH28.ParserLengths
import Solidity.Frontend.TypeGrammarH28.ParserMapping
import Solidity.Frontend.TypeGrammarH28.ParserParams
import Solidity.Frontend.TypeGrammarH28.ParserPaths
import Solidity.Frontend.TypeGrammarH28.ParserReady
import Solidity.Frontend.TypeGrammarH28.TypeRegions

namespace Solidity.Frontend.TypeGrammarH28.Boundary
#print axioms mark_open
#print axioms mark_close
#print axioms prefix_nil
#print axioms prefix_append
#print axioms prefix_cons
#print axioms cut_empty
#print axioms cut_nonempty
#print axioms cut_nonempty_plain
#print axioms cut_nonempty_open
#print axioms cut_close
#print axioms cut_empty_plain
#print axioms cut_empty_open
#print axioms balanced_cut
#print axioms region_cut
#print axioms cut_boundary
#print axioms region_cut_boundary
#print axioms boundary_unique
#print axioms region_balanced
#print axioms nest_balanced
#print axioms nest_region
#print axioms arbitrary_nested_boundary
#print axioms mismatched_close_refused
#print axioms unterminated_group_refused
#print axioms inner_comma_preserved
#print axioms balanced_append
#print axioms region_append
#print axioms prefix_head_inv
#print axioms cut_suffix
end Solidity.Frontend.TypeGrammarH28.Boundary

namespace Solidity.Frontend.TypeGrammarH28
#print axioms exact_elem
#print axioms exact_userType
#print axioms exact_params_nil
#print axioms exact_params_cons
#print axioms exact_no_length
#print axioms exact_some_length
#print axioms exact_array
#print axioms exact_param
#print axioms exact_mapping
#print axioms exact_fnType
#print axioms params_cons_decompose
#print axioms exact_toks
#print axioms exact_layout_equivalent
#print axioms exact_dynamic_depth
#print axioms exact_empty_function
#print axioms exact_nested_layout
end Solidity.Frontend.TypeGrammarH28

namespace Solidity.Frontend.TypeGrammarH28
#print axioms raw_yield_not_unique
#print axioms raw_counterexample_precedence
end Solidity.Frontend.TypeGrammarH28

namespace Solidity.Frontend.TypeGrammarH28.Exactness
#print axioms deps_sound
#print axioms type_prefix
#print axioms param_certified
#print axioms params_certified
#print axioms all_constructor_coverage
#print axioms finite_atom_dependencies
#print axioms type_certified
#print axioms finite_type_prefix
#print axioms finite_type_completeness
#print axioms frozen_type_complete
#print axioms checked_type_complete
#print axioms source_type_sound
#print axioms source_type_complete
#print axioms source_type_iff
#print axioms type_yield_unique
#print axioms finite_type_exactness
#print axioms finite_source_type_iff
#print axioms elem_params_deps
#print axioms param_precedence
#print axioms cons_precedence
#print axioms fn_precedence
#print axioms mixed_deps
#print axioms mixed_prec
#print axioms mixed_exact
#print axioms mixed_checked
#print axioms mixed_source_iff
#print axioms atom_length_balance
#print axioms deps_balanced
#print axioms type_atoms_balanced
#print axioms type_boundary_decomposition
#print axioms type_boundary_exactness
#print axioms finite_boundary_exactness
end Solidity.Frontend.TypeGrammarH28.Exactness

namespace Solidity.Frontend.TypeGrammarH28
#print axioms layoutEquivalent_symm
#print axioms layoutEquivalent_trans
#print axioms elem_yield
#print axioms userType_yield
#print axioms elem_toks
#print axioms userType_toks
#print axioms elem_no_unused_layout
#print axioms userType_no_unused_layout
end Solidity.Frontend.TypeGrammarH28

namespace Solidity.Frontend.TypeGrammarH28.ParserArray
#print axioms elem_name_token
#print axioms elem_name_payable
#print axioms elem_name_complete
#print axioms elem_dispatch
#print axioms elem_then_suffix
#print axioms brackets_no_payable
#print axioms brackets_path_stop
#print axioms dynamic_elem_complete
#print axioms user_then_suffix
#print axioms dynamic_user_complete
#print axioms dynamic_yield
#print axioms dynamic_toks
#print axioms dynamic_prec
#print axioms brackets_budget
#print axioms frozen_budget
#print axioms dynamic_frozen_budget
#print axioms dynamic_elem_complete_ge
#print axioms dynamic_user_complete_ge
#print axioms dynamic_elem_checked
#print axioms dynamic_user_checked
#print axioms parseType_dynamic_elem
#print axioms parseType_dynamic_user
#print axioms dynamic_elem_layout
#print axioms dynamic_user_layout
#print axioms dynamic_elem_checked_yield
#print axioms dynamic_user_checked_yield
#print axioms dynamic_elem_yield_unique
#print axioms dynamic_user_yield_unique
#print axioms dynamic_elem_user_yield_unique
#print axioms suffix_dynamic_insufficient
#print axioms dynamic_elem_insufficient
#print axioms dynamic_user_insufficient
end Solidity.Frontend.TypeGrammarH28.ParserArray

namespace Solidity.Frontend.TypeGrammarH28.ParserBasic
#print axioms located_nil
#print axioms located_cons
#print axioms located_one
#print axioms suffix_eof
#print axioms elem_token_eof
#print axioms payable_eof
#print axioms elem_single_projection
#print axioms payable_projection
#print axioms elem_yield_eof
#print axioms elem_complete_ge
#print axioms type_zero_refused
#print axioms suffix_zero_refused
#print axioms elementary_one_refused
#print axioms suffix_stop
#print axioms suffix_dynamic_step
#print axioms suffix_dynamic_complete
#print axioms located_append
#print axioms raw_payable_no_yield
end Solidity.Frontend.TypeGrammarH28.ParserBasic

namespace Solidity.Frontend.TypeGrammarH28.ParserCheck
#print axioms checked_category_converse
#print axioms elem_located_complete
#print axioms elem_parseCat_complete
#print axioms parseType_elem_complete
#print axioms artificial_payable_refused
#print axioms parseType_elem_iff
#print axioms witness_locations_tokens
#print axioms elem_tokens_injective
#print axioms elem_yield_unique
#print axioms checked_category_iff
end Solidity.Frontend.TypeGrammarH28.ParserCheck

namespace Solidity.Frontend.TypeGrammarH28.ParserContext
#print axioms boundary_no_payable
#print axioms boundary_no_suffix
#print axioms boundary_no_path
#print axioms boundary_no_attrs
#print axioms boundary_no_returns
#print axioms brackets_boundary_no_payable
#print axioms brackets_boundary_no_path
#print axioms dynamic_elem_prefix
#print axioms dynamic_user_prefix
#print axioms elem_prefix
#print axioms user_prefix
#print axioms complete_elem
#print axioms complete_user
#print axioms complete_dynamic_elem
#print axioms complete_dynamic_user
#print axioms boundary_excludes_array_continuation
#print axioms boundary_excludes_visibility_continuation
#print axioms boundary_excludes_mutability_continuation
#print axioms boundary_excludes_returns_continuation
end Solidity.Frontend.TypeGrammarH28.ParserContext

namespace Solidity.Frontend.TypeGrammarH28.ParserDynamicClosure
#print axioms dynamic_succ
#print axioms brackets_snoc
#print axioms array_none_yield
#print axioms array_none_toks
#print axioms array_none_toks_decompose
#print axioms dynamic_toks_from_base
#print axioms dynamic_toks_decompose
#print axioms array_none_prec_converse
#print axioms dynamic_prec_converse
#print axioms dynamic_mapping_prefix
#print axioms complete_dynamic_mapping
#print axioms dynamic_mapping_budget
#print axioms certified_dynamic_mapping
#print axioms grammar_certified
#print axioms grammar_prec
#print axioms grammar_yield_inhabited
#print axioms grammar_checked_inhabited
#print axioms grammar_yield_unique
#print axioms grammar_parseType_iff
#print axioms grammar_no_unused_layout
end Solidity.Frontend.TypeGrammarH28.ParserDynamicClosure

namespace Solidity.Frontend.TypeGrammarH28.ParserFnAttrs
#print axioms singles_empty
#print axioms singles_vis
#print axioms singles_mut
#print axioms singles_both
#print axioms arrange_empty_converse
#print axioms map_append_converse
#print axioms arrange_vis_converse
#print axioms arrange_mut_converse
#print axioms arrange_both_converse
#print axioms arrange_layout
#print axioms layout_arrange
#print axioms arrange_layout_iff
#print axioms attrs_stop
#print axioms vis_step
#print axioms mut_step
#print axioms attrs_complete
#print axioms arranged_attrs_complete
#print axioms repeated_vis_stops
#print axioms repeated_mut_refused
#print axioms layout_length
#print axioms overlong_order_refused
#print axioms arranged_fields_unique
#print axioms attrs_inhabited
#print axioms mut_first_inhabited
end Solidity.Frontend.TypeGrammarH28.ParserFnAttrs

namespace Solidity.Frontend.TypeGrammarH28.ParserFunction
#print axioms paren_prefix
#print axioms returns_nil
#print axioms returns_cons
#print axioms empty_returns_refused
#print axioms returns_from_list
#print axioms returns_attr_boundary
#print axioms capture_paren_prefix
#print axioms fn_body_complete
#print axioms fn_body_complete_ge
#print axioms ready_fn
#print axioms parens_length
#print axioms fn_params_length
#print axioms fn_returns_length
#print axioms fuel_slack
#print axioms fn_budget
#print axioms params_prec_node
#print axioms fn_prec_converse
#print axioms fn_yield_attrs
#print axioms fn_yield_decompose
#print axioms prefix_fn
#print axioms certified_fn
#print axioms fn_parseType_iff
#print axioms fn_elem_prefix
#print axioms fn_elem_prec
#print axioms fn_elem_tokens
#print axioms fn_elem_checked_inhabited
#print axioms nested_fn_prefix
#print axioms nested_fn_prec
#print axioms nested_fn_exact
#print axioms nested_fn_elem_checked
#print axioms fn_arrays_prefix
#print axioms function_two_refused
end Solidity.Frontend.TypeGrammarH28.ParserFunction

namespace Solidity.Frontend.TypeGrammarH28.ParserLength
#print axioms balanced_front_no_close
#print axioms expr_ident_before_close
#print axioms expr_num_before_close
#print axioms ident_expr_at
#print axioms num_expr_at
#print axioms ident_length_atom
#print axioms num_length_atom
#print axioms expr_zero_not_complete
#print axioms suffix_static_step
#print axioms ready_array_some
#print axioms array_some_yield
#print axioms all_node
#print axioms array_some_prec_converse
#print axioms static_tokens_length
#print axioms static_budget
#print axioms array_some_yield_decompose
#print axioms prefix_array_some
#print axioms certified_array_some
#print axioms array_some_parseType_iff
#print axioms array_some_prec
#print axioms static_tower_prefix
#print axioms static_tower_prec
#print axioms static_tower_exact
#print axioms static_num_checked
#print axioms static_ident_checked
#print axioms ident_expr_four_refused
end Solidity.Frontend.TypeGrammarH28.ParserLength

namespace Solidity.Frontend.TypeGrammarH28.ParserMapping
#print axioms opt_ident_complete
#print axioms name_boundary
#print axioms tail_complete
#print axioms mapping_elem_tail
#print axioms mapping_path_tail
#print axioms mapping_tokens_cons
#print axioms key_elem_spelling
#print axioms mapping_body_complete
#print axioms mapping_dispatch
#print axioms mapping_prefix
#print axioms complete_mapping
#print axioms toks_yield_decompose
#print axioms mapping_toks
#print axioms mapping_prec
#print axioms middle_length
#print axioms mapping_length
#print axioms budget_lift
#print axioms mapping_budget
#print axioms mapping_checked
#print axioms parseType_mapping
#print axioms type_prec_node
#print axioms mapping_prec_converse
#print axioms mapping_yield
#print axioms mapping_toks_decompose
#print axioms certified_elem
#print axioms certified_user
#print axioms certified_mapping
#print axioms dynamic_tokens_budget
#print axioms certified_dynamic_elem
#print axioms certified_dynamic_user
#print axioms certified_checked
#print axioms certified_parseType
#print axioms certified_yield_unique
#print axioms certified_nested_mappings
#print axioms nested_mappings_prec
#print axioms nested_dynamic_elem_unique
#print axioms nested_dynamic_user_unique
#print axioms nested_mappings_toks
#print axioms nested_dynamic_elem_inhabited
#print axioms nested_dynamic_user_inhabited
#print axioms artificial_payable_key_refused
#print axioms payable_key_spelling_refused
#print axioms certified_parseType_iff
#print axioms parseType_mapping_iff
end Solidity.Frontend.TypeGrammarH28.ParserMapping

namespace Solidity.Frontend.TypeGrammarH28.ParserParams
#print axioms list_boundary_type
#print axioms list_boundary_no_ident
#print axioms param_tail_complete
#print axioms trailer_type_boundary
#print axioms param_prefix
#print axioms param_complete
#print axioms param_yield
#print axioms param_prec_converse
#print axioms param_length
#print axioms param_certified
#print axioms list_end_boundary
#print axioms list_end_no_comma
#print axioms commaSep_head
#print axioms param_list_inverse
#print axioms param_values_to_syn
#print axioms list_ready_to_syn
#print axioms list_ready_positive
#print axioms list_ready_exact
#print axioms tail_tokens_boundary
#print axioms sep_aux_step
#print axioms sep_aux_complete
#print axioms sep_aux_complete_ge
#print axioms tail_tokens_count
#print axioms sep_one_complete
#print axioms comma_sep_tail_length
#print axioms list_ready_budget
#print axioms params_nil_certified
#print axioms params_cons_prec
#print axioms params_cons_certified
#print axioms param_rparen_no_success
#print axioms param_success_no_close
#print axioms params_paren_complete
#print axioms elem_params_certified
#print axioms elem_params_exact
#print axioms elem_params_prec
#print axioms elem_params_ready
#print axioms elem_params_parse
#print axioms missing_close_refused
#print axioms duplicate_comma_refused
end Solidity.Frontend.TypeGrammarH28.ParserParams

namespace Solidity.Frontend.TypeGrammarH28.ParserPath
#print axioms path_step_empty
#print axioms path_step_pair
#print axioms many_stop
#print axioms many_step
#print axioms path_tail_complete
#print axioms path_tail_budget
#print axioms path_tail_complete_ge
#print axioms path_complete
#print axioms path_eof
#print axioms user_type_complete
#print axioms user_yield_eof
#print axioms user_complete_ge
#print axioms user_located_complete
#print axioms user_parseCat_complete
#print axioms parseType_user_complete
#print axioms parseType_user_iff
#print axioms user_tokens_injective
#print axioms user_yield_unique
#print axioms path_step_lone_period
#print axioms path_step_period_elem
#print axioms user_trailing_period_refused
end Solidity.Frontend.TypeGrammarH28.ParserPath

namespace Solidity.Frontend.TypeGrammarH28.ParserReady
#print axioms continuation_no_payable
#print axioms continuation_no_path
#print axioms continuation_no_attrs
#print axioms continuation_no_returns
#print axioms ready_completeAt
#print axioms ready_elem
#print axioms ready_user
#print axioms prefix_to_certified
#print axioms prefix_elem
#print axioms prefix_user
#print axioms ready_mapping
#print axioms prefix_mapping
#print axioms ready_array_none
#print axioms prefix_array_none
#print axioms prefix_dynamic
#print axioms grammar_prefix
#print axioms ready_elem_zero
#print axioms not_complete_elem_one
#print axioms unconsumed_layout_control
end Solidity.Frontend.TypeGrammarH28.ParserReady

namespace Solidity.Frontend.TypeGrammarH28.TypeRegion
#print axioms elem_region
#print axioms path_tail_region
#print axioms path_region
#print axioms name_region
#print axioms loc_region
#print axioms vis_region
#print axioms mut_region
#print axioms key_region
#print axioms parens_region
#print axioms brackets_region
#print axioms commaSep_balanced
#print axioms param_region
#print axioms array_region
#print axioms mapping_region
#print axioms arrange_cons_nil
#print axioms arrange_region
#print axioms single_region
#print axioms fn_attrs_region
#print axioms function_region
#print axioms atoms_elem_iff
#print axioms atoms_userType_iff
#print axioms atoms_array_iff
#print axioms atoms_mapping_iff
#print axioms atoms_fnType_iff
#print axioms atoms_param_iff
#print axioms atoms_params_nil_iff
#print axioms atoms_params_cons_iff
#print axioms no_length_balance
#print axioms some_length_balance
#print axioms numeric_length_balance
#print axioms yield_elem_region
#print axioms yield_userType_region
#print axioms yield_mapping_region
#print axioms yield_array_region
#print axioms yield_fnType_region
#print axioms yield_param_region
#print axioms yield_params_nil
#print axioms yield_params_cons
#print axioms type_yield_region
#print axioms param_yield_region
#print axioms params_yield_regions
#print axioms region_all_closes
#print axioms type_toks_region
#print axioms type_toks_boundary
#print axioms type_token_boundary_unique
#print axioms dynamic_atoms_balanced
#print axioms dynamic_type_boundary
#print axioms nested_atoms_balanced
#print axioms every_close_boundary
#print axioms commaSep_split
#print axioms afterFirst_boundary
#print axioms params_first_boundary
#print axioms nested_type_boundary
#print axioms malformed_layouts_refused
end Solidity.Frontend.TypeGrammarH28.TypeRegion
